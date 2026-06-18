# Inventory: ./HasseWeil/GapQfKernel.lean

**File purpose**: Sorry-skeleton (with several axiom-clean results) for `omegaPullbackCoeff (mulByInt m) = m` via the formal group (Silverman IV), and a char-p Kähler-kernel development (ker D = K(E)ᵖ in char p, finrank = p). Also collects mem_F propagation closures and isConstant wrappers for specific isogenies.

**Imports**: `HasseWeil.FormalIsogenySeries`, `HasseWeil.Ramification`, `HasseWeil.RouteBInduction`, `HasseWeil.Curves.Infinity`

---

## Declarations

### `theorem formalIsogenySeries_FGL_additivity`
- **Type**: `∀ k : ℕ, 1 ≤ k → formalIsogenySeries W (mulByInt W.toAffine ((k : ℤ) + 1)) = MvPowerSeries.subst (![formalIsogenySeries W (mulByInt W.toAffine (k : ℤ)), formalIsogenySeries W (mulByInt W.toAffine 1)]) (formalGroupLaw W).toMvPowerSeries`
- **What**: States that the formal isogeny series of `[k+1]` equals the formal group law applied to the series of `[k]` and `[1]` — i.e., `[k+1]_F = F([k]_F, [1]_F)` (Silverman IV.2.3a substance).
- **How**: Body is `sorry`.
- **Hypotheses**: Elliptic curve `W` over a field `F`.
- **Uses from project**: `formalIsogenySeries`, `mulByInt`, `formalGroupLaw`
- **Used by**: `coeff_one_formalIsogenySeries_mulByInt_eq` (via `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003`)
- **Visibility**: public
- **Lines**: 41–49, proof length 1 line
- **Notes**: sorry (bare sub-ticket leaf, BRIDGE-003)

---

### `theorem coeff_one_formalIsogenySeries_mulByInt_nonpos`
- **Type**: `(m : ℤ) → m ≤ 0 → PowerSeries.coeff 1 (formalIsogenySeries W (mulByInt W.toAffine m)) = (m : F)`
- **What**: The linear coefficient of the formal isogeny series of `[m]` equals `m` for `m ≤ 0` (includes `[0]` and negative multiplication maps).
- **How**: Body is `sorry`.
- **Hypotheses**: `m ≤ 0`.
- **Uses from project**: `formalIsogenySeries`, `mulByInt`
- **Used by**: `coeff_one_formalIsogenySeries_mulByInt_eq`
- **Visibility**: public
- **Lines**: 54–56, proof length 1 line
- **Notes**: sorry (sub-leaf for m ≤ 0 case, L-F1)

---

### `theorem coeff_one_formalIsogenySeries_mulByInt_eq`
- **Type**: `(m : ℤ) → PowerSeries.coeff 1 (formalIsogenySeries W (mulByInt W.toAffine m)) = (m : F)`
- **What**: The linear coefficient of the formal isogeny series of `[m]` equals `m` for all integers `m` (Silverman IV.2.3a, L-F1).
- **How**: Splits on `m ≤ 0` (handled by `coeff_one_formalIsogenySeries_mulByInt_nonpos`) and `m > 0` (handled by the shipped induction closer `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003` with `formalIsogenySeries_FGL_additivity`).
- **Hypotheses**: None beyond elliptic curve.
- **Uses from project**: `coeff_one_formalIsogenySeries_mulByInt_nonpos`, `formalIsogenySeries_FGL_additivity`, `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003` (from FormalIsogenySeries)
- **Used by**: `omegaPullbackCoeff_mulByInt_via_formalGroup`
- **Visibility**: public
- **Lines**: 58–66, proof length 8 lines

---

### `theorem laurentSeries_derivative_mul`
- **Type**: `{R : Type*} → [CommRing R] → (f g : LaurentSeries R) → LaurentSeries.derivative R (f * g) = f * LaurentSeries.derivative R g + g * LaurentSeries.derivative R f`
- **What**: Product rule (Leibniz rule) for the formal derivative `hasseDeriv 1` on `LaurentSeries R`, proved by an antidiagonal reindexing argument at the coefficient level.
- **How**: Rewrites using `LaurentSeries.hasseDeriv_coeff` and `Ring.choose_one_right`, then performs two symmetric reindexing arguments on `Finset.addAntidiagonal` (shifting by ±1 in one coordinate), summing to `ij.1 + ij.2 = m+1 = (m+1) • 1`.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: none (uses only mathlib)
- **Used by**: `localExpand_derivative_leibniz`, `localExpandDeriv`
- **Visibility**: public
- **Lines**: 70–179, proof length ~109 lines
- **Notes**: proof > 30 lines; likely a mathlib gap (Leibniz for `LaurentSeries.derivative` not in mathlib as of this file's date)

---

### `theorem localExpand_derivative_leibniz`
- **Type**: `(f g : KE) → LaurentSeries.derivative F (localExpand W (f * g)) = localExpand W f * LaurentSeries.derivative F (localExpand W g) + localExpand W g * LaurentSeries.derivative F (localExpand W f)`
- **What**: The composition `f ↦ (d/dt)(localExpand f)` satisfies the Leibniz rule — it is a derivation on K(E) valued in LaurentSeries F (Silverman IV.1).
- **How**: Uses `map_mul` (ring hom) + `laurentSeries_derivative_mul`.
- **Hypotheses**: None beyond elliptic curve.
- **Uses from project**: `localExpand`, `laurentSeries_derivative_mul`
- **Used by**: `localExpandDeriv`
- **Visibility**: public
- **Lines**: 183–188, proof length 5 lines

---

### `theorem localExpand_injective`
- **Type**: `Function.Injective (localExpand W)`
- **What**: The local expansion ring hom `localExpand : K(E) →+* LaurentSeries F` is injective.
- **How**: Directly from `(localExpand W).injective` (ring hom injectivity).
- **Hypotheses**: None beyond elliptic curve.
- **Uses from project**: `localExpand`
- **Used by**: `omegaPullbackCoeff_eq_formalIsogenyLeading_via_localization`
- **Visibility**: public
- **Lines**: 192–193, proof length 1 line (term-mode)

---

### `theorem derivative_localExpand_algebraMap`
- **Type**: `(r : F) → LaurentSeries.derivative F (localExpand W (algebraMap F KE r)) = 0`
- **What**: The formal t-derivative of the local expansion of any constant `r ∈ F` is zero (constants have zero derivative).
- **How**: Uses `localExpand_algebraMap`, `HahnSeries.ofPowerSeries_C`, rewrites to `HahnSeries.single 0 r`, and applies `LaurentSeries.hasseDeriv_single`.
- **Hypotheses**: None beyond elliptic curve.
- **Uses from project**: `localExpand`, `localExpand_algebraMap`
- **Used by**: `localExpandDeriv`
- **Visibility**: public
- **Lines**: 198–203, proof length 5 lines

---

### `structure LExp`
- **Type**: Structure with one field `out : LaurentSeries F`, parametrized by `W`.
- **What**: A wrapper type for `LaurentSeries F` that carries the `K(E)`-module structure via `localExpand` (needed to resolve the `SMul F (LaurentSeries F)` instance diamond for `liftKaehlerDifferential`).
- **How**: Structure definition with a single field.
- **Hypotheses**: Elliptic curve `W`.
- **Uses from project**: `localExpand`
- **Used by**: All `LExp` namespace members, `localExpandDeriv`, `localExpandKaehlerLift`
- **Visibility**: public
- **Lines**: 220–227

---

### `theorem LExp.ext`
- **Type**: `{x y : LExp W} → x.out = y.out → x = y`
- **What**: Extensionality for `LExp`: two wrappers are equal iff their underlying Laurent series agree.
- **How**: `cases x; cases y; congr`.
- **Hypotheses**: None.
- **Uses from project**: `LExp`
- **Used by**: `localExpandDeriv` (in `map_smul'`, `map_one_eq_zero'`, `leibniz'`)
- **Visibility**: public
- **Lines**: 228, proof length 1 line

---

### `noncomputable instance : Zero (LExp W)`
- **Type**: `Zero (LExp W)`
- **What**: Zero element for the wrapper type.
- **Hypotheses**: None.
- **Uses from project**: `LExp`
- **Used by**: Other `LExp` instances
- **Visibility**: public
- **Lines**: 230

---

### `noncomputable instance : Add (LExp W)`
- **Type**: `Add (LExp W)`
- **What**: Addition for the wrapper type, pointwise on `out`.
- **Hypotheses**: None.
- **Uses from project**: `LExp`
- **Used by**: Other `LExp` instances
- **Visibility**: public
- **Lines**: 231

---

### `noncomputable instance : Neg (LExp W)`
- **Type**: `Neg (LExp W)`
- **What**: Negation for the wrapper type.
- **Hypotheses**: None.
- **Uses from project**: `LExp`
- **Used by**: Other `LExp` instances
- **Visibility**: public
- **Lines**: 232

---

### `noncomputable instance : Sub (LExp W)`
- **Type**: `Sub (LExp W)`
- **What**: Subtraction for the wrapper type.
- **Hypotheses**: None.
- **Uses from project**: `LExp`
- **Used by**: Other `LExp` instances
- **Visibility**: public
- **Lines**: 233

---

### `theorem out_zero`, `out_add`, `out_neg`, `out_sub`
- **Type**: `@[simp]` lemmas relating `LExp` arithmetic to underlying `out`.
- **What**: Simp lemmas unfolding `LExp` arithmetic to operations on the underlying Laurent series.
- **Hypotheses**: None.
- **Uses from project**: `LExp`
- **Used by**: `instAddCommGroup`, `instModuleKE`, `instModuleF`, `IsScalarTower` instance
- **Visibility**: public
- **Lines**: 234–237

---

### `noncomputable instance : AddCommGroup (LExp W)`
- **Type**: `AddCommGroup (LExp W)`
- **What**: Makes `LExp W` an abelian group, proved by reducing to `LaurentSeries F`.
- **Hypotheses**: None.
- **Uses from project**: `LExp`, `LExp.ext`, `out_add`, etc.
- **Used by**: `instModuleKE`, `instModuleF`
- **Visibility**: public
- **Lines**: 239–247

---

### `noncomputable instance instSMulKE`
- **Type**: `SMul KE (LExp W)`
- **What**: `K(E)` acts on `LExp W` by `c • x = localExpand(c) * x.out`.
- **Hypotheses**: None.
- **Uses from project**: `localExpand`, `LExp`
- **Used by**: `instModuleKE`, `IsScalarTower`
- **Visibility**: public
- **Lines**: 250–252

---

### `theorem out_smul_KE`
- **Type**: `@[simp]` lemma: `(c • x : LExp W).out = localExpand W c * x.out`
- **What**: Simp lemma for the K(E)-scalar action on `LExp`.
- **Hypotheses**: None.
- **Uses from project**: `instSMulKE`
- **Used by**: `instModuleKE`, `IsScalarTower`, `localExpandKaehlerLift_smul`
- **Visibility**: public
- **Lines**: 252

---

### `noncomputable instance instModuleKE`
- **Type**: `Module KE (LExp W)`
- **What**: Makes `LExp W` a `K(E)`-module via `localExpand`-multiplication.
- **Hypotheses**: None.
- **Uses from project**: `LExp`, `instSMulKE`, `out_smul_KE`, `localExpand`
- **Used by**: `localExpandDeriv`, `localExpandKaehlerLift`
- **Visibility**: public
- **Lines**: 254–261

---

### `noncomputable instance instSMulF`
- **Type**: `SMul F (LExp W)`
- **What**: `F` acts on `LExp W` by restriction through `algebraMap F KE`, making the scalar tower hold by construction.
- **Hypotheses**: None.
- **Uses from project**: `instSMulKE`
- **Used by**: `instModuleF`, `IsScalarTower`
- **Visibility**: public
- **Lines**: 264–265

---

### `theorem out_smul_F`
- **Type**: `@[simp]` lemma: `(r • x : LExp W).out = localExpand W (algebraMap F KE r) * x.out`
- **What**: Simp lemma for the F-scalar action on `LExp` (via the algebra map).
- **Hypotheses**: None.
- **Uses from project**: `instSMulF`, `localExpand`
- **Used by**: `instModuleF`, `IsScalarTower`, `localExpandDeriv`
- **Visibility**: public
- **Lines**: 266–267

---

### `noncomputable instance instModuleF`
- **Type**: `Module F (LExp W)`
- **What**: Makes `LExp W` an `F`-module by restriction of scalars through `algebraMap F KE`.
- **Hypotheses**: None.
- **Uses from project**: `instSMulF`, `out_smul_F`, `localExpand`
- **Used by**: `localExpandDeriv`, `localExpandKaehlerLift`
- **Visibility**: public
- **Lines**: 269–275

---

### `instance : IsScalarTower F KE (LExp W)`
- **Type**: `IsScalarTower F KE (LExp W)`
- **What**: The scalar tower `F → K(E) → LExp W` holds: `(r • c) • x = r • (c • x)`.
- **How**: Reduces via `Algebra.smul_def` and `map_mul` to commutativity of `localExpand` with the algebra map.
- **Hypotheses**: None.
- **Uses from project**: `instSMulKE`, `instSMulF`, `localExpand`, `out_smul_KE`, `out_smul_F`
- **Used by**: `localExpandDeriv`, `localExpandKaehlerLift`
- **Visibility**: public
- **Lines**: 277–282, proof length 5 lines

---

### `noncomputable def localExpandDeriv`
- **Type**: `Derivation F KE (LExp W)`
- **What**: The derivation `g ↦ (d/dt)(localExpand g)` from `K(E)` to `LExp W`, establishing that formal differentiation after local expansion is an `F`-derivation.
- **How**: Provides all four fields (`map_add'`, `map_smul'`, `map_one_eq_zero'`, `leibniz'`) using `laurentSeries_derivative_mul`, `derivative_localExpand_algebraMap`, and `localExpand_derivative_leibniz`.
- **Hypotheses**: None beyond elliptic curve.
- **Uses from project**: `LExp`, `localExpand`, `laurentSeries_derivative_mul`, `derivative_localExpand_algebraMap`, `localExpand_derivative_leibniz`, `LExp.ext`, `out_smul_F`, `out_add`, `out_smul_KE`
- **Used by**: `localExpandKaehlerLift`
- **Visibility**: public
- **Lines**: 288–312, proof length ~24 lines

---

### `noncomputable def localExpandKaehlerLift`
- **Type**: `Ω[KE⁄F] →ₗ[KE] LExp W`
- **What**: The `K(E)`-linear map from Kähler differentials `Ω[K(E)/F]` to `LExp W`, obtained by lifting `localExpandDeriv` through the universal property of Kähler differentials.
- **How**: Direct application of `Derivation.liftKaehlerDifferential`.
- **Hypotheses**: None beyond elliptic curve.
- **Uses from project**: `localExpandDeriv`, `LExp`
- **Used by**: `localExpandKaehlerLift_D`, `localExpandKaehlerLift_smul`, `omegaPullbackCoeff_F_value_eq_coeff_one`
- **Visibility**: public
- **Lines**: 315–316, proof length 1 line (term-mode)

---

### `theorem localExpandKaehlerLift_D`
- **Type**: `(g : KE) → (localExpandKaehlerLift W (KaehlerDifferential.D F KE g)).out = LaurentSeries.derivative F (localExpand W g)`
- **What**: The Kähler lift sends `D g` to the formal t-derivative of `localExpand g`.
- **How**: Unfolds `localExpandKaehlerLift` and applies `Derivation.liftKaehlerDifferential_comp_D`.
- **Hypotheses**: None.
- **Uses from project**: `localExpandKaehlerLift`, `localExpand`
- **Used by**: `omegaPullbackCoeff_F_value_eq_coeff_one`
- **Visibility**: public
- **Lines**: 319–323, proof length 4 lines

---

### `theorem localExpandKaehlerLift_smul`
- **Type**: `(c : KE) → (ω : Ω[KE⁄F]) → (localExpandKaehlerLift W (c • ω)).out = localExpand W c * (localExpandKaehlerLift W ω).out`
- **What**: The Kähler lift is `K(E)`-semilinear: a `K(E)` scalar `c` becomes `localExpand c`.
- **How**: Simp using `map_smul` and `out_smul_KE`.
- **Hypotheses**: None.
- **Uses from project**: `localExpandKaehlerLift`, `localExpand`, `out_smul_KE`
- **Used by**: `omegaPullbackCoeff_F_value_eq_coeff_one`
- **Visibility**: public
- **Lines**: 326–329, proof length 3 lines

---

### `theorem omegaPullbackCoeff_isIntegral_polynomialX`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) → IsIntegral (Polynomial F) (omegaPullbackCoeff W α)`
- **What**: `a_α` (the scaling factor of `α*ω`) is integral over `F[X]` — it has no finite poles (Silverman III.1.5 substrate, sub-leaf A1).
- **How**: Body is `sorry`.
- **Hypotheses**: Any self-isogeny `α`.
- **Uses from project**: `omegaPullbackCoeff`
- **Used by**: `omegaPullbackCoeff_mem_F`
- **Visibility**: public
- **Lines**: 357–360, proof length 1 line
- **Notes**: sorry (bare sub-ticket leaf, needs divisor-of-ω infrastructure)

---

### `theorem omegaPullbackCoeff_ordAtInfty_nonneg`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) → (0 : WithTop ℤ) ≤ (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).ordAtInfty (omegaPullbackCoeff W α)`
- **What**: `a_α` has nonneg order at infinity — no pole at `∞` (Silverman III.1.5 substrate, sub-leaf A2).
- **How**: Body is `sorry`.
- **Hypotheses**: Any self-isogeny `α`.
- **Uses from project**: `omegaPullbackCoeff`
- **Used by**: `omegaPullbackCoeff_mem_F`
- **Visibility**: public
- **Lines**: 367–372, proof length 1 line
- **Notes**: sorry (bare sub-ticket leaf, needs ord-at-infty of Kähler differential)

---

### `theorem omegaPullbackCoeff_mem_F`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) → ∃ c : F, omegaPullbackCoeff W α = algebraMap F KE c`
- **What**: `a_α` is a constant in the base field `F` (Silverman III.1.5: invariant differential has no zeros/poles, so `α*ω = a_α·ω` forces `a_α ∈ F`).
- **How**: Combines the two sorry sub-leaves (`omegaPullbackCoeff_isIntegral_polynomialX` + `omegaPullbackCoeff_ordAtInfty_nonneg`) via the shipped algebraic-Liouville theorem `HasseWeil.Curves.SmoothPlaneCurve.const_of_isIntegral_polynomialX_of_ordAtInfty`.
- **Hypotheses**: Any self-isogeny `α`.
- **Uses from project**: `omegaPullbackCoeff_isIntegral_polynomialX`, `omegaPullbackCoeff_ordAtInfty_nonneg`, `HasseWeil.Curves.SmoothPlaneCurve.const_of_isIntegral_polynomialX_of_ordAtInfty`
- **Used by**: `omegaPullbackCoeff_localExpand_eq_coeff_one`
- **Visibility**: public
- **Lines**: 384–392, proof length 8 lines
- **Notes**: inherits sorry via sub-leaves

---

### `theorem omegaPullbackCoeff_isIntegral_polynomialX_frobenius`
- **Type**: `[Fintype F] → IsIntegral (Polynomial F) (omegaPullbackCoeff W (frobeniusIsog W))`
- **What**: `a_π = 0` is integral over `F[X]` (trivially, since `0` is integral). Frobenius-specific axiom-clean pass leaf.
- **How**: `rw [omegaPullbackCoeff_frobenius]; exact isIntegral_zero`.
- **Hypotheses**: `[Fintype F]`.
- **Uses from project**: `omegaPullbackCoeff_frobenius`, `frobeniusIsog`
- **Used by**: `omegaPullbackCoeff_mem_F_frobenius`
- **Visibility**: public
- **Lines**: 412–416, proof length 3 lines

---

### `theorem omegaPullbackCoeff_ordAtInfty_nonneg_frobenius`
- **Type**: `[Fintype F] → (0 : WithTop ℤ) ≤ (...).ordAtInfty (omegaPullbackCoeff W (frobeniusIsog W))`
- **What**: `a_π = 0` has nonneg ord at infinity (trivially `ord_∞ 0 = ⊤ ≥ 0`).
- **How**: Rewrites via `omegaPullbackCoeff_frobenius` and `ordAtInfty_zero`, then `le_top`.
- **Hypotheses**: `[Fintype F]`.
- **Uses from project**: `omegaPullbackCoeff_frobenius`, `HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_zero`
- **Used by**: `omegaPullbackCoeff_mem_F_frobenius`
- **Visibility**: public
- **Lines**: 420–427, proof length 6 lines

---

### `theorem omegaPullbackCoeff_mem_F_frobenius`
- **Type**: `[Fintype F] → ∃ c : F, omegaPullbackCoeff W (frobeniusIsog W) = algebraMap F KE c`
- **What**: `a_π` is a constant in `F` (specifically `0`). Axiom-clean per-Frobenius discharge.
- **How**: Applies `HasseWeil.Curves.SmoothPlaneCurve.const_of_isIntegral_polynomialX_of_ordAtInfty` to the two pass leaves.
- **Hypotheses**: `[Fintype F]`.
- **Uses from project**: `omegaPullbackCoeff_isIntegral_polynomialX_frobenius`, `omegaPullbackCoeff_ordAtInfty_nonneg_frobenius`, `HasseWeil.Curves.SmoothPlaneCurve.const_of_isIntegral_polynomialX_of_ordAtInfty`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 432–438, proof length 6 lines

---

### `theorem omegaPullbackCoeff_mem_F_comp_of_witnesses`
- **Type**: `(α β : Isogeny ...) → (c_α c_β : F) → omegaPullbackCoeff W α = algebraMap F KE c_α → omegaPullbackCoeff W β = algebraMap F KE c_β → ∃ c : F, omegaPullbackCoeff W (α.comp β) = algebraMap F KE c`
- **What**: Given explicit scalar witnesses for `a_α` and `a_β`, derives mem_F for `α∘β` with constant `c_α · c_β` (chain rule).
- **How**: Uses `omegaPullbackCoeff_comp_of_base W α β c_α hα`.
- **Hypotheses**: Explicit `c_α, c_β : F` and equality witnesses.
- **Uses from project**: `omegaPullbackCoeff_comp_of_base`
- **Used by**: `omegaPullbackCoeff_mem_F_comp_of_mem_F`
- **Visibility**: public
- **Lines**: 448–456, proof length 7 lines

---

### `theorem omegaPullbackCoeff_mem_F_comp_of_mem_F`
- **Type**: `(α β : Isogeny ...) → (∃ c, omegaPullbackCoeff W α = algebraMap F KE c) → (∃ c, omegaPullbackCoeff W β = algebraMap F KE c) → ∃ c, omegaPullbackCoeff W (α.comp β) = algebraMap F KE c`
- **What**: Existential form of composition closure for mem_F.
- **How**: Destructs existential witnesses and applies `omegaPullbackCoeff_mem_F_comp_of_witnesses`.
- **Hypotheses**: Existential mem_F for `α` and `β`.
- **Uses from project**: `omegaPullbackCoeff_mem_F_comp_of_witnesses`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 461–468, proof length 7 lines

---

### `theorem omegaPullbackCoeff_mem_F_of_add_witness`
- **Type**: `(α β γ : Isogeny ...) → (hα : ∃ c, ...) → (hβ : ∃ c, ...) → omegaPullbackCoeff W γ = omegaPullbackCoeff W α + omegaPullbackCoeff W β → ∃ c, omegaPullbackCoeff W γ = algebraMap F KE c`
- **What**: mem_F propagates through additivity: given mem_F for `α, β` and `a_γ = a_α + a_β`, derives mem_F for `γ` with constant `c_α + c_β`.
- **How**: Destructs witnesses, provides `⟨c_α + c_β, ...⟩` and rewrites via `map_add`.
- **Hypotheses**: Existential mem_F for `α` and `β`, plus additivity hypothesis `h_add`.
- **Uses from project**: none directly (uses mathlib `map_add`)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 474–484, proof length 9 lines

---

### `theorem omegaPullbackCoeff_mem_F_addIsog_id_of_witness`
- **Type**: `[Fintype F] → (α : Isogeny ...) → (hxy : AddNonInversePair (Isogeny.id W.toAffine) α) → (hinj : ...) → (h_ne : x_gen W ≠ α.pullback (x_gen W)) → (c_α : F) → omegaPullbackCoeff W α = algebraMap F KE c_α → ∃ c, omegaPullbackCoeff W (addIsog hxy hinj) = algebraMap F KE c`
- **What**: Given mem_F for `α` (with explicit constant `c_α`) and the witnesses for the chord step, derives mem_F for the sum isogeny `id ⊞ α` with constant `1 + c_α`.
- **How**: Uses `omegaPullbackCoeff_addIsog_id W α hxy hinj h_ne` and `map_add`, `map_one`.
- **Hypotheses**: `[Fintype F]`, `AddNonInversePair`, injectivity, x-mismatch, explicit `c_α`.
- **Uses from project**: `omegaPullbackCoeff_addIsog_id`, `addIsog`, `AddNonInversePair`, `addCoordAlgHomPair`, `x_gen`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 497–508, proof length 10 lines

---

### `theorem omegaPullbackCoeff_mem_F_comp_of_omega_zero_leading`
- **Type**: `(α β : Isogeny ...) → omegaPullbackCoeff W α = 0 → ∃ c : F, omegaPullbackCoeff W (α.comp β) = algebraMap F KE c`
- **What**: If `a_α = 0` (purely inseparable `α`), then `a_{α∘β} = 0` for any `β`, so `α∘β` has mem_F trivially.
- **How**: Reinterprets `hα : a_α = 0` as `a_α = algebraMap F KE 0`, then applies `omegaPullbackCoeff_comp_of_base`.
- **Hypotheses**: `omegaPullbackCoeff W α = 0`.
- **Uses from project**: `omegaPullbackCoeff_comp_of_base`
- **Used by**: `omegaPullbackCoeff_mem_F_frobeniusIsog_comp`, `omegaPullbackCoeff_mem_F_negFrobeniusIsog_comp`
- **Visibility**: public
- **Lines**: 523–530, proof length 7 lines

---

### `theorem omegaPullbackCoeff_mem_F_frobeniusIsog_comp`
- **Type**: `[Fintype F] → (β : Isogeny ...) → ∃ c, omegaPullbackCoeff W ((frobeniusIsog W).comp β) = algebraMap F KE c`
- **What**: Universal mem_F for compositions with the Frobenius isogeny as the leading factor.
- **How**: Direct application of `omegaPullbackCoeff_mem_F_comp_of_omega_zero_leading` with `omegaPullbackCoeff_frobenius`.
- **Hypotheses**: `[Fintype F]`.
- **Uses from project**: `omegaPullbackCoeff_mem_F_comp_of_omega_zero_leading`, `frobeniusIsog`, `omegaPullbackCoeff_frobenius`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 535–541, proof length 3 lines (term-mode)

---

### `theorem omegaPullbackCoeff_mem_F_negFrobeniusIsog_comp`
- **Type**: `[Fintype F] → (β : Isogeny ...) → ∃ c, omegaPullbackCoeff W ((negFrobeniusIsog W).comp β) = algebraMap F KE c`
- **What**: Universal mem_F for compositions with `negFrobeniusIsog` as the leading factor.
- **How**: Direct application of `omegaPullbackCoeff_mem_F_comp_of_omega_zero_leading` with `omegaPullbackCoeff_negFrobeniusIsog`.
- **Hypotheses**: `[Fintype F]`.
- **Uses from project**: `omegaPullbackCoeff_mem_F_comp_of_omega_zero_leading`, `negFrobeniusIsog`, `omegaPullbackCoeff_negFrobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 546–552, proof length 4 lines (term-mode)

---

### `theorem omegaPullbackCoeff_isIntegral_polynomialX_id`
- **Type**: `IsIntegral (Polynomial F) (omegaPullbackCoeff W (Isogeny.id W.toAffine))`
- **What**: `a_id = 1` is integral over `F[X]`. Trivial axiom-clean pass leaf.
- **How**: `rw [omegaPullbackCoeff_id]; exact isIntegral_one`.
- **Hypotheses**: None.
- **Uses from project**: `omegaPullbackCoeff_id`
- **Used by**: unused in file (intermediate leaf for `omegaPullbackCoeff_mem_F_id` which is self-contained)
- **Visibility**: public
- **Lines**: 562–565, proof length 3 lines

---

### `theorem omegaPullbackCoeff_ordAtInfty_nonneg_id`
- **Type**: `(0 : WithTop ℤ) ≤ (...).ordAtInfty (omegaPullbackCoeff W (Isogeny.id W.toAffine))`
- **What**: `a_id = 1` has nonneg ord at infinity (trivially: `ord_∞(algebraMap F KE 1) = 0 ≥ 0`).
- **How**: Uses `omegaPullbackCoeff_id`, `ordAtInfty_algebraMap_F_nonzero`.
- **Hypotheses**: None.
- **Uses from project**: `omegaPullbackCoeff_id`, `ordAtInfty_algebraMap_F_nonzero`, `W_smooth`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 569–577, proof length 8 lines

---

### `theorem omegaPullbackCoeff_mem_F_id`
- **Type**: `∃ c : F, omegaPullbackCoeff W (Isogeny.id W.toAffine) = algebraMap F KE c`
- **What**: `a_id ∈ F` (specifically `a_id = 1`). Identity baseline for the dispatch chain.
- **How**: `⟨1, by rw [omegaPullbackCoeff_id, map_one]⟩`.
- **Hypotheses**: None.
- **Uses from project**: `omegaPullbackCoeff_id`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 581–583, proof length 1 line (term-mode)

---

### `theorem omegaPullbackCoeff_isIntegral_polynomialX_mulByInt`
- **Type**: `[Fintype F] → (n : ℤ) → n ≠ 0 → IsIntegral (Polynomial F) (omegaPullbackCoeff W (mulByInt W.toAffine n))`
- **What**: `a_{[n]}` is integral over `F[X]` (trivially: equals `algebraMap F KE n`). Axiom-clean via routeB.
- **How**: `rw [omegaPullbackCoeff_mulByInt_routeB W n hn]; exact isIntegral_algebraMap`.
- **Hypotheses**: `[Fintype F]`, `n ≠ 0`.
- **Uses from project**: `omegaPullbackCoeff_mulByInt_routeB`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 595–600, proof length 5 lines

---

### `theorem omegaPullbackCoeff_ordAtInfty_nonneg_mulByInt`
- **Type**: `[Fintype F] → (n : ℤ) → n ≠ 0 → (0 : WithTop ℤ) ≤ (...).ordAtInfty (omegaPullbackCoeff W (mulByInt W.toAffine n))`
- **What**: `a_{[n]}` has nonneg ord at infinity. Cases: `(n:F) = 0` gives `ord_∞ 0 = ⊤`; else `ord_∞(algebraMap F KE n) = 0`.
- **How**: Rewrites via `omegaPullbackCoeff_mulByInt_routeB`, then cases on whether `(n:F) = 0`, using `ordAtInfty_zero` or `ordAtInfty_algebraMap_F_nonzero`.
- **Hypotheses**: `[Fintype F]`, `n ≠ 0`.
- **Uses from project**: `omegaPullbackCoeff_mulByInt_routeB`, `HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_zero`, `ordAtInfty_algebraMap_F_nonzero`, `W_smooth`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 605–617, proof length 12 lines

---

### `theorem omegaPullbackCoeff_mem_F_mulByInt`
- **Type**: `[Fintype F] → (n : ℤ) → n ≠ 0 → ∃ c : F, omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE c`
- **What**: `a_{[n]} ∈ F` (specifically `= n`). Axiom-clean direct from routeB closed form.
- **How**: `⟨(n : F), omegaPullbackCoeff_mulByInt_routeB W n hn⟩`.
- **Hypotheses**: `[Fintype F]`, `n ≠ 0`.
- **Uses from project**: `omegaPullbackCoeff_mulByInt_routeB`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 622–626, proof length 2 lines (term-mode)

---

### `theorem omegaPullbackCoeff_isIntegral_polynomialX_negFrobenius`
- **Type**: `[Fintype F] → IsIntegral (Polynomial F) (omegaPullbackCoeff W (negFrobeniusIsog W))`
- **What**: `a_{-π} = 0` is integral. Trivial axiom-clean pass leaf.
- **How**: `rw [omegaPullbackCoeff_negFrobeniusIsog]; exact isIntegral_zero`.
- **Hypotheses**: `[Fintype F]`.
- **Uses from project**: `omegaPullbackCoeff_negFrobeniusIsog`, `negFrobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 637–641, proof length 4 lines

---

### `theorem omegaPullbackCoeff_ordAtInfty_nonneg_negFrobenius`
- **Type**: `[Fintype F] → (0 : WithTop ℤ) ≤ (...).ordAtInfty (omegaPullbackCoeff W (negFrobeniusIsog W))`
- **What**: `a_{-π}` has nonneg ord at infinity. Trivially `⊤ ≥ 0`.
- **How**: Rewrites `omegaPullbackCoeff_negFrobeniusIsog` = 0, then `ordAtInfty_zero = ⊤`, then `le_top`.
- **Hypotheses**: `[Fintype F]`.
- **Uses from project**: `omegaPullbackCoeff_negFrobeniusIsog`, `HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 645–652, proof length 7 lines

---

### `theorem omegaPullbackCoeff_mem_F_negFrobenius`
- **Type**: `[Fintype F] → ∃ c : F, omegaPullbackCoeff W (negFrobeniusIsog W) = algebraMap F KE c`
- **What**: `a_{-π} ∈ F` (specifically `0`). Axiom-clean.
- **How**: `⟨0, by rw [omegaPullbackCoeff_negFrobeniusIsog, map_zero]⟩`.
- **Hypotheses**: `[Fintype F]`.
- **Uses from project**: `omegaPullbackCoeff_negFrobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 657–660, proof length 2 lines (term-mode)

---

### `theorem omegaPullbackCoeff_isIntegral_polynomialX_isogOneSub_negFrobenius`
- **Type**: `[Fintype F] → (p : ℕ) → [Fact p.Prime] → [CharP F p] → (hq : 2 ≤ Fintype.card F) → IsIntegral (Polynomial F) (omegaPullbackCoeff W (isogOneSub_negFrobenius W hq))`
- **What**: `a_{1+π} = 1` is integral. Axiom-clean trivial leaf.
- **How**: `rw [omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one W p hq]; exact isIntegral_one`.
- **Hypotheses**: `[Fintype F]`, `[Fact p.Prime]`, `[CharP F p]`, `2 ≤ Fintype.card F`.
- **Uses from project**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`, `isogOneSub_negFrobenius`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 673–680, proof length 7 lines

---

### `theorem omegaPullbackCoeff_ordAtInfty_nonneg_isogOneSub_negFrobenius`
- **Type**: `[Fintype F] → (p : ℕ) → [Fact p.Prime] → [CharP F p] → (hq : ...) → (0 : WithTop ℤ) ≤ (...).ordAtInfty (omegaPullbackCoeff W (isogOneSub_negFrobenius W hq))`
- **What**: `a_{1+π} = 1` has nonneg ord at infinity. Trivially `ord_∞(algebraMap F KE 1) = 0`.
- **How**: Rewrites via `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`, then `ordAtInfty_algebraMap_F_nonzero`.
- **Hypotheses**: As above.
- **Uses from project**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`, `ordAtInfty_algebraMap_F_nonzero`, `W_smooth`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 684–695, proof length 11 lines

---

### `theorem omegaPullbackCoeff_mem_F_isogOneSub_negFrobenius`
- **Type**: `[Fintype F] → (p : ℕ) → [Fact p.Prime] → [CharP F p] → (hq : ...) → ∃ c : F, omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = algebraMap F KE c`
- **What**: `a_{1+π} ∈ F` (specifically `1`). Key mem_F for the Hasse-bound isogeny.
- **How**: `⟨1, by rw [omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one W p hq, map_one]⟩`.
- **Hypotheses**: As above.
- **Uses from project**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 700–706, proof length 4 lines (term-mode)

---

### `theorem invariantDiff_localExpand_coeff_zero`
- **Type**: `((localExpand W (u_gen W))⁻¹ * LaurentSeries.derivative F (localExpand W (x_gen W))).coeff 0 = 1`
- **What**: The constant term of the local expansion of the invariant differential `ω = u⁻¹ dx` is `1` — the formal-group normalization `ω_F(T) = 1 + O(T)` (Silverman IV.4.2, sub-leaf N).
- **How**: Body is `sorry`.
- **Hypotheses**: None beyond elliptic curve.
- **Uses from project**: `localExpand`, `u_gen`, `x_gen`
- **Used by**: `omegaPullbackCoeff_F_value_eq_coeff_one`
- **Visibility**: public
- **Lines**: 713–716, proof length 1 line
- **Notes**: sorry

---

### `theorem pullback_invariantDiff_coeff_zero`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) → ((localExpand W (alpha_star_u W α))⁻¹ * LaurentSeries.derivative F (localExpand W (α.pullback (x_gen W)))).coeff 0 = (localExpand W (α.pullback (localParam W))).coeff (1 : ℤ)`
- **What**: The constant term of `α*ω` (as a Laurent series) equals the linear coefficient of the local expansion of `α*t` — the chain-rule identity `(α*ω)₀ = (α*t)'(0)` (Silverman IV.4.2/4.3, sub-leaf P).
- **How**: Body is `sorry`.
- **Hypotheses**: Any self-isogeny `α`.
- **Uses from project**: `localExpand`, `alpha_star_u`, `x_gen`, `localParam`
- **Used by**: `omegaPullbackCoeff_F_value_eq_coeff_one`
- **Visibility**: public
- **Lines**: 723–727, proof length 1 line
- **Notes**: sorry

---

### `theorem omegaPullbackCoeff_F_value_eq_coeff_one`
- **Type**: `(α : Isogeny ...) → (c : F) → omegaPullbackCoeff W α = algebraMap F KE c → c = PowerSeries.coeff 1 (formalIsogenySeries W α)`
- **What**: The value `c` of `a_α` (when `a_α = algebraMap c`) equals the linear coefficient of the formal isogeny series (Silverman IV.4.3 / L-KL-main sub-leaf B). Bridges the curve (Kähler) and formal-group (power series) perspectives.
- **How**: Applies `localExpandKaehlerLift` to `omegaPullbackCoeff_spec`, reading off `coeff 0` using `invariantDiff_localExpand_coeff_zero` (N) and `pullback_invariantDiff_coeff_zero` (P).
- **Hypotheses**: `c` explicit, `hc : omegaPullbackCoeff W α = algebraMap F KE c`.
- **Uses from project**: `localExpandKaehlerLift`, `localExpandKaehlerLift_smul`, `localExpandKaehlerLift_D`, `omegaPullbackCoeff_spec`, `invariantDifferential`, `invariantDiff_localExpand_coeff_zero`, `pullback_invariantDiff_coeff_zero`, `formalIsogenySeries_coeff`, `localExpand_algebraMap`, `u_gen`, `x_gen`
- **Used by**: `omegaPullbackCoeff_localExpand_eq_coeff_one`
- **Visibility**: public
- **Lines**: 735–755, proof length ~20 lines
- **Notes**: inherits sorry via sub-leaves

---

### `theorem omegaPullbackCoeff_localExpand_eq_coeff_one`
- **Type**: `(α : Isogeny ...) → localExpand W (omegaPullbackCoeff W α) = HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (PowerSeries.coeff 1 (formalIsogenySeries W α)))`
- **What**: The local expansion of `a_α` equals the constant Laurent series `C(coeff 1 [α_F])`.
- **How**: Obtains `c` from `omegaPullbackCoeff_mem_F`, rewrites via `localExpand_algebraMap` and `omegaPullbackCoeff_F_value_eq_coeff_one`.
- **Hypotheses**: None.
- **Uses from project**: `omegaPullbackCoeff_mem_F`, `omegaPullbackCoeff_F_value_eq_coeff_one`, `localExpand_algebraMap`, `formalIsogenySeries`
- **Used by**: `omegaPullbackCoeff_eq_formalIsogenyLeading_via_localization`
- **Visibility**: public
- **Lines**: 757–763, proof length 6 lines
- **Notes**: inherits sorry via `omegaPullbackCoeff_mem_F`

---

### `theorem omegaPullbackCoeff_eq_formalIsogenyLeading_via_localization`
- **Type**: `(α : Isogeny ...) → omegaPullbackCoeff W α = algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W α))`
- **What**: BRIDGE-001: the curve↔formal bridge `a_α = algebraMap F KE (coeff 1 [α_F])`, via localExpand injectivity.
- **How**: `localExpand_injective W` + `omegaPullbackCoeff_localExpand_eq_coeff_one` + `localExpand_algebraMap`.
- **Hypotheses**: None.
- **Uses from project**: `localExpand_injective`, `omegaPullbackCoeff_localExpand_eq_coeff_one`, `localExpand_algebraMap`
- **Used by**: `omegaPullbackCoeff_mulByInt_via_formalGroup`
- **Visibility**: public
- **Lines**: 768–773, proof length 5 lines
- **Notes**: inherits sorry transitively

---

### `theorem omegaPullbackCoeff_mulByInt_via_formalGroup`
- **Type**: `(m : ℤ) → omegaPullbackCoeff W (mulByInt W.toAffine m) = algebraMap F KE (m : F)`
- **What**: TOP theorem (Silverman III.5.3): `a_{[m]} = m`, wronskian-free, via the formal group. Chains BRIDGE-001 and L-F1.
- **How**: `omegaPullbackCoeff_eq_formalIsogenyLeading_via_localization` + `coeff_one_formalIsogenySeries_mulByInt_eq`.
- **Hypotheses**: None.
- **Uses from project**: `omegaPullbackCoeff_eq_formalIsogenyLeading_via_localization`, `coeff_one_formalIsogenySeries_mulByInt_eq`
- **Used by**: `omegaPullbackCoeff_mulByInt_p_eq_zero_via_formalGroup`
- **Visibility**: public
- **Lines**: 777–780, proof length 3 lines
- **Notes**: inherits sorry transitively

---

### `theorem omegaPullbackCoeff_mulByInt_p_eq_zero_via_formalGroup`
- **Type**: `(p : ℕ) → [CharP F p] → omegaPullbackCoeff W (mulByInt W.toAffine (p : ℤ)) = 0`
- **What**: `a_{[p]} = 0` in char `p` — the wronskian-free Pillar B start (Silverman III.5.3 at `m = p`).
- **How**: Uses `omegaPullbackCoeff_mulByInt_via_formalGroup` + `CharP.cast_eq_zero` + `map_zero`.
- **Hypotheses**: `[CharP F p]`.
- **Uses from project**: `omegaPullbackCoeff_mulByInt_via_formalGroup`
- **Used by**: unused in file (separate wronskian-free route; the file uses `omegaPullbackCoeff_mulByInt_p_eq_zero_routeB` in `D_mulByInt_p_pullback_x_gen_eq_zero`)
- **Visibility**: public
- **Lines**: 787–792, proof length 5 lines
- **Notes**: inherits sorry transitively

---

### `theorem D_mulByInt_p_pullback_x_gen_eq_zero`
- **Type**: `[Fintype F] → (p : ℕ) → [CharP F p] → [Fact p.Prime] → KaehlerDifferential.D F KE ((mulByInt W.toAffine (p : ℤ)).pullback (x_gen W)) = 0`
- **What**: `D([p]*x_gen) = 0` in char `p`. From `omegaPullbackCoeff_spec` at `[p]` + `a_{[p]} = 0` and the non-vanishing of `([p]*u)⁻¹`.
- **How**: Rewrites `omegaPullbackCoeff_spec` with `omegaPullbackCoeff_mulByInt_p_eq_zero_routeB` (axiom-clean routeB), giving `0 = ([p]*u)⁻¹ • D([p]*x)`, then resolves by `inv_ne_zero` and `smul_eq_zero`.
- **Hypotheses**: `[Fintype F]`, `[CharP F p]`, `[Fact p.Prime]`.
- **Uses from project**: `omegaPullbackCoeff_spec`, `omegaPullbackCoeff_mulByInt_p_eq_zero_routeB`, `alpha_star_u`, `alpha_star_u_eq`, `u_gen_ne_zero`, `x_gen`
- **Used by**: `mulByInt_p_pullback_x_gen_mem_pth_powers`
- **Visibility**: public
- **Lines**: 797–809, proof length 12 lines

---

### `theorem kaehlerD_pth_power_eq_zero`
- **Type**: `(p : ℕ) → [CharP F p] → (g : KE) → KaehlerDifferential.D F KE (g ^ p) = 0`
- **What**: `D(gᵖ) = 0` in char `p` — a key property of Kähler derivations in characteristic `p`.
- **How**: Uses `Derivation.leibniz_pow` and `CharP.cast_eq_zero` (after casting `p • · = (p : KE) • ·`).
- **Hypotheses**: `[CharP F p]`.
- **Uses from project**: `charP_of_injective_algebraMap`, `algebraMap`
- **Used by**: `kaehlerD_pth_power_mul`, `kaehlerD_eq_zero_iff_mem_pth_powers`, `x_gen_not_pth_power`
- **Visibility**: public
- **Lines**: 812–818, proof length 6 lines

---

### `theorem kaehlerD_pth_power_mul`
- **Type**: `(p : ℕ) → [CharP F p] → (g h : KE) → KaehlerDifferential.D F KE (g ^ p * h) = g ^ p • KaehlerDifferential.D F KE h`
- **What**: `D` is `K(E)ᵖ`-semilinear: `D(gᵖ · h) = gᵖ · Dh`. This makes `ker D` a `K(E)ᵖ`-submodule.
- **How**: `Derivation.leibniz` + `kaehlerD_pth_power_eq_zero`.
- **Hypotheses**: `[CharP F p]`.
- **Uses from project**: `kaehlerD_pth_power_eq_zero`
- **Used by**: unused in file (used conceptually in the `ker D` IntermediateField construction inside `kaehlerD_eq_zero_iff_mem_pth_powers`)
- **Visibility**: public
- **Lines**: 822–824, proof length 2 lines

---

### `theorem kaehlerD_ne_zero`
- **Type**: `∃ w : KE, KaehlerDifferential.D F KE w ≠ 0`
- **What**: The Kähler derivation D is nontrivial — some element has nonzero differential. Implies `ker D ⊊ K(E)`.
- **How**: Contradicts `span_range_derivation` (Ω = span of range D) with `kaehler_rank_one` (finrank Ω = 1 ≠ 0) by showing D ≡ 0 would force Ω = 0.
- **Hypotheses**: None (no `[CharP]` assumed).
- **Uses from project**: `kaehler_rank_one`
- **Used by**: `kaehlerD_eq_zero_iff_mem_pth_powers`
- **Visibility**: public
- **Lines**: 828–843, proof length 15 lines

---

### `theorem x_gen_not_pth_power`
- **Type**: `(p : ℕ) → [CharP F p] → ¬ ∃ w : KE, w ^ p = x_gen W`
- **What**: `x_gen` is not a `p`-th power in `K(E)`, because `D(wᵖ) = 0` but `D(x_gen) ≠ 0`.
- **How**: `kaehlerD_pth_power_eq_zero` + `D_x_ne_zero` (from project).
- **Hypotheses**: `[CharP F p]`.
- **Uses from project**: `kaehlerD_pth_power_eq_zero`, `D_x_ne_zero`, `x_gen`
- **Used by**: `minpoly_x_gen_frobeniusRange_natDegree` (in proving `n ≠ 0`)
- **Visibility**: public
- **Lines**: 847–852, proof length 5 lines

---

### `theorem isPurelyInseparable_frobeniusRange_p`
- **Type**: `(p : ℕ) → [Fact p.Prime] → [CharP F p] → IsPurelyInseparable ↥((frobenius KE p).fieldRange) KE`
- **What**: `K(E)` is purely inseparable over its subfield of `p`-th powers `K(E)ᵖ`.
- **How**: Uses `isPurelyInseparable_iff_pow_mem`, noting `xᵖ = frobenius x ∈ K(E)ᵖ` for every `x`.
- **Hypotheses**: `[Fact p.Prime]`, `[CharP F p]`.
- **Uses from project**: `charP_of_injective_algebraMap`
- **Used by**: `minpoly_x_gen_frobeniusRange_natDegree`, `finrank_KE_over_frobeniusRange_p`, `kaehlerD_eq_zero_iff_mem_pth_powers`
- **Visibility**: public
- **Lines**: 856–862, proof length 6 lines

---

### `theorem minpoly_x_gen_frobeniusRange_natDegree`
- **Type**: `(p : ℕ) → [Fact p.Prime] → [CharP F p] → [PerfectField F] → (minpoly ↥((frobenius KE p).fieldRange) (x_gen W)).natDegree = p`
- **What**: The minimal polynomial of `x_gen` over `K(E)ᵖ` has degree exactly `p`.
- **How**: Uses `IsPurelyInseparable.minpoly_eq_X_pow_sub_C` to get `minpoly = X^(pⁿ) - C y`; upper bound `pⁿ ≤ p` from divisibility by `Xᵖ - x_genᵖ`; lower bound `n ≥ 1` from `x_gen_not_pth_power`; then `n = 1` by primality.
- **Hypotheses**: `[Fact p.Prime]`, `[CharP F p]`, `[PerfectField F]`.
- **Uses from project**: `isPurelyInseparable_frobeniusRange_p`, `x_gen_not_pth_power`, `x_gen`, `charP_of_injective_algebraMap`
- **Used by**: `finrank_KE_over_frobeniusRange_p`
- **Visibility**: public
- **Lines**: 867–916, proof length ~49 lines
- **Notes**: proof > 30 lines

---

### `theorem isSeparable_KE_over_frobeniusRange_adjoin_x_gen`
- **Type**: `(p : ℕ) → [Fact p.Prime] → [CharP F p] → [PerfectField F] → (halg : Algebra ...) → (hsep0 : @Algebra.IsSeparable ...) → (htower : IsScalarTower ...) → Algebra.IsSeparable ↥(IntermediateField.adjoin ↥((frobenius KE p).fieldRange) {x_gen W}) KE`
- **What**: `K(E)` is separable over `K(E)ᵖ(x_gen)`, by being separable over `F(x_gen) = FractionRing(F[X])` (by tower law for separability).
- **How**: Uses `Algebra.isSeparable_tower_top_of_isSeparable` after constructing an `Algebra (FractionRing (Polynomial F)) ↥L` instance by showing the image of `FractionRing(F[X])` lies in `L` (via `surjective_frobenius` + induction on polynomials).
- **Hypotheses**: `[Fact p.Prime]`, `[CharP F p]`, `[PerfectField F]`; explicit `FractionRing` algebra and isSeparable instances passed as terms due to the `backward.isDefEq.respectTransparency false` option.
- **Uses from project**: `charP_of_injective_algebraMap`, `functionField_algebra_fractionRing`, `functionField_isSeparable`, `functionField_isScalarTower`, `x_gen`
- **Used by**: `finrank_KE_over_frobeniusRange_p`
- **Visibility**: public
- **Lines**: 924–977, proof length ~53 lines
- **Notes**: proof > 30 lines; uses `set_option backward.isDefEq.respectTransparency false` (no justifying comment in option line itself, context is in docstring)

---

### `theorem finrank_KE_over_frobeniusRange_p`
- **Type**: `(p : ℕ) → [Fact p.Prime] → [CharP F p] → [PerfectField F] → Module.finrank ↥((frobenius KE p).fieldRange) KE = p`
- **What**: The degree `[K(E) : K(E)ᵖ] = p` (SK-KERD-FINRANK-P). Key step for the Kähler kernel = `K(E)ᵖ` argument.
- **How**: Shows `K(E) = K(E)ᵖ(x_gen)` via purely-inseparable + separable (using `isSeparable_KE_over_frobeniusRange_adjoin_x_gen` and `isPurelyInseparable_frobeniusRange_p`), then `IntermediateField.adjoin.finrank` + `minpoly_x_gen_frobeniusRange_natDegree`.
- **Hypotheses**: `[Fact p.Prime]`, `[CharP F p]`, `[PerfectField F]`.
- **Uses from project**: `isPurelyInseparable_frobeniusRange_p`, `isSeparable_KE_over_frobeniusRange_adjoin_x_gen`, `minpoly_x_gen_frobeniusRange_natDegree`, `functionField_algebra_fractionRing`, `functionField_isSeparable`, `functionField_isScalarTower`, `x_gen`, `charP_of_injective_algebraMap`
- **Used by**: `kaehlerD_eq_zero_iff_mem_pth_powers`
- **Visibility**: public
- **Lines**: 986–1018, proof length ~32 lines
- **Notes**: proof > 30 lines; `set_option maxHeartbeats 1600000` + `set_option synthInstance.maxHeartbeats 1600000` (no justifying comment on the option lines)

---

### `theorem kaehlerD_eq_zero_iff_mem_pth_powers`
- **Type**: `(p : ℕ) → [Fact p.Prime] → [CharP F p] → [PerfectField F] → (w : KE) → KaehlerDifferential.D F KE w = 0 ↔ ∃ g : KE, g ^ p = w`
- **What**: Characterizes the kernel of the Kähler derivation D in characteristic `p`: `ker D = K(E)ᵖ` (the image of Frobenius). The forward direction is the nontrivial part, using the finrank argument.
- **How**: Forward: constructs `ker D` as an `IntermediateField` over `K(E)ᵖ`; uses `finrank_KE_over_frobeniusRange_p` (= p prime) + `kaehlerD_ne_zero` (M ≠ ⊤) + Frobenius rank forcing `M = ⊥`, giving `w ∈ K(E)ᵖ`. Backward: `kaehlerD_pth_power_eq_zero`.
- **Hypotheses**: `[Fact p.Prime]`, `[CharP F p]`, `[PerfectField F]`.
- **Uses from project**: `charP_of_injective_algebraMap`, `finrank_KE_over_frobeniusRange_p`, `kaehlerD_pth_power_eq_zero`, `kaehlerD_ne_zero`, `isPurelyInseparable_frobeniusRange_p`
- **Used by**: `mulByInt_p_pullback_x_gen_mem_pth_powers`
- **Visibility**: public
- **Lines**: 1023–1080, proof length ~57 lines
- **Notes**: proof > 30 lines; `set_option maxHeartbeats 1600000` + `set_option synthInstance.maxHeartbeats 1600000` (no comment)

---

### `theorem mulByInt_p_pullback_x_gen_mem_pth_powers`
- **Type**: `[Fintype F] → (p : ℕ) → [Fact p.Prime] → [CharP F p] → [PerfectField F] → ∃ g : KE, g ^ p = (mulByInt W.toAffine (p : ℤ)).pullback (x_gen W)`
- **What**: `[p]*x_gen` is a `p`-th power in `K(E)` (SK-QTH). Concrete reduction: `D([p]*x_gen) = 0` implies membership in `ker D = K(E)ᵖ`.
- **How**: Applies `kaehlerD_eq_zero_iff_mem_pth_powers` to `D_mulByInt_p_pullback_x_gen_eq_zero`.
- **Hypotheses**: `[Fintype F]`, `[Fact p.Prime]`, `[CharP F p]`, `[PerfectField F]`.
- **Uses from project**: `kaehlerD_eq_zero_iff_mem_pth_powers`, `D_mulByInt_p_pullback_x_gen_eq_zero`, `x_gen`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1084–1087, proof length 2 lines (term-mode)

---

### `theorem omegaPullbackCoeff_id_isConstant`
- **Type**: `omegaPullbackCoeff W (Isogeny.id W.toAffine) ∈ (algebraMap F KE).range`
- **What**: `a_id ∈ range(algebraMap F KE)`. Alternate phrasing for `FormalGroupBridge` consumers.
- **How**: `⟨1, by rw [omegaPullbackCoeff_id, map_one]⟩`.
- **Hypotheses**: None.
- **Uses from project**: `omegaPullbackCoeff_id`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1096–1098, proof length 1 line (term-mode)

---

### `theorem omegaPullbackCoeff_frobenius_isConstant`
- **Type**: `[Fintype F] → omegaPullbackCoeff W (frobeniusIsog W) ∈ (algebraMap F KE).range`
- **What**: `a_π ∈ range(algebraMap F KE)`. Alternate phrasing for `FormalGroupBridge` consumers.
- **How**: `⟨0, by rw [omegaPullbackCoeff_frobenius, map_zero]⟩`.
- **Hypotheses**: `[Fintype F]`.
- **Uses from project**: `omegaPullbackCoeff_frobenius`, `frobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1101–1103, proof length 1 line (term-mode)

---

### `theorem omegaPullbackCoeff_negFrobeniusIsog_isConstant`
- **Type**: `[Fintype F] → omegaPullbackCoeff W (negFrobeniusIsog W) ∈ (algebraMap F KE).range`
- **What**: `a_{-π} ∈ range(algebraMap F KE)`.
- **How**: `⟨0, by rw [omegaPullbackCoeff_negFrobeniusIsog, map_zero]⟩`.
- **Hypotheses**: `[Fintype F]`.
- **Uses from project**: `omegaPullbackCoeff_negFrobeniusIsog`, `negFrobeniusIsog`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1106–1108, proof length 1 line (term-mode)

---

### `theorem omegaPullbackCoeff_isogOneSub_negFrobenius_isConstant`
- **Type**: `[Fintype F] → (p : ℕ) → [Fact p.Prime] → [CharP F p] → (hq : 2 ≤ Fintype.card F) → omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) ∈ (algebraMap F KE).range`
- **What**: `a_{1+π} ∈ range(algebraMap F KE)`.
- **How**: `⟨1, by rw [omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one W p hq, map_one]⟩`.
- **Hypotheses**: `[Fintype F]`, `[Fact p.Prime]`, `[CharP F p]`, `2 ≤ Fintype.card F`.
- **Uses from project**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`, `isogOneSub_negFrobenius`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1113–1117, proof length 2 lines (term-mode)

---

## Summary statistics

- **Total declarations**: 73 (5 sorry-bearing)
- **Defs** (including noncomputable def): 2 (`localExpandDeriv`, `localExpandKaehlerLift`)
- **Structures**: 1 (`LExp`)
- **Instances**: 10
- **Theorems/Lemmas**: 60
- **Sorries**: `formalIsogenySeries_FGL_additivity`, `coeff_one_formalIsogenySeries_mulByInt_nonpos`, `omegaPullbackCoeff_isIntegral_polynomialX`, `omegaPullbackCoeff_ordAtInfty_nonneg`, `invariantDiff_localExpand_coeff_zero`, `pullback_invariantDiff_coeff_zero`
- **Long proofs (>30 lines)**: `laurentSeries_derivative_mul` (~109), `minpoly_x_gen_frobeniusRange_natDegree` (~49), `isSeparable_KE_over_frobeniusRange_adjoin_x_gen` (~53), `finrank_KE_over_frobeniusRange_p` (~32), `kaehlerD_eq_zero_iff_mem_pth_powers` (~57)
