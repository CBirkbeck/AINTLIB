# Inventory: PadicLFunctions/Interpolation/LpFunction.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/Interpolation/LpFunction.lean`

Module context: defines RJW's p-adic L-function `L_p(θ,s)` of a Dirichlet character (RJW §5.3, Def 5.18) via the cleared measure `ζ_η` on `ℤ_p^×`, and proves the Kubota–Leopoldt interpolation Theorem 5.19 (`Lp_interpolation`).

Section variables (apply to all decls): `p : ℕ` with `[Fact p.Prime]`; `K : Type*` a complete charzero ultrametric `NormedField` that is a `NormedAlgebra ℚ_[p]`. Everything is in `namespace PadicLFunctions.MeasureR`, `noncomputable section`.

---

### def teichmullerCharR
- Type: `DirichletCharacter (integerRing K) p`
- What: The Teichmüller character `ω` on `ℤ/p`, upgraded from `PadicInt.teichmullerChar p` (valued in `ℤ_[p]`) to coefficients in `integerRing K` by composing with the structure ring hom `algebraMap ℤ_[p] (integerRing K)`.
- How: Direct definition via `MulChar.ringHomComp` of `PadicInt.teichmullerChar p` along `algebraMap ℤ_[p] (integerRing K)`.
- Hypotheses: none beyond the section instances.
- Uses from project: [] (uses only `PadicInt.teichmullerChar`, an upstream/non-project namespace, and `integerRing`)
- Used by: `twistedPChar`, and inside `Lp_interpolation`'s proof (`hkey`/`hpt` rewrites)
- Visibility: public
- Lines: 35–38 (def, no proof)
- Notes: none

### def invUnitsCM
- Type: `C(ℤ_[p]ˣ, integerRing K)`
- What: The continuous map `x ↦ x⁻¹` on `ℤ_p^×`, valued in `integerRing K` (the coefficient upgrade of `PadicMeasure.invCM p` along the isometric structure map).
- How: Bundles `fun u => algebraMap ℤ_[p] (integerRing K) (PadicMeasure.invCM p u)`; continuity from composing `integerRing.isometry_algebraMap`'s continuity with `map_continuous (PadicMeasure.invCM p)`.
- Hypotheses: none beyond section instances.
- Uses from project: [`PadicMeasure.invCM`, `integerRing.isometry_algebraMap`]
- Used by: `zetaEtaCleared`, `invUnitsCM_apply`, `zetaEtaCleared_apply`, and `Lp_interpolation`'s proof (`hpt`, `hfun`)
- Visibility: public
- Lines: 40–44 (def, no proof)
- Notes: none

### def anglePowCM
- Type: `(s : ℤ_[p]) → C(ℤ_[p]ˣ, integerRing K)`
- What: The continuous map `x ↦ ⟨x⟩^s` on `ℤ_p^×` for fixed `s ∈ ℤ_p` (raising the principal-unit part `angleUnit` to the p-adic power `s` via `onePAdicPow`), valued in `integerRing K`.
- How: Bundles `algebraMap` of `PadicInt.onePAdicPow p (angleUnit ...) ... s`; continuity from `integerRing.isometry_algebraMap`'s continuity composed with `continuous_onePAdicPow_angleUnit p s`.
- Hypotheses: a fixed exponent `s : ℤ_[p]`.
- Uses from project: [`PadicInt.onePAdicPow`, `PadicInt.angleUnit`, `PadicInt.angleUnit_sub_one_mem`, `continuous_onePAdicPow_angleUnit`, `integerRing.isometry_algebraMap`]
- Used by: `LpFunction`, `anglePowCM_apply`, and `Lp_interpolation`'s proof
- Visibility: public
- Lines: 46–53 (def, no proof)
- Notes: none

### def zetaEtaCleared
- Type: `{D : ℕ} [NeZero D] (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p:ℕ) ∣ D) : MeasureR K ℤ_[p]ˣ`
- What: RJW's measure `ζ_η = x⁻¹·Res_{ℤ_p^×}(μ_η)` on `ℤ_p^×` in the Gauss-cleared normalisation `G(η⁻¹)·ζ_η`; pairing `g` against it integrates `x⁻¹·g` (extended by zero) against the cleared measure `μ̃_η`.
- How: Composes `muEtaCleared p K η hζ hD` (a `MeasureR` on `ℤ_p`) with the linear map `extendByZero ∘ (multiplication by invUnitsCM)`, so `ζ_η.comp T` precomposes test functions by `T`.
- Hypotheses: `D ≠ 0`; `ζ` a primitive `D`-th root of unity; `p ∤ D` (η of conductor prime to p).
- Uses from project: [`MeasureR`, `muEtaCleared`, `extendByZero`, `invUnitsCM`]
- Used by: `LpFunction`, `zetaEtaCleared_apply`, and `Lp_interpolation`'s proof
- Visibility: public
- Lines: 55–63 (def, no proof)
- Notes: none

### def LpFunction
- Type: `... (η : DirichletCharacter (integerRing K) D) (hζ : IsPrimitiveRoot ζ D) (hD : ¬ p ∣ D) {n : ℕ} (χ : DirichletCharacter (integerRing K) (p^n)) (s : ℤ_[p]) : K`
- What: RJW Def 5.18, the p-adic L-function `L_p(θ,s) = ∫_{ℤ_p^×} χ(x)⟨x⟩^{1−s}·ζ_η` of `θ = χη`, returned as a `K`-value; the Gauss-sum clearing of `μ̃_η` is divided back out by multiplying by `G(η⁻¹)⁻¹`.
- How: Direct definition: `(gaussSum η⁻¹ (zmodChar D ...))⁻¹` (cast to `K`) times the `K`-cast of `zetaEtaCleared` paired against the test function `χ.toContinuousMapZp ∘ unitsValCM * anglePowCM (1−s)`.
- Hypotheses: `D ≠ 0`; `ζ` primitive `D`-th root; `p ∤ D`; `χ` a Dirichlet character of `p`-power level `p^n`; exponent `s ∈ ℤ_p`.
- Uses from project: [`zetaEtaCleared`, `anglePowCM`, `PadicMeasure.unitsValCM`] (also `gaussSum`/`AddChar.zmodChar`/`toContinuousMapZp` from upstream)
- Used by: `Lp_interpolation`
- Visibility: public
- Lines: 65–75 (def, no proof)
- Notes: none

### def twistedPChar
- Type: `{n : ℕ} (χ : DirichletCharacter (integerRing K) (p^n)) (k : ℕ) : DirichletCharacter (integerRing K) (p ^ max n 1)`
- What: The p-part of `θω^{−k}`, namely the character `χ·ω^{−k}` realised at level `p^{max n 1}` (the join of χ's level `p^n` and ω's level `p^1`).
- How: Product (in the Dirichlet-character monoid) of `changeLevel χ` (to `p^{max n 1}`) and the `k`-th power of the inverse of `changeLevel teichmullerCharR` (to `p^{max n 1}`).
- Hypotheses: `χ` of level `p^n`; nonnegative twist exponent `k`.
- Uses from project: [`teichmullerCharR`]
- Used by: `Lp_interpolation` (hypothesis `hχ'` and proof step `hkey`)
- Visibility: public
- Lines: 77–84 (def, no proof)
- Notes: none

### lemma invUnitsCM_apply
- Type: `(u : ℤ_[p]ˣ) : invUnitsCM p K u = algebraMap ℤ_[p] (integerRing K) (PadicMeasure.invCM p u)`
- What: Computes `invUnitsCM` pointwise as the `algebraMap` image of `invCM`.
- How: `rfl`.
- Hypotheses: none.
- Uses from project: [`invUnitsCM`, `PadicMeasure.invCM`]
- Used by: `Lp_interpolation`'s proof (`hpt`)
- Visibility: public
- Lines: 88–93 (proof 1 line, `rfl`)
- Notes: `@[simp]`; `omit [CompleteSpace K] [CharZero K]`

### lemma anglePowCM_apply
- Type: `(s : ℤ_[p]) (u : ℤ_[p]ˣ) : anglePowCM p K s u = algebraMap ℤ_[p] (integerRing K) (PadicInt.onePAdicPow p (angleUnit p u) (angleUnit_sub_one_mem p u) s)`
- What: Computes `anglePowCM` pointwise as the `algebraMap` image of `onePAdicPow` of the angle unit.
- How: `rfl`.
- Hypotheses: a fixed `s : ℤ_[p]`.
- Uses from project: [`anglePowCM`, `PadicInt.onePAdicPow`, `PadicInt.angleUnit`, `PadicInt.angleUnit_sub_one_mem`]
- Used by: `Lp_interpolation`'s proof (`hpt`)
- Visibility: public
- Lines: 95–102 (proof 1 line, `rfl`)
- Notes: `@[simp]`; `omit [CompleteSpace K] [CharZero K]`

### lemma zetaEtaCleared_apply
- Type: `... (g : C(ℤ_[p]ˣ, integerRing K)) : zetaEtaCleared p K η hζ hD g = muEtaCleared p K η hζ hD (extendByZero p K (invUnitsCM p K * g))`
- What: Unfolds the pairing of the measure `zetaEtaCleared` against a test function `g` into integrating `invUnitsCM * g`, extended by zero, against `muEtaCleared`.
- How: `rfl` (the composition in `zetaEtaCleared`'s definition computes definitionally).
- Hypotheses: `D ≠ 0`; `ζ` primitive `D`-th root; `p ∤ D`; test function `g`.
- Uses from project: [`zetaEtaCleared`, `muEtaCleared`, `extendByZero`, `invUnitsCM`]
- Used by: `Lp_interpolation`'s proof
- Visibility: public
- Lines: 104–112 (proof 1 line, `rfl`)
- Notes: `@[simp]`; `omit [CharZero K]`

### lemma exists_primitive_pPow_factorisation
- Type: `{R : Type*} [CommMonoidWithZero R] {M : ℕ} (ψ : DirichletCharacter R (p^M)) : ∃ (m : ℕ) (hm : m ≤ M) (ψ₀ : DirichletCharacter R (p^m)), ψ₀.IsPrimitive ∧ ψ = changeLevel (pow_dvd_pow p hm) ψ₀`
- What: Every Dirichlet character of `p`-power level `p^M` factors through a primitive character `ψ₀` at a `p`-power sub-level `p^m` with `m ≤ M` (RJW T516 conductor argument, packaged to instantiate `Lp_interpolation`).
- How: The conductor of `ψ` divides `p^M`, so `Nat.dvd_prime_pow` writes `ψ.conductor = p^m` with `m ≤ M`; then `ψ` factors through its conductor (`factorsThrough_conductor`), giving `ψ₀`. Primitivity (`conductor ψ₀ = p^m`) is `le_antisymm`: `≤` from `conductor_dvd_level`, `≥` by showing `ψ₀.conductor ∈ conductorSet ψ` (via `changeLevel_trans`/`changeLevel_primitiveCharacter`) and `Nat.sInf_le`, with `p^m = ψ.conductor`.
- Hypotheses: `R` a `CommMonoidWithZero`; `ψ` a Dirichlet character at level `p^M`.
- Uses from project: [] (relies on mathlib `DirichletCharacter` API: `conductor_dvd_level`, `factorsThrough_conductor`, `conductorSet`, `primitiveCharacter`, `changeLevel_trans`, `changeLevel_primitiveCharacter`)
- Used by: unused in file (documented as supplied to callers instantiating `Lp_interpolation`)
- Visibility: public
- Lines: 117–138 (proof ~17 lines)
- Notes: none

### theorem Lp_interpolation
- Type: large; abbreviated. `{D : ℕ} [NeZero D] (hD1 : 1 < D) {η} (hη : η.IsPrimitive) {ζ} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ p ∣ D) {n} {χ : DirichletCharacter (integerRing K) (p^n)} (_hχ : χ.IsPrimitive) {ε} (hε : IsPrimitiveRoot ε (p^max n 1)) {k} (hk : 0 < k) {m} (hmle : m ≤ max n 1) {χ' : DirichletCharacter ... (p^m)} (hχ'prim) (hχ' : twistedPChar p K χ k = changeLevel ... χ') {θ'} (hθ' : θ' = changeLevel ... η * changeLevel ... χ') : LpFunction p K η hζ hD χ (1 − (k:ℤ_[p])) = (1 − (θ' (p : ZMod (D*p^m)) : K) * (p:K)^(k−1)) * LvalNeg (toFieldChar θ') (k−1)`
- What: RJW Theorem 5.19 (Kubota–Leopoldt interpolation): for all `k ≥ 1`, `L_p(θ, 1−k) = (1 − θω^{−k}(p)·p^{k−1})·L(θω^{−k}, 1−k)`, where `χ'` is the primitive core of the p-part `χ·ω^{−k}`, and `θ' = η·χ'` realises `θω^{−k}` at its conductor `D·p^m`.
- How: Rewrites `k = k'+1`; gets a primitive root `ε^{p^{...}}` at level `p^m` (`hε.pow_of_dvd`, `Nat.pow_div`, `Nat.sub_sub_self`) to invoke `zetaEta_twisted_moments` (`hmom`). Key character identity `hkey`: `changeLevel χ = changeLevel χ' · (changeLevel ω)^{k'+1}` from `hχ'`/`twistedPChar` by `inv_mul_cancel`. Pointwise `hpt`: on each unit `u`, `x⁻¹·χ(x)·⟨x⟩^{k'+1} = χ'(x)·x^{k'}`, proved by pushing `hkey` through `toContinuousMapZp_changeLevel`, `castHom_toZModPow_eq_toZMod`, `teichmullerChar_toZMod`, and the units identity `teichmuller_mul_angleUnit` (so `u⁻¹·(τ·angle)^{k'+1} = u^{k'}`), then `onePAdicPow_natCast`. Then `hfun` extends this to test functions (split `IsUnit x` / not, via `extendByZero_coe_unit`/`charFnCM_apply`/`Set.indicator`). Finally `LpFunction` unfolds, `hfun` rewrites the integrand into `charFnCM_units * (χ'.toContinuousMapZp * powCM k')`, identified with `twist ... (res ...) (powCM k')`, fed to `hmom`; the Gauss unit `G(η⁻¹) ≠ 0` (`gaussSum_isUnit_of_coprime`) cancels via `inv_mul_cancel₀`.
- Hypotheses: `D > 1`; `η` primitive of conductor `D`; `ζ` primitive `D`-th root; `p ∤ D`; `χ` primitive of level `p^n`; `ε` primitive `p^{max n 1}`-th root; `k ≥ 1`; `m ≤ max n 1`; `χ'` primitive at level `p^m` equal to the primitive core of `twistedPChar χ k`; `θ' = η·χ'` at level `D·p^m`.
- Uses from project: [`LpFunction`, `zetaEtaCleared` (via `zetaEtaCleared_apply`), `zetaEtaCleared_apply`, `twistedPChar`, `teichmullerCharR`, `invUnitsCM` (via `invUnitsCM_apply`), `invUnitsCM_apply`, `anglePowCM` (via `anglePowCM_apply`), `anglePowCM_apply`, `zetaEta_twisted_moments`, `muEtaCleared`, `extendByZero`, `charFnCM`, `twist`, `res`, `powCM`, `powCM_apply`, `toFieldChar`, `LvalNeg`, `gaussSum_isUnit_of_coprime`, `PadicMeasure.unitsValCM`, `PadicMeasure.invCM`, `PadicMeasure.isClopen_units`, `DirichletCharacter.toContinuousMapZp_changeLevel`, `PadicInt.teichmullerFun`, `PadicInt.angleUnit`, `PadicInt.teichmuller`, `PadicInt.teichmuller_mul_angleUnit`, `PadicInt.onePAdicPow_natCast`, `PadicInt.castHom_toZModPow_eq_toZMod`, `PadicInt.teichmullerChar_toZMod`, `extendByZero_coe_unit`, `charFnCM_apply`]
- Used by: unused in file (top-level theorem of the module)
- Visibility: public
- Lines: 140–268 (proof ~105 lines)
- Notes: **OVER-50** (needs `/decompose-proof`); uses `classical`; no `sorry`/`set_option`/`TODO`. Natural decomposition boundaries already present as named `have`s: `hε'`, `hkey`, `hpt` (the ~50-line pointwise core), `hfun`, `hG`.

---

## File Summary

- **Total declarations: 10** — defs: 6 (`teichmullerCharR`, `invUnitsCM`, `anglePowCM`, `zetaEtaCleared`, `LpFunction`, `twistedPChar`) / lemmas+theorems: 4 (`invUnitsCM_apply`, `anglePowCM_apply`, `zetaEtaCleared_apply`, `exists_primitive_pPow_factorisation`, `Lp_interpolation` — i.e. 1 theorem + 3 `_apply` simp lemmas) / instances: 0.
  - (Counting: 6 defs + 5 lemma/theorem-kind decls = 11 if `Lp_interpolation` is counted as a theorem alongside the 4 lemmas. The 4 `lemma`s plus 1 `theorem` = 5 lemma/theorem declarations.)
- **Key API (used by ≥3 decls in-file):**
  - `invUnitsCM` — used by `zetaEtaCleared`, `invUnitsCM_apply`, `zetaEtaCleared_apply`, `Lp_interpolation` (4).
  - `anglePowCM` — used by `LpFunction`, `anglePowCM_apply`, `Lp_interpolation` (3).
  - `zetaEtaCleared` — used by `LpFunction`, `zetaEtaCleared_apply`, `Lp_interpolation` (3).
  - (`teichmullerCharR` used by `twistedPChar` + `Lp_interpolation` = 2; below threshold.)
- **Unused in file:** `exists_primitive_pPow_factorisation` and `Lp_interpolation` (both are exported module API — the theorem is the headline result; the factorisation lemma supplies a `Lp_interpolation` hypothesis to external callers). `LpFunction` and `twistedPChar` are used (by `Lp_interpolation`).
- **Declarations with `sorry`:** none.
- **`set_option`:** none.
- **Proofs > 50 lines: 1** — `Lp_interpolation` (~105 lines).
- **Proofs 30–50 lines: 0** (`exists_primitive_pPow_factorisation` ~17 lines is the next-largest).
