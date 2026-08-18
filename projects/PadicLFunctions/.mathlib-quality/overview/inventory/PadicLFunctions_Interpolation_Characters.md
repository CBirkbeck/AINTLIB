# Inventory: PadicLFunctions/Interpolation/Characters.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/Interpolation/Characters.lean`

Dirichlet characters as continuous functions on `ℤ_[p]`, and Gauss sums (RJW §5.1). Imports `PadicLFunctions.Coefficients` and `PadicLFunctions.Measure.Basic`.

---

### def DirichletCharacter.toContinuousMapZp
- Type: `(χ : DirichletCharacter R (p ^ n)) : C(ℤ_[p], R)` (R a `NormedCommRing`)
- What: Realizes a Dirichlet character mod `p^n` as a continuous (locally constant) bundled map `ℤ_[p] → R` via `x ↦ χ (PadicInt.toZModPow n x)`, reduction mod `p^n`.
- How: Continuity proved through `IsLocallyConstant.continuous`; the preimage of any set is rewritten as a finite union of `toZModPow`-fibers (indexed by `b` with `χ b ∈ s`), each open by `PadicMeasure.isOpen_toZModPow_fiber`, then `isOpen_biUnion`.
- Hypotheses: `χ` a Dirichlet character with modulus `p ^ n`; `R` a normed commutative ring. Opened `Classical`.
- Uses from project: [`PadicMeasure.isOpen_toZModPow_fiber`]
- Used by: `toContinuousMapZp_apply`, `toContinuousMapZp_eq_zero`, `toContinuousMapZp_changeLevel`, `toContinuousMapZp_mul`, `isLocallyConstant_toContinuousMapZp`, `norm_toContinuousMapZp_le`
- Visibility: public (`_root_.DirichletCharacter`, noncomputable)
- Lines: 39-49 (proof ~8 lines)
- Notes: none

### lemma DirichletCharacter.toContinuousMapZp_apply
- Type: `(χ : DirichletCharacter R (p ^ n)) (x : ℤ_[p]) : χ.toContinuousMapZp x = χ (PadicInt.toZModPow n x)`
- What: The defining unfolding equation: the bundled map at `x` equals `χ` of the mod-`p^n` reduction of `x`.
- How: `rfl` (definitional).
- Hypotheses: as above.
- Uses from project: [`DirichletCharacter.toContinuousMapZp`]
- Used by: `toContinuousMapZp_changeLevel`
- Visibility: public; `@[simp]`
- Lines: 51-54 (proof 1 line)
- Notes: none

### lemma DirichletCharacter.toContinuousMapZp_eq_zero
- Type: `(χ : DirichletCharacter R (p ^ n)) (hn : 1 ≤ n) {x : ℤ_[p]} (hx : ¬IsUnit x) : χ.toContinuousMapZp x = 0`
- What: For `n ≥ 1` the function vanishes at every non-unit `x` (the character kills non-units, which reduce to non-units mod `p^n`).
- How: Reduces via `χ.map_nonunit` to showing `toZModPow n x` is a non-unit; contrapositive uses `PadicInt.isUnit_iff` and `PadicInt.norm_lt_one_iff_dvd` to write `x = p·y`, derives `IsUnit (p : ZMod (p^n))` via `isUnit_of_mul_isUnit_left`, then `ZMod.isUnit_iff_coprime` + `Nat.coprime_pow_right_iff` contradicts `hp.out.ne_one`.
- Hypotheses: modulus `p^n` with `n ≥ 1`; `x` not a unit in `ℤ_[p]`; `p` prime (`Fact`).
- Uses from project: [`DirichletCharacter.toContinuousMapZp`]
- Used by: unused in file
- Visibility: public
- Lines: 56-71 (proof ~11 lines)
- Notes: none

### lemma DirichletCharacter.toContinuousMapZp_changeLevel
- Type: `{m : ℕ} (hmn : m ≤ n) (hdvd : p ^ m ∣ p ^ n) (χ₀ : DirichletCharacter R (p ^ m)) {x : ℤ_[p]} (hx : IsUnit x) : (changeLevel hdvd χ₀).toContinuousMapZp x = χ₀.toContinuousMapZp x`
- What: At a unit `x`, raising the level via `changeLevel` from `p^m` to `p^n` does not change the value of the continuous map; it depends only on the primitive core.
- How: Uses `IsUnit.map` to get a unit reduction, then `changeLevel_eq_cast_of_dvd` to rewrite the level-raised character on the unit, and `PadicInt.cast_toZModPow m n hmn` for compatibility of reductions across levels.
- Hypotheses: `m ≤ n`, `p^m ∣ p^n`, `x` a unit in `ℤ_[p]`.
- Uses from project: [`DirichletCharacter.toContinuousMapZp`, `DirichletCharacter.toContinuousMapZp_apply`]
- Used by: unused in file
- Visibility: public
- Lines: 73-84 (proof ~5 lines)
- Notes: none

### lemma DirichletCharacter.toContinuousMapZp_mul
- Type: `(χ : DirichletCharacter R (p ^ n)) (x y : ℤ_[p]) : χ.toContinuousMapZp (x*y) = χ.toContinuousMapZp x * χ.toContinuousMapZp y`
- What: Multiplicativity of the continuous map (it is a multiplicative character on `ℤ_[p]`).
- How: `simp [map_mul]` — `toZModPow` is a ring hom and `χ` is multiplicative.
- Hypotheses: modulus `p^n` (the skeleton's `1 ≤ n` was dropped as unnecessary).
- Uses from project: [`DirichletCharacter.toContinuousMapZp`]
- Used by: unused in file
- Visibility: public
- Lines: 86-92 (proof 1 line)
- Notes: none

### lemma DirichletCharacter.isLocallyConstant_toContinuousMapZp
- Type: `(χ : DirichletCharacter R (p ^ n)) : IsLocallyConstant (χ.toContinuousMapZp : ℤ_[p] → R)`
- What: The underlying function of the continuous map is locally constant.
- How: Same fiber-decomposition argument as the definition: preimage of `s` is the finite union of `toZModPow`-fibers over `{b : χ b ∈ s}`, each open by `PadicMeasure.isOpen_toZModPow_fiber`, closed under `isOpen_biUnion`.
- Hypotheses: modulus `p^n`. Uses `classical`.
- Uses from project: [`DirichletCharacter.toContinuousMapZp`, `PadicMeasure.isOpen_toZModPow_fiber`]
- Used by: unused in file
- Visibility: public
- Lines: 94-105 (proof ~9 lines)
- Notes: none

### lemma DirichletCharacter.norm_toContinuousMapZp_le
- Type: `{K} [NormedField K] [IsUltrametricDist K] (χ : DirichletCharacter (integerRing K) (p ^ n)) (x : ℤ_[p]) : ‖χ.toContinuousMapZp x‖ ≤ 1`
- What: For a character valued in the integer ring of an ultrametric normed field, all values of the continuous map have norm ≤ 1.
- How: Immediate from ball-valuedness — the value lives in `integerRing K` whose `.2` field is exactly the `‖·‖ ≤ 1` proof.
- Hypotheses: `K` ultrametric normed field; `χ` valued in `integerRing K`.
- Uses from project: [`DirichletCharacter.toContinuousMapZp`]
- Used by: unused in file
- Visibility: public
- Lines: 107-114 (proof 1 line)
- Notes: none

### theorem gaussSum_mul_gaussSum_inv
- Type: `{χ : DirichletCharacter R N} (hχ : χ.IsPrimitive) {e : AddChar (ZMod N) R} (he : e.IsPrimitive) : gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = (N : R)` (R a domain)
- What: L5.1.5 — for a primitive character `χ` mod `N` and a primitive additive character `e` into a domain, `G(χ,e)·G(χ⁻¹,e⁻¹) = N` (Rem 5.3(i) at general/non-prime level; mathlib has only the prime/field case).
- How: `calc` over four finite sums: expand `G(χ⁻¹,e⁻¹)`, rewrite each summand via `gaussSum_mulShift_of_isPrimitive`, swap the two sums (`Finset.sum_comm`), then collapse the inner sum using primitive-character orthogonality `AddChar.sum_mulShift _ he` (`∑_b e(b·c) = N·δ_{c,0}`); final `Finset.sum_ite_eq'` and `ZMod.card`.
- Hypotheses: `N ≠ 0`; `R` a commutative domain; `χ` primitive; `e` a primitive additive character.
- Uses from project: []
- Used by: `norm_gaussSum_eq_one`
- Visibility: public
- Lines: 132-162 (proof ~27 lines)
- Notes: none

### lemma norm_eq_one_of_pow_eq_one
- Type: `{x : L} {m : ℕ} (h : x ^ m = 1) (hm : m ≠ 0) : ‖x‖ = 1` (L a normed field)
- What: Any root of unity in a normed field has norm exactly one (analogue of `Complex.norm_eq_one_of_pow_eq_one`).
- How: From `‖x‖^m = ‖x^m‖ = ‖1‖ = 1`, conclude `‖x‖ = 1` by `le_antisymm` of `pow_le_one_iff_of_nonneg` and `one_le_pow_iff_of_nonneg`.
- Hypotheses: `x^m = 1` with `m ≠ 0`; `L` a normed field (omits `Fact p.Prime`, `IsUltrametricDist`, `CompleteSpace`).
- Uses from project: []
- Used by: `norm_gaussSum_eq_one`
- Visibility: public
- Lines: 175-179 (proof ~4 lines)
- Notes: none

### theorem norm_gaussSum_eq_one
- Type: `{D : ℕ} [NeZero D] {η : DirichletCharacter L D} (hη : η.IsPrimitive) (hD : ¬(p:ℕ) ∣ D) {ζ : L} (hζ : IsPrimitiveRoot ζ D) : ‖gaussSum η (AddChar.zmodChar D hζ.pow_eq_one)‖ = 1`
- What: For `η` primitive of conductor `D` coprime to `p` and `ζ` a primitive `D`-th root of unity in `L`, the Gauss sum has norm one (hence is a unit of the integer ring).
- How: Local `hval` shows any Gauss sum of a `D`-torsion pair has norm ≤ 1 via `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty` plus `norm_eq_one_of_pow_eq_one` (character values are roots of unity, using `ZMod.pow_totient`). Then `gaussSum_mul_gaussSum_inv hη` gives `‖G(η)‖·‖G(η⁻¹)‖ = ‖D‖ = 1` (via `Padic.norm_natCast_eq_one_iff` + coprimality `Nat.Prime.coprime_iff_not_dvd`), and `nlinarith` forces both factors to equal 1. Torsion of `e`, `e⁻¹` from `AddChar.map_nsmul_eq_pow`.
- Hypotheses: `D ≠ 0`; `η` primitive mod `D`; `p ∤ D`; `ζ` primitive `D`-th root of unity; `L` a complete ultrametric normed `ℚ_[p]`-algebra (CompleteSpace omitted).
- Uses from project: [`gaussSum_mul_gaussSum_inv`]
- Used by: unused in file
- Visibility: public
- Lines: 190-233 (proof ~39 lines)
- Notes: long(30-50) — proof ~39 lines (between 30 and 50).

### lemma DirichletCharacter.factorsThrough_ringHomComp_iff
- Type: `{R S} [CommRing R] [CommRing S] {N} [NeZero N] (χ : DirichletCharacter R N) {f : R →+* S} (hf : Function.Injective f) {d : ℕ} : FactorsThrough (χ.ringHomComp f) d ↔ χ.FactorsThrough d`
- What: Composing with an injective ring hom `f` does not change which levels `d` a Dirichlet character factors through.
- How: Case split on `d ∣ N`. In the divisible case, both sides rewritten via `factorsThrough_iff_ker_unitsMap`; a helper `hker` shows `(χ.ringHomComp f).toUnitHom x = 1 ↔ χ.toUnitHom x = 1` using injectivity of `f` and `MulChar.ringHomComp_apply`; kernels then match. The non-divisible case is vacuous via `FactorsThrough.dvd`.
- Hypotheses: `R`, `S` commutative rings; `N ≠ 0`; `f` injective ring hom.
- Uses from project: []
- Used by: `DirichletCharacter.isPrimitive_ringHomComp_iff`
- Visibility: public (`_root_.DirichletCharacter`)
- Lines: 242-258 (proof ~14 lines)
- Notes: none

### lemma DirichletCharacter.isPrimitive_ringHomComp_iff
- Type: `{R S} [CommRing R] [CommRing S] {N} [NeZero N] (χ : DirichletCharacter R N) {f : R →+* S} (hf : Function.Injective f) : IsPrimitive (χ.ringHomComp f) ↔ χ.IsPrimitive`
- What: Primitivity of a Dirichlet character is preserved/reflected by composition with an injective coefficient homomorphism.
- How: Unfolds `IsPrimitive`/`conductor`; shows the two conductor-sets coincide by `Set.ext` applied pointwise through `factorsThrough_ringHomComp_iff`, so the conductors (and primitivity) agree.
- Hypotheses: same as above.
- Uses from project: [`DirichletCharacter.factorsThrough_ringHomComp_iff`]
- Used by: unused in file
- Visibility: public (`_root_.DirichletCharacter`)
- Lines: 262-268 (proof ~3 lines)
- Notes: none

---

## File Summary

- Total decls: 11 (1 def / 9 lemmas+theorems / 0 instances)
  - defs: `DirichletCharacter.toContinuousMapZp`
  - lemmas/theorems: `toContinuousMapZp_apply`, `toContinuousMapZp_eq_zero`, `toContinuousMapZp_changeLevel`, `toContinuousMapZp_mul`, `isLocallyConstant_toContinuousMapZp`, `norm_toContinuousMapZp_le`, `gaussSum_mul_gaussSum_inv`, `norm_eq_one_of_pow_eq_one`, `norm_gaussSum_eq_one`, `factorsThrough_ringHomComp_iff`, `isPrimitive_ringHomComp_iff`
  - instances: none
- Key API (used by ≥3 in-file): `DirichletCharacter.toContinuousMapZp` (used by 6 in-file decls). No other decl reaches 3 in-file consumers.
- Unused in file (no in-file consumer): `toContinuousMapZp_eq_zero`, `toContinuousMapZp_changeLevel`, `toContinuousMapZp_mul`, `isLocallyConstant_toContinuousMapZp`, `norm_toContinuousMapZp_le`, `norm_gaussSum_eq_one`, `isPrimitive_ringHomComp_iff` (these are public API consumed by other files in the project).
- Decls with `sorry`: none.
- `set_option`: none. (Three `omit` instance-discharges on `norm_eq_one_of_pow_eq_one` / `norm_gaussSum_eq_one`; `open Classical in` on the def.)
- Proofs >50 lines (OVER-50): none (count: 0).
- Proofs 30-50 lines: 1 — `norm_gaussSum_eq_one` (~39 lines).

Project deps referenced: `PadicMeasure.isOpen_toZModPow_fiber` (from `Measure.Basic`); all other dependencies are mathlib (`DirichletCharacter.*`, `gaussSum*`, `AddChar.*`, `PadicInt.*`, `ZMod.*`, `Padic.*`).
