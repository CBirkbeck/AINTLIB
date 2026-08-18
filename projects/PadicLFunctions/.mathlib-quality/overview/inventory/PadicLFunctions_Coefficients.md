# Inventory: PadicLFunctions/Coefficients.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/Coefficients.lean`

Namespace context: `PadicLFunctions`, with section variables
`(p : ℕ) [hp : Fact p.Prime]`, `(L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`.

---

### def integerRing
- Type: `def integerRing : Subring L` (carrier `{x : L | ‖x‖ ≤ 1}`).
- What: The integer ring of a nonarchimedean normed field `L`, defined as the norm-unit ball `{x | ‖x‖ ≤ 1}` packaged as a subring; for a finite extension `L/ℚ_p` this is the ring of integers `𝒪_L`.
- How: Verifies the four subring closure axioms directly from the norm: multiplicativity via `mul_le_one₀`, additive closure via the ultrametric inequality `IsUltrametricDist.norm_add_le_max` combined with `max_le`, and `one_mem`/`zero_mem`/`neg_mem` by `simp`.
- Hypotheses: `L` a normed field with ultrametric distance (the `NormedAlgebra ℚ_[p] L` and `CompleteSpace L` from the section variables are present but only the norm/ultrametric structure is used).
- Uses from project: []
- Used by: `integerRing.instIsUltrametricDist`, `integerRing.instCompleteSpace`, `integerRing.instAlgebraPadicInt`, `ballIdeal`, `integerRing.instIsLinearTopology`, `norm_algebraMap_eq`, `isometry_algebraMap`, `integerRing.instIsBoundedSMul`, `integerRing.not_isUnit_of_norm_lt_one`, `integerRing.isUnit_of_norm_eq_one` (the whole `integerRing` namespace API).
- Visibility: public
- Lines: 39–47 (def body ~6 lines, no separate proof).
- Notes: none.

### instance integerRing.instIsUltrametricDist (anonymous)
- Type: `instance : IsUltrametricDist (integerRing L)`.
- What: The subtype `integerRing L` inherits an ultrametric distance from the ambient field `L`.
- How: Supplies the strong triangle inequality by transporting `IsUltrametricDist.dist_triangle_max` along the subtype distance equation `Subtype.dist_eq` via `simpa`.
- Hypotheses: `L` ultrametric.
- Uses from project: [`integerRing`]
- Used by: unused in file (instance, resolved by typeclass search).
- Visibility: public
- Lines: 51–52 (proof ~1 line).
- Notes: none.

### instance integerRing.instCompleteSpace (anonymous)
- Type: `instance : CompleteSpace (integerRing L)`.
- What: The integer ring is a complete metric space.
- How: Uses `completeSpace_coe_iff_isComplete` to reduce to completeness of the carrier set, then shows the unit ball is closed via `IsClosed.isComplete` and `isClosed_le` (the norm is continuous, `fun_prop`), using that a closed subset of a complete space is complete.
- Hypotheses: `L` complete (`CompleteSpace L`).
- Uses from project: [`integerRing`]
- Used by: unused in file (instance).
- Visibility: public
- Lines: 54–57 (proof ~4 lines).
- Notes: none.

### instance integerRing.instAlgebraPadicInt (anonymous)
- Type: `noncomputable instance : Algebra ℤ_[p] (integerRing L)`.
- What: Gives `integerRing L` the structure of a `ℤ_[p]`-algebra, via the embedding `ℤ_[p] → ℚ_[p] → L` corestricted to the unit ball.
- How: Builds a `RingHom` by composing `algebraMap ℚ_[p] L` with `PadicInt.Coe.ringHom`, then `codRestrict`s into `integerRing L`, the membership obligation `‖algebraMap ℚ_[p] L x‖ ≤ 1` discharged by `norm_algebraMap'` and `x.norm_le_one`.
- Hypotheses: `L` a normed `ℚ_[p]`-algebra.
- Uses from project: [`integerRing`]
- Used by: `norm_algebraMap_eq`, `isometry_algebraMap`, `integerRing.instIsBoundedSMul` (they reference `algebraMap ℤ_[p] (integerRing L)`).
- Visibility: public
- Lines: 59–63 (proof ~3 lines).
- Notes: none.

### def integerRing.ballIdeal
- Type: `noncomputable def ballIdeal (ε : ℝ) : Ideal (integerRing L)` (carrier `{x | ‖(x:L)‖ ≤ max ε 0}`).
- What: The closed ball of radius `ε` (clamped to be nonnegative as `max ε 0`) inside the integer ring, packaged as an ideal.
- How: Checks the ideal axioms from the norm: additive closure via the ultrametric `IsUltrametricDist.norm_add_le_max` plus `max_le`, and absorption `smul_mem'` via `norm_mul` and `mul_le_mul` using that the scalar `r` has norm `≤ 1` (it lies in the unit ball).
- Hypotheses: `L` ultrametric normed field; `ε : ℝ` arbitrary.
- Uses from project: [`integerRing`]
- Used by: `integerRing.instIsLinearTopology`.
- Visibility: public
- Lines: 65–75 (def body ~7 lines).
- Notes: none.

### instance integerRing.instIsLinearTopology (anonymous)
- Type: `instance : IsLinearTopology (integerRing L) (integerRing L)`.
- What: The norm topology on the integer ring is linear, i.e. has a neighbourhood basis at `0` consisting of (the open/closed balls which are) ideals; needed for `PowerSeries.eval₂`-substitution into `(integerRing L)⟦T⟧`.
- How: Applies `IsLinearTopology.mk_of_hasBasis'` with the family of ideals `ballIdeal L ε` (`0 < ε`), then identifies them with the metric closed-ball basis `Metric.nhds_basis_closedBall` via `Filter.HasBasis.congr` and an `ext`/`simp` unfolding of `ballIdeal`, `Metric.mem_closedBall`, `dist_zero_right`, `max_eq_left`.
- Hypotheses: `L` ultrametric normed field with multiplicative norm.
- Uses from project: [`integerRing`, `ballIdeal`]
- Used by: unused in file (instance).
- Visibility: public
- Lines: 77–88 (proof ~9 lines).
- Notes: none.

### lemma integerRing.norm_algebraMap_eq
- Type: `lemma norm_algebraMap_eq (x : ℤ_[p]) : ‖algebraMap ℤ_[p] (integerRing L) x‖ = ‖x‖`.
- What: The algebra map `ℤ_[p] → integerRing L` preserves norms (it is the restriction of the isometric scalar embedding `ℚ_[p] → L`).
- How: Unfolds the algebra map to `algebraMap ℚ_[p] L (x : ℚ_[p])` (definitionally), then rewrites with `norm_algebraMap'` (norm of scalar image) and `PadicInt.norm_def` (the `ℤ_[p]`-norm is the `ℚ_[p]`-norm of the coercion).
- Hypotheses: `L` a normed `ℚ_[p]`-algebra (`CompleteSpace` omitted).
- Uses from project: [`integerRing`, `integerRing.instAlgebraPadicInt`]
- Used by: `isometry_algebraMap`, `integerRing.instIsBoundedSMul`.
- Visibility: public
- Lines: 90–96 (proof ~2 lines); preceded by `omit [CompleteSpace L]`.
- Notes: none.

### lemma integerRing.isometry_algebraMap
- Type: `lemma isometry_algebraMap : Isometry (algebraMap ℤ_[p] (integerRing L))`.
- What: The algebra map `ℤ_[p] → integerRing L` is an isometry.
- How: Promotes the norm-preservation lemma `norm_algebraMap_eq` to an isometry via `AddMonoidHomClass.isometry_of_norm`.
- Hypotheses: `L` a normed `ℚ_[p]`-algebra (`CompleteSpace` omitted).
- Uses from project: [`integerRing`, `integerRing.instAlgebraPadicInt`, `norm_algebraMap_eq`]
- Used by: unused in file.
- Visibility: public
- Lines: 98–100 (proof ~1 line); preceded by `omit [CompleteSpace L]`.
- Notes: none.

### instance integerRing.instIsBoundedSMul (anonymous)
- Type: `instance : IsBoundedSMul ℤ_[p] (integerRing L)`.
- What: Scalar multiplication of `ℤ_[p]` on `integerRing L` is bounded (norm-submultiplicative).
- How: Uses `IsBoundedSMul.of_norm_smul_le`, rewriting the scalar action as multiplication via `Algebra.smul_def`, then bounding by `norm_mul_le` and the isometry equation `norm_algebraMap_eq`.
- Hypotheses: `L` a normed `ℚ_[p]`-algebra (`CompleteSpace` omitted).
- Uses from project: [`integerRing`, `integerRing.instAlgebraPadicInt`, `norm_algebraMap_eq`]
- Used by: unused in file (instance).
- Visibility: public
- Lines: 102–106 (proof ~3 lines); preceded by `omit [CompleteSpace L]`.
- Notes: none.

### lemma charZero_of_qpAlgebra
- Type: `lemma charZero_of_qpAlgebra (q : ℕ) [Fact q.Prime] {M : Type*} [NormedField M] [NormedAlgebra ℚ_[q] M] : CharZero M`.
- What: Any normed `ℚ_[q]`-algebra field has characteristic zero.
- How: Applies `charZero_of_injective_algebraMap` to the injective algebra map `algebraMap ℚ_[q] M` (injective because `ℚ_[q]` has characteristic zero and `M` is a field/domain receiving it).
- Hypotheses: `q` prime, `M` a normed `ℚ_[q]`-algebra field. (Stated with its own prime `q`/algebra `M` rather than the section `p`/`L`, deliberately not an instance since `p` is not determined by the goal.)
- Uses from project: []
- Used by: unused in file.
- Visibility: public
- Lines: 112–116 (proof ~1 line). (Declared under `variable {p L}`.)
- Notes: none.

### theorem integerRing.not_isUnit_of_norm_lt_one
- Type: `theorem integerRing.not_isUnit_of_norm_lt_one {x : integerRing L} (hx : ‖(x:L)‖ < 1) : ¬ IsUnit x`.
- What: An element of the integer ring with norm strictly less than one is not a unit.
- How: From a hypothetical right inverse `y` (`IsUnit.exists_right_inv`) deduces `(x:L)*(y:L)=1`, hence `‖x‖·‖y‖=1` (via `norm_mul`, `norm_one`); contradiction by `nlinarith` using `‖x‖<1`, `‖y‖≤1` (`y.2`) so the product is `<1`.
- Hypotheses: `L` ultrametric normed field (`NormedAlgebra` and `CompleteSpace` omitted); `‖x‖ < 1`.
- Uses from project: [`integerRing`]
- Used by: unused in file.
- Visibility: public
- Lines: 118–125 (proof ~5 lines); preceded by `omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L]`.
- Notes: none.

### theorem integerRing.isUnit_of_norm_eq_one
- Type: `theorem integerRing.isUnit_of_norm_eq_one {x : integerRing L} (hx : ‖(x:L)‖ = 1) : IsUnit x`.
- What: An element of the integer ring with norm exactly one is a unit, since its field inverse also has norm one and hence lies in the integer ring.
- How: Notes `x ≠ 0` (norm one), then exhibits the inverse `(x:L)⁻¹` with norm `‖x⁻¹‖ = 1 ≤ 1` (`norm_inv`, `inv_one`) as an integer-ring element, and applies `IsUnit.of_mul_eq_one` with `mul_inv_cancel₀` (lifted via `Subtype.ext`).
- Hypotheses: `L` ultrametric normed field (`NormedAlgebra` and `CompleteSpace` omitted); `‖x‖ = 1`.
- Uses from project: [`integerRing`]
- Used by: unused in file.
- Visibility: public
- Lines: 127–135 (proof ~5 lines); preceded by `omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L]`.
- Notes: none.

### theorem norm_natCast_self_lt_one
- Type: `theorem norm_natCast_self_lt_one : ‖((p : ℕ) : L)‖ < 1`.
- What: In a normed `ℚ_[p]`-algebra, the image of the prime `p` (as a natural number cast into `L`) has norm `‖p‖ = p⁻¹ < 1`.
- How: Rewrites `(p : L)` as `algebraMap ℚ_[p] L ((p:ℕ):ℚ_[p])` (via `map_natCast`) and `norm_algebraMap'`, reducing to `Padic.norm_p_lt_one`.
- Hypotheses: `L` a normed `ℚ_[p]`-algebra (`IsUltrametricDist` and `CompleteSpace` omitted).
- Uses from project: []
- Used by: `IsPrimitiveRoot.norm_sub_one_lt`.
- Visibility: public
- Lines: 137–143 (proof ~3 lines); preceded by `omit [IsUltrametricDist L] [CompleteSpace L]`.
- Notes: none.

### theorem IsPrimitiveRoot.norm_sub_one_lt
- Type: `theorem _root_.IsPrimitiveRoot.norm_sub_one_lt {ζ : L} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ n)) : ‖ζ - 1‖ < 1`.
- What: W2 — a primitive `p^n`-th root of unity `ζ` in `L` satisfies `‖ζ − 1‖ < 1`; consequently `ζ − 1` is topologically nilpotent and `x ↦ ζ^x` extends to a continuous additive character of `ℤ_[p]`.
- How: Case `n = 0` gives `ζ = 1` trivially (`IsPrimitiveRoot.one_right_iff`). For `n > 0`, by contradiction assume `‖x‖ ≥ 1` where `x = ζ − 1`; expand `1 = ζ^N = (x+1)^N` via `add_pow` and peel the `k=0` term (`Finset.sum_range_succ'`) to get `∑ x^(k+1)·C(N,k+1) = 0`, isolate the top term `x^N` (`Finset.sum_range_succ`, `Nat.choose_self`), bound the sum by a single dominant term using the ultrametric `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty`, use that each lower binomial coefficient is divisible by `p` (`Nat.Prime.dvd_choose_pow`, so its norm `≤ ‖p‖`), and assemble `‖x‖^N ≤ ‖p‖·‖x‖^N < ‖x‖^N` to force `1 ≤ ‖p‖`, contradicting `norm_natCast_self_lt_one`.
- Hypotheses: `L` ultrametric normed `ℚ_[p]`-algebra (`CompleteSpace` omitted); `ζ` a primitive `p^n`-th root of unity.
- Uses from project: [`norm_natCast_self_lt_one`]
- Used by: `IsPrimitiveRoot.tendsto_pow_sub_one`.
- Visibility: public (`_root_` namespace — extends `IsPrimitiveRoot`).
- Lines: 145–200 (proof ~48 lines); preceded by `omit [CompleteSpace L]`.
- Notes: long(30-50) — proof body ≈48 lines; candidate for `/decompose-proof`. No sorry/TODO/set_option.

### theorem IsPrimitiveRoot.tendsto_pow_sub_one
- Type: `theorem _root_.IsPrimitiveRoot.tendsto_pow_sub_one {ζ : L} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ n)) : Tendsto ((ζ - 1) ^ ·) atTop (𝓝 0)`.
- What: W2' — the powers of `ζ − 1` (for `ζ` a primitive `p^n`-th root) tend to `0`, i.e. `ζ − 1` is topologically nilpotent.
- How: Immediate from `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` applied to the bound `‖ζ−1‖ < 1` supplied by `IsPrimitiveRoot.norm_sub_one_lt`.
- Hypotheses: `L` ultrametric normed `ℚ_[p]`-algebra (`CompleteSpace` omitted); `ζ` a primitive `p^n`-th root of unity.
- Uses from project: [`IsPrimitiveRoot.norm_sub_one_lt`]
- Used by: unused in file.
- Visibility: public (`_root_`).
- Lines: 202–207 (proof ~1 line); preceded by `omit [CompleteSpace L]`.
- Notes: none.

### theorem norm_natCast_eq_one_of_not_dvd
- Type: `theorem norm_natCast_eq_one_of_not_dvd {D : ℕ} (hD : ¬ (p:ℕ) ∣ D) : ‖(D : L)‖ = 1`.
- What: In a normed `ℚ_[p]`-algebra, a natural number `D` not divisible by `p` has norm one in `L`; this bridges the abstract norm-one hypothesis of W3 back to the `p ∤ D` condition used in §5.
- How: Rewrites `(D:L)` as `algebraMap ℚ_[p] L ((D:ℕ):ℚ_[p])` (via `map_natCast`, `norm_algebraMap'`) and uses `Padic.norm_natCast_eq_one_iff` together with `Nat.Prime.coprime_iff_not_dvd` to convert `p ∤ D` into the coprimality giving norm one.
- Hypotheses: `L` a normed `ℚ_[p]`-algebra (`IsUltrametricDist` and `CompleteSpace` omitted); `p ∤ D`.
- Uses from project: []
- Used by: unused in file (intended caller is W3 `IsPrimitiveRoot.norm_pow_sub_one_eq_one` via its `‖(D:L)‖ = 1` hypothesis, but not referenced directly here).
- Visibility: public
- Lines: 209–218 (proof ~3 lines); preceded by `omit [IsUltrametricDist L] [CompleteSpace L]`.
- Notes: none.

### theorem IsPrimitiveRoot.norm_pow_sub_one_eq_one
- Type: `theorem _root_.IsPrimitiveRoot.norm_pow_sub_one_eq_one {ζ : L} {D : ℕ} (hζ : IsPrimitiveRoot ζ D) (hD : ‖(D : L)‖ = 1) {c : ℕ} (hc : ¬ D ∣ c) : ‖ζ ^ c - 1‖ = 1`.
- What: W3 — for `ζ` a primitive `D`-th root of unity with `‖(D:L)‖ = 1` and `D ∤ c`, the element `ζ^c − 1` has norm exactly one (hence is a unit of the integer ring).
- How: Writes `D = n+1`; shows `‖ζ‖ = 1` (`pow_eq_one_iff_of_nonneg` + `hζ.pow_eq_one`), each factor `‖1 − ζ^(k+1)‖ ≤ 1` (ultrametric `norm_add_le_max`), and that the product over `range n` of these factors equals `D` in norm via `IsPrimitiveRoot.prod_one_sub_pow_eq_order` (with `hD`); since a product of norm-`≤1` factors equals one, each factor has norm exactly one (`Finset.mul_prod_erase` + `nlinarith` with `Finset.prod_le_one`/`Finset.prod_nonneg`); finally reduces the exponent `c` mod `D` (`Nat.div_add_mod`, `hζ.pow_eq_one`), notes `c % D ≠ 0` (from `D ∤ c`), and reads off the corresponding factor's norm after `neg_sub`.
- Hypotheses: `L` ultrametric normed field (`NormedAlgebra` and `CompleteSpace` omitted); `ζ` a primitive `D`-th root of unity; `‖(D:L)‖ = 1`; `D ∤ c`.
- Uses from project: []
- Used by: unused in file.
- Visibility: public (`_root_`).
- Lines: 220–266 (proof ~35 lines); preceded by `omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L]`.
- Notes: long(30-50) — proof body ≈35 lines; candidate for `/decompose-proof`. No sorry/TODO/set_option.

---

## File Summary

- Total declarations: 16 — defs 2 (`integerRing`, `ballIdeal`) / lemmas+theorems 9 (`norm_algebraMap_eq`, `isometry_algebraMap`, `charZero_of_qpAlgebra`, `integerRing.not_isUnit_of_norm_lt_one`, `integerRing.isUnit_of_norm_eq_one`, `norm_natCast_self_lt_one`, `IsPrimitiveRoot.norm_sub_one_lt`, `IsPrimitiveRoot.tendsto_pow_sub_one`, `norm_natCast_eq_one_of_not_dvd`, `IsPrimitiveRoot.norm_pow_sub_one_eq_one` — note: 10 listed, see count below) / instances 5 (IsUltrametricDist, CompleteSpace, Algebra ℤ_[p], IsLinearTopology, IsBoundedSMul). Precisely: 2 defs + 10 lemma/theorem + 5 instances = 17 declarations (the `integerRing` Subring def counts once; the 5 anonymous instances + 10 named lemma/theorems + 2 named defs).
- Key API (used by ≥3 in file): `integerRing` (used by all ~10 namespace decls); `integerRing.instAlgebraPadicInt` (used by 3: `norm_algebraMap_eq`, `isometry_algebraMap`, `instIsBoundedSMul`); `norm_algebraMap_eq` (used by 3: `isometry_algebraMap`, `instIsBoundedSMul`, and underlies the algebra instance API). No other decl reaches 3 in-file uses.
- Unused in file (no in-file consumer; these are the file's exported API): the 5 instances (`IsUltrametricDist`, `CompleteSpace`, `Algebra ℤ_[p]` is used, `IsLinearTopology`, `IsBoundedSMul`), `isometry_algebraMap`, `charZero_of_qpAlgebra`, `integerRing.not_isUnit_of_norm_lt_one`, `integerRing.isUnit_of_norm_eq_one`, `IsPrimitiveRoot.tendsto_pow_sub_one`, `norm_natCast_eq_one_of_not_dvd`, `IsPrimitiveRoot.norm_pow_sub_one_eq_one`.
- Declarations with sorry: none.
- set_option: none.
- Proofs >50 lines (OVER-50): none (count 0).
- Proofs 30–50 lines: 2 — `IsPrimitiveRoot.norm_sub_one_lt` (≈48 lines, 145–200), `IsPrimitiveRoot.norm_pow_sub_one_eq_one` (≈35 lines, 220–266). Both flagged long(30-50), candidates for `/decompose-proof`.
- omit usage: many decls use `omit [...]` to drop unused section instances (`CompleteSpace L`, `IsUltrametricDist L`, `NormedAlgebra ℚ_[p] L`) — relevant for generality auditing.
