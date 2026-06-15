# Inventory: ./HasseWeil/FormalGroup/CharP.lean

**File**: `HasseWeil/FormalGroup/CharP.lean`
**Module**: Multiplication by p in characteristic p (Silverman IV.4.4)
**Imports**: `HasseWeil.FormalGroup.MulByNat`, `HasseWeil.FormalGroup.InvariantDiff`,
  `Mathlib.RingTheory.PowerSeries.Expand`, `Mathlib.Algebra.CharP.Invertible`
**Namespace**: `HasseWeil.FormalGroup`
**Total declarations**: 4 (2 private, 2 public)

---

### `private theorem exists_expand_of_coeff_vanishing`

- **Type**: `(p : ℕ) (hp : p ≠ 0) (f : PowerSeries R) (h : ∀ n, ¬ p ∣ n → PowerSeries.coeff n f = 0) : ∃ g : PowerSeries R, f = g.expand p hp`
- **What**: If every coefficient of a power series `f` at an index not divisible by `p` is zero, then `f` factors through `PowerSeries.expand p hp`; i.e., `f = g(T^p)` for some `g`.
- **How**: Constructs `g` explicitly as `PowerSeries.mk (fun m => coeff (p * m) f)`, then uses `PowerSeries.coeff_expand` and `Nat.mul_div_cancel_left` to verify coefficient equality. The `split_ifs` handles the divisibility case.
- **Hypotheses**: `p ≠ 0`; `R` is a commutative ring; every coefficient of `f` at non-`p`-multiple indices vanishes.
- **Uses from project**: none
- **Used by**: `FormalGroup.mulByP_exists_expand` (within this file)
- **Visibility**: private
- **Lines**: 44–53, proof length ~8 lines
- **Notes**: Pure combinatorial lemma; likely matches a mathlib lemma in `PowerSeries.Expand` (possible duplication with `PowerSeries.expand_eq_iff` or similar).

---

### `private theorem coeff_eq_zero_of_derivative_eq_zero_charP`

- **Type**: `{p : ℕ} [Fact p.Prime] [CharP R p] {f : PowerSeries R} (hf : PowerSeries.derivative R f = 0) (n : ℕ) (hpn : ¬ p ∣ n) : PowerSeries.coeff n f = 0`
- **What**: Over a ring of prime characteristic `p`, if the formal derivative of a power series is zero, then every coefficient at an index not divisible by `p` vanishes.
- **How**: Writes `n = m + 1` (using `Nat.exists_eq_succ_of_ne_zero`), extracts `coeff (m+1) f * (m+1 : R) = 0` from `hf` via `PowerSeries.coeff_derivative`, then uses `CharP.isUnit_natCast_iff` to conclude `(m+1 : R)` is a unit (since `p ∤ m+1`), forcing `coeff (m+1) f = 0` via `IsUnit.mul_left_eq_zero`.
- **Hypotheses**: `p` is a prime, `R` has characteristic `p`, formal derivative of `f` is zero, `p` does not divide `n`.
- **Uses from project**: none (only mathlib: `CharP.isUnit_natCast_iff`, `PowerSeries.coeff_derivative`)
- **Used by**: `FormalGroup.mulByP_exists_expand` (within this file)
- **Visibility**: private
- **Lines**: 57–75, proof length ~16 lines
- **Notes**: No `set_option maxHeartbeats`. The key mathlib lemma is `CharP.isUnit_natCast_iff`.

---

### `private lemma constantCoeff_subst_zero_const`

- **Type**: `(g : PowerSeries R) (hg : PowerSeries.constantCoeff g = 0) (f : PowerSeries R) : PowerSeries.constantCoeff (PowerSeries.subst g f) = PowerSeries.constantCoeff f`
- **What**: The constant coefficient of `subst g f` equals the constant coefficient of `f`, provided the constant coefficient of the substitution variable `g` is zero.
- **How**: Rewrites via `PowerSeries.subst_def` to reduce to the `MvPowerSeries` setting, constructs `HasSubst` using `MvPowerSeries.hasSubst_of_constantCoeff_zero`, then applies the project lemma `HasseWeil.FG.constantCoeff_subst_vanishing` (from `HasseWeil.FormalGroup.Definition`).
- **Hypotheses**: `R` is a commutative ring; `g` has zero constant coefficient.
- **Uses from project**: `HasseWeil.FG.constantCoeff_subst_vanishing` (from `HasseWeil.FormalGroup.Definition`)
- **Used by**: `FormalGroup.mulByP_exists_expand` (within this file)
- **Visibility**: private
- **Lines**: 79–86, proof length ~5 lines
- **Notes**: Thin wrapper around `HasseWeil.FG.constantCoeff_subst_vanishing` specialized to the univariate `PowerSeries` case. The `MvPowerSeries.hasSubst_of_constantCoeff_zero` construction is the non-trivial step.

---

### `theorem FormalGroup.mulByP_exists_expand`

- **Type**: `(F : FormalGroup R) (p : ℕ) [hp_prime : Fact p.Prime] [CharP R p] : ∃ g : PowerSeries R, (F.mulByNatHom p).toSeries = g.expand p hp_prime.out.ne_zero`
- **What**: **Silverman IV.4.4**: For a formal group `F` over a ring of prime characteristic `p`, the multiplication-by-`p` series `[p](T)` is a power series in `T^p`; i.e., `[p](T) = g(T^p)` for some `g`.
- **How**: 
  1. Uses `FormalGroupHom.invariantDifferential_chain` (chain rule for invariant differentials) to get `subst [p] ω_F · [p]'(T) = (p:R) · ω_F`.
  2. `CharP.cast_eq_zero` gives `(p:R) = 0`, so RHS = 0.
  3. `constantCoeff_subst_zero_const` and `F.invariantDiff_constantCoeff` show `subst [p] ω_F` has constant coefficient 1, hence is a unit (`PowerSeries.isUnit_iff_constantCoeff`).
  4. `IsUnit.mul_right_eq_zero` then gives `[p]'(T) = 0`.
  5. Applies `coeff_eq_zero_of_derivative_eq_zero_charP` then `exists_expand_of_coeff_vanishing`.
- **Hypotheses**: `p` is a prime, `R` has characteristic `p`, `F` is a formal group over `R`.
- **Uses from project**: 
  - `exists_expand_of_coeff_vanishing` (this file)
  - `coeff_eq_zero_of_derivative_eq_zero_charP` (this file)
  - `constantCoeff_subst_zero_const` (this file)
  - `FormalGroupHom.invariantDifferential_chain` (from `HasseWeil.FormalGroup.InvariantDiff`)
  - `FormalGroup.coeff_one_mulByNatHom` (from `HasseWeil.FormalGroup.MulByNat`)
  - `FormalGroupHom.zero_const` (from `HasseWeil.FormalGroup.MulByNat` or similar)
  - `FormalGroup.normalizedDifferential` (from `HasseWeil.FormalGroup.InvariantDiff`)
  - `FormalGroup.invariantDiff_constantCoeff` (from `HasseWeil.FormalGroup.InvariantDiff`)
  - `FormalGroup.invariantDiff` (from `HasseWeil.FormalGroup.InvariantDiff`)
- **Used by**: `FormalGroup.mulByP_decomposition` (within this file); no other callers found in the project
- **Visibility**: public
- **Lines**: 95–122, proof length ~25 lines
- **Notes**: Main result of the file. Proof is clean, no `sorry`, no `set_option maxHeartbeats`.

---

### `theorem FormalGroup.mulByP_decomposition`

- **Type**: `(F : FormalGroup R) (p : ℕ) [hp_prime : Fact p.Prime] [CharP R p] : ∃ f g : PowerSeries R, (F.mulByNatHom p).toSeries = PowerSeries.C (p : R) * f + g.expand p hp_prime.out.ne_zero`
- **What**: **Silverman IV.4.4 (decomposition form)**: In characteristic `p`, `[p](T) = p·f(T) + g(T^p)`; in characteristic `p` the term `p·f` vanishes, so this is a trivial corollary of `mulByP_exists_expand` (taking `f = 0`).
- **How**: Calls `mulByP_exists_expand` to get the `g`, then takes `f = 0`, simplifies `C p * 0 = 0` and `0 + expand g = expand g`.
- **Hypotheses**: `p` is a prime, `R` has characteristic `p`, `F` is a formal group over `R`.
- **Uses from project**: `FormalGroup.mulByP_exists_expand` (this file)
- **Used by**: no callers found in the project (dead-code candidate)
- **Visibility**: public
- **Lines**: 130–141, proof length ~9 lines
- **Notes**: Mirrors the Silverman statement but is mathematically weaker than `mulByP_exists_expand` (takes `f=0`); serves as a Silverman-shaped interface. Likely unused in the project currently.
