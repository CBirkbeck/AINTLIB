# Inventory: `LutzNagell/LutzNagellTheorem/PIDDenominators.lean`

File path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDDenominators.lean`

Namespace: `LutzNagell.PID`

Module variables (in scope for all decls): `{R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]`, `{K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]`.

Imports: `LutzNagell.LutzNagellTheorem.PIDCurve`, `Mathlib.RingTheory.Localization.NumDen`.

---

### lemma not_dvd_sum_of_not_dvd_cube
- Type: `{q α : R} (hq : Prime q) (hpa : ¬ q ∣ α) (c₂ c₄ c₆ : R) : ¬ q ∣ (α ^ 3 + c₂ * α ^ 2 * q + c₄ * α * q ^ 2 + c₆ * q ^ 3)`
- What: For a prime `q` not dividing `α`, `q` does not divide the value `α³ + c₂α²q + c₄αq² + c₆q³` (a "leading cube plus a `q`-multiple tail").
- How: Assume `q` divides the whole; the tail `c₂α²q + c₄αq² + c₆q³` is visibly a multiple of `q` (witness `c₂α² + c₄αq + c₆q²`), so `q ∣ α³` by subtracting the two divisibility witnesses via `linear_combination`; then `hq.dvd_of_dvd_pow` forces `q ∣ α`, contradicting `hpa`.
- Hypotheses: `q` is prime; `q ∤ α`; `c₂, c₄, c₆` arbitrary ring elements.
- Uses from project: []
- Used by: `den_no_simple_prime_factor_of_on_curve`
- Visibility: private
- Lines: 29–40 (proof ~10 lines)
- Notes: `omit [IsDomain R] [UniqueFactorizationMonoid R]` (only `CommRing` + primality needed). none

### lemma clearing_denominators
- Type: `(W : WeierstrassCurve R) {x y : K} (heq : Weierstrass eqn for (x,y) over K) {α d γ e : R} (hd_ne : d ≠ 0) (he_ne : e ≠ 0) (hx : x = algebraMap R K α / algebraMap R K d) (hy : y = algebraMap R K γ / algebraMap R K e) : γ²d³ + a₁αγd²e + a₃γd³e = e²(α³ + a₂α²d + a₄αd² + a₆d³)` (signature >3 lines; abbreviated)
- What: Clears denominators in the Weierstrass equation: if `x = α/d` and `y = γ/e` in the fraction field, then multiplying the curve equation by `d³e²` yields the stated polynomial identity in `R`.
- How: Reduce to an equality in `K` via `IsFractionRing.injective R K`; nonvanishing of `algebraMap d`, `algebraMap e` comes from `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors` (+ `mem_nonZeroDivisors_of_ne_zero`); substitute `hx`,`hy` into `heq`, multiply both sides by `d³e²` (`congr_arg`), then `field_simp` clears the fractions and `linear_combination key` matches the two polynomial sides.
- Hypotheses: `(x,y)` satisfies the Weierstrass equation over `K`; denominators `d, e` nonzero; `x, y` expressed as the given fractions.
- Uses from project: []
- Used by: `den_no_simple_prime_factor_of_on_curve`
- Visibility: private
- Lines: 44–71 (proof ~14 lines)
- Notes: `omit [UniqueFactorizationMonoid R]` (UFD not needed for clearing). long? No — proof under 30 lines. none

### theorem den_no_simple_prime_factor_of_on_curve
- Type: `(W : WeierstrassCurve R) {x y : K} (heq : Weierstrass eqn for (x,y) over K) {q : R} (hq : Prime q) (hqd : q ∣ (den R x : R)) (hq2 : ¬ q² ∣ (den R x : R)) : False` (signature >3 lines; abbreviated)
- What: If `(x,y)` lies on a Weierstrass curve over a UFD and a prime `q` divides the reduced denominator of `x` exactly once (`q ∣ den`, `q² ∤ den`), this is contradictory — i.e. denominators of `x`-coordinates are never divisible by a prime to exactly the first power.
- How: Write `x = α/d`, `y = γ/e` in reduced form (`IsFractionRing.num_den_reduced`, `mk'_num_den'`); reducedness gives `q ∤ α`. Factor `d = q·u` with `q ∤ u` (using `hq2`). Apply `clearing_denominators` to get equation `hZ` in `R`. Set `S := α³ + a₂α²d + a₄αd² + a₆d³`; via `not_dvd_sum_of_not_dvd_cube`, `q ∤ S`. Then three descent rounds: (R1) `q ∣ LHS = e²S` so `q ∣ e²` so `q ∣ e` (`hq.dvd_or_dvd` + `.resolve_right` + `dvd_of_dvd_pow`); (R2) substitute `e = q·e₁`, cancel `q²` (`mul_left_cancel₀`), get `q ∣ e₁²S` so `q ∣ e₁`; (R3) substitute `e₁ = q·e₂`, cancel `q`, get `q ∣ γ²u³`, and since `q ∤ u`, `q ∣ γ`. Finally `q ∣ γ` and `q ∣ e` contradict `IsRelPrime γ e` (`hcop_y`) via `hq.not_unit`. Each round's algebraic rearrangement is closed by `linear_combination` / explicit divisibility witnesses + `ring`.
- Hypotheses: `(x,y)` on the Weierstrass curve over `K`; `q` prime in `R`; `q` divides `den(x)` but `q²` does not.
- Uses from project: `not_dvd_sum_of_not_dvd_cube`, `clearing_denominators`
- Used by: `den_not_prime_of_on_curve`
- Visibility: public
- Lines: 87–170 (proof ~84 lines)
- Notes: OVER-50 (proof ~84 lines — needs `/decompose-proof` pass; natural split is the three descent rounds R1/R2/R3). No `sorry`/`set_option`/`TODO`.

### theorem den_not_prime_of_on_curve
- Type: `(W : WeierstrassCurve R) {x y : K} (heq : Weierstrass eqn for (x,y) over K) (hp : Prime (den R x : R)) : False` (signature >3 lines; abbreviated)
- What: Corollary — if the reduced denominator of `x` is itself a prime element, then `(x,y)` on the curve is contradictory.
- How: Apply `den_no_simple_prime_factor_of_on_curve` with `q := den R x`: `q ∣ q` is `dvd_rfl`, and `q² ∤ q` since otherwise `1 = q·c` (via `sq`, `mul_assoc`, `mul_left_cancel₀ hp.ne_zero`), making `q` a unit (`isUnit_of_dvd_one`), contradicting `hp.not_unit`.
- Hypotheses: `(x,y)` on the curve over `K`; `den(x)` is a prime element of `R`.
- Uses from project: `den_no_simple_prime_factor_of_on_curve`
- Used by: unused in file
- Visibility: public
- Lines: 176–186 (proof ~10 lines, term-mode with inline `by`)
- Notes: none

---

## File Summary

- Total decls: 4 (defs: 0 / lemmas+theorems: 4 / instances: 0). Breakdown: 2 private lemmas, 2 public theorems.
- Key API (used by ≥3 in-file): none. The most-used decl is `den_no_simple_prime_factor_of_on_curve` (used by 1: `den_not_prime_of_on_curve`); the two private helpers are each used by 1.
- Unused decls (within this file): `den_not_prime_of_on_curve` (public corollary — likely consumed by downstream files in the project).
- Decls with `sorry`: none.
- Decls with `set_option`: none.
- Proofs >50 lines: 1 — `den_no_simple_prime_factor_of_on_curve` (~84 lines, OVER-50).
- Proofs 30–50 lines: 0.
