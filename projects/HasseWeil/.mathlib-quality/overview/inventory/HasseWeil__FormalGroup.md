# Inventory: ./HasseWeil/FormalGroup.lean

**File**: `HasseWeil/FormalGroup.lean`
**Imports**: `HasseWeil.PowerSeriesHelpers`, `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`, `Mathlib.RingTheory.PowerSeries.Basic`, `Mathlib.RingTheory.MvPowerSeries.Basic`
**Imported by**: `HasseWeil.FormalGroup` (directly used in `LocalExpansion.lean` and `FormalGroupAssoc.lean`)

---

## Section 1: Convolution helpers

### `def conv₂`
- **Type**: `(ℕ → R) → ℕ → R`
- **What**: The discrete convolution of a sequence `f` with itself: `(conv₂ f n) = Σ_{i=0}^{n} f(i) * f(n-i)`.
- **How**: Direct Finset.sum computation.
- **Hypotheses**: `R : Type*`, `[CommRing R]`
- **Uses from project**: []
- **Used by**: `formalW_step`, `coeff_formalW_sq`, `coeff_formalW_cube`, `conv₂_truncate`, `conv₂_truncate'`, `formalW_recurrence`, `formalGroupLaw_coeff`
- **Visibility**: public
- **Lines**: 16–18 (def, ~2 lines)
- **Notes**: Key computational helper used in 7+ sites.

---

### `def conv₃`
- **Type**: `(ℕ → R) → ℕ → R`
- **What**: The triple discrete convolution: `(conv₃ f n) = Σ_{i,j} f(i)*f(j)*f(n-i-j)`.
- **How**: Nested Finset.sum.
- **Hypotheses**: `R : Type*`, `[CommRing R]`
- **Uses from project**: []
- **Used by**: `formalW_step`, `coeff_formalW_cube`, `conv₃_truncate`, `formalW_recurrence`
- **Visibility**: public
- **Lines**: 19–21 (def, ~3 lines)
- **Notes**: Companion to `conv₂`; encodes the w³ term of the formal group recurrence.

---

## Section 2: w(z) and u(z)

### `def formalW_step`
- **Type**: `WeierstrassCurve R → ℕ → (∀ m, m < n → R) → R`
- **What**: The well-founded step function for the coefficient recurrence of `w(z)`: returns 0 for n<3, 1 for n=3, and the Silverman IV.1.1 linear combination for n≥4.
- **How**: If-then-else case split using `conv₂` and `conv₃` of the predecessor values.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `conv₂`, `conv₃`
- **Used by**: `formalW_coeff`, `formalW_coeff_eq_step`, `formalW_recurrence`
- **Visibility**: public
- **Lines**: 25–29 (def, ~5 lines)
- **Notes**: The step function fed to `WellFoundedRelation.wf.fix`.

---

### `noncomputable def formalW_coeff`
- **Type**: `WeierstrassCurve R → ℕ → R`
- **What**: The n-th coefficient of the formal series `w(z)` (Silverman Ch. IV §1), defined by well-founded recursion: `w(z) = z³ + a₁zw + a₂z²w + a₃w² + a₄zw² + a₆w³`.
- **How**: Uses `WellFoundedRelation.wf.fix (formalW_step W)`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `formalW_step`
- **Used by**: `formalW`, `formalU_coeff`, `formalInverse_coeff` (via `invDenom_coeff`), `formalGroupLaw_coeff`, all `formalW_coeff_*` theorems, `conv₂_truncate`, `conv₂_truncate'`, `coeff_formalW_sq`, `coeff_formalW_cube`, `conv₃_truncate`, `formalW_recurrence`
- **Visibility**: public
- **Lines**: 31–33 (def, ~2 lines)
- **Notes**: The central computational object; used by 10+ declarations in the file.

---

### `noncomputable def formalW`
- **Type**: `WeierstrassCurve R → PowerSeries R`
- **What**: The formal power series `w(z) ∈ R⟦z⟧` (Silverman IV §1), constructed as `PowerSeries.mk (formalW_coeff W)`.
- **How**: Direct `PowerSeries.mk`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `formalW_coeff`
- **Used by**: `coeff_formalW_sq`, `coeff_formalW_cube`, `coeff_formalW_pow_two`, `coeff_formalW_pow_three`, `formalW_recurrence`; also used extensively in `LocalExpansion.lean`
- **Visibility**: public
- **Lines**: 34–36 (def, ~2 lines)
- **Notes**: Wraps `formalW_coeff` into a `PowerSeries`; used in `LocalExpansion.lean` and `FormalGroupAssoc.lean`.

---

### `noncomputable def formalU_coeff`
- **Type**: `WeierstrassCurve R → ℕ → R`
- **What**: The n-th coefficient of the unit series `u(z) = w(z)/z³ = 1 + a₁z + ...`; simply `formalW_coeff W (n+3)`.
- **How**: Direct shift of `formalW_coeff`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `formalW_coeff`
- **Used by**: `invDenom_coeff`, `formalU_coeff_zero`
- **Visibility**: public
- **Lines**: 37–39 (def, ~2 lines)
- **Notes**: Used in `invDenom_coeff` for the formal inverse construction.

---

### `noncomputable def formalPoly`
- **Type**: `WeierstrassCurve R → MvPowerSeries (Fin 2) R`
- **What**: The bivariate power series `z³ + a₁zw + a₂z²w + a₃w² + a₄zw² + a₆w³` in two variables z=X₀, w=X₁, encoding the Weierstrass equation as an element of `R⟦z,w⟧`.
- **How**: Direct MvPowerSeries expression using `MvPowerSeries.X 0`, `MvPowerSeries.X 1`, and `MvPowerSeries.C`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: []
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 40–45 (def, ~6 lines)
- **Notes**: Appears to be a standalone reference object; not referenced anywhere else in this file. Possible dead code or intended for future use.

---

## Section 3: Formal inverse i(z)

### `private noncomputable def invDenom_coeff`
- **Type**: `WeierstrassCurve R → ℕ → R`
- **What**: Coefficients of the denominator series `1 - a₁z - a₃z³u(z)`, computed by well-founded recursion so that the formal inverse can be expressed as `-z/(denominator)`.
- **How**: `WellFoundedRelation.wf.fix` with base case 1 and recursion using `formalU_coeff`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `formalU_coeff`
- **Used by**: `formalInverse_coeff`
- **Visibility**: private
- **Lines**: 49–55 (def, ~7 lines)

---

### `noncomputable def formalInverse_coeff`
- **Type**: `WeierstrassCurve R → ℕ → R`
- **What**: The n-th coefficient of the formal inverse `i(z) = -z/(1 - a₁z - a₃z³u(z))`.
- **How**: Uses `invDenom_coeff`: coefficient 0 is 0, coefficient n≥1 is `-(invDenom_coeff W (n-1))`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `invDenom_coeff`
- **Used by**: `formalInverse`, `formalGroupLaw_coeff`
- **Visibility**: public
- **Lines**: 57–59 (def, ~2 lines)
- **Notes**: Also used in `FormalGroupAssoc.lean`.

---

### `noncomputable def formalInverse`
- **Type**: `WeierstrassCurve R → PowerSeries R`
- **What**: The formal inverse power series `i(z) ∈ R⟦z⟧`.
- **How**: `PowerSeries.mk (formalInverse_coeff W)`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `formalInverse_coeff`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 60–62 (def, ~2 lines)
- **Notes**: Dead code in this file; presumably consumed by `FormalGroupAssoc.lean` or downstream files.

---

## Section 4: Bivariate helpers

### `private def bmul`
- **Type**: `(ℕ → ℕ → R) → (ℕ → ℕ → R) → ℕ → ℕ → R`
- **What**: Bivariate Cauchy product: `(bmul f g)(i,j) = Σ_{a≤i, b≤j} f(a,b)*g(i-a,j-b)`.
- **How**: Double Finset.sum.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: []
- **Used by**: `bpow`, `formalGroupLaw_coeff` (inline)
- **Visibility**: private
- **Lines**: 65–67 (def, ~3 lines)

---

### `private noncomputable def binv_by_degree`
- **Type**: `(ℕ → ℕ → R) → ℕ → (ℕ → ℕ → R)`
- **What**: Degree-layered inversion of a bivariate unit power series: computes `g_{i,j}` at total degree N using previously computed coefficients of smaller degree, implementing `g·f = 1`.
- **How**: `WellFoundedRelation.wf.fix` on the total degree `i+j`; base case g₀₀=1, recursion is `-Σ_{(a,b)≠(i,j)} g_{a,b}*f_{i-a,j-b}`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: []
- **Used by**: `binv_aux`
- **Visibility**: private
- **Lines**: 77–88 (def, ~12 lines)
- **Notes**: Implements bivariate unit inversion layer by layer on total degree.

---

### `private noncomputable def binv_aux`
- **Type**: `(ℕ → ℕ → R) → ℕ → ℕ → R`
- **What**: Thin wrapper: extracts the (i,j)-entry from `binv_by_degree f (i+j)`.
- **How**: Direct call to `binv_by_degree`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `binv_by_degree`
- **Used by**: `binv`
- **Visibility**: private
- **Lines**: 90–91 (def, ~2 lines)

---

### `private noncomputable def binv`
- **Type**: `(ℕ → ℕ → R) → ℕ → ℕ → R`
- **What**: The bivariate inverse of a bivariate power series `f` with `f(0,0)=1`; alias for `binv_aux`.
- **How**: Delegation to `binv_aux`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `binv_aux`
- **Used by**: `formalGroupLaw_coeff` (inline as `binv A`)
- **Visibility**: private
- **Lines**: 93–94 (def, ~2 lines)

---

### `private def bpow`
- **Type**: `(ℕ → ℕ → R) → ℕ → ℕ → ℕ → R`
- **What**: The n-fold convolution (power) of a bivariate formal series: `f^0 = δ_{(0,0)}`, `f^{k+1} = f * f^k` (using `bmul`).
- **How**: Structural recursion on the exponent; base case is the bivariate delta at (0,0).
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `bmul`
- **Used by**: `bcomp`
- **Visibility**: private
- **Lines**: 96–98 (def, ~3 lines)

---

### `private noncomputable def bcomp`
- **Type**: `(ℕ → R) → (ℕ → ℕ → R) → ℕ → ℕ → R`
- **What**: Bivariate composition `(h ∘ s)(i,j) = Σ_{n=0}^{i+j} h(n)*s^n(i,j)`, where `s^n` is the n-th bivariate power.
- **How**: Finset.sum over `n` up to `i+j`, using `bpow`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `bpow`
- **Used by**: `formalGroupLaw_coeff` (as `bcomp (formalInverse_coeff W) z3 i j`)
- **Visibility**: private
- **Lines**: 100–101 (def, ~2 lines)

---

## Section 5: Formal group law F(z₁,z₂)

### `structure FormalGroupLaw`
- **Type**: `(R : Type*) → [CommRing R] → Type*`; single field `toMvPowerSeries : MvPowerSeries (Fin 2) R`
- **What**: A thin wrapper structure holding a bivariate formal power series, representing the formal group law `F(z₁,z₂)`.
- **How**: Single-field structure.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: []
- **Used by**: `formalGroupLaw`
- **Visibility**: public
- **Lines**: 105–107 (structure, ~3 lines)
- **Notes**: Minimal structure with no axioms; not confirmed to satisfy formal-group-law axioms within this file.

---

### `noncomputable def formalGroupLaw_coeff`
- **Type**: `WeierstrassCurve R → (Fin 2 →₀ ℕ) → R`
- **What**: The (i,j)-th coefficient of the formal group law `F(z₁,z₂)` (Silverman IV): explicit formulas for low degrees (0 through 4), and for degree ≥5 computes via the slope/intercept formula `F = i(z₃)` where `z₃ = -B·A⁻¹ - z₁ - z₂` using bivariate inversion and composition.
- **How**: Case split on total degree `i+j`; degree ≥5 uses `bmul`, `binv`, `bcomp`, and `formalInverse_coeff`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `formalW_coeff`, `formalInverse_coeff`, `bmul`, `binv`, `bcomp`
- **Used by**: `formalGroupLaw`, `formalGroupLaw_dX_at_zero`; also used heavily in `FormalGroupAssoc.lean`
- **Visibility**: public
- **Lines**: 108–133 (def, ~26 lines)
- **Notes**: Core formula for the elliptic curve formal group law. The degree-1 terms give `F(z₁,0)=z₁` and `F(0,z₂)=z₂`; the degree-2 term is `-a₁`.

---

### `noncomputable def formalGroupLaw`
- **Type**: `WeierstrassCurve R → FormalGroupLaw R`
- **What**: Packages `formalGroupLaw_coeff` into the `FormalGroupLaw` structure.
- **How**: Anonymous constructor.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `formalGroupLaw_coeff`, `FormalGroupLaw`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 134–135 (def, ~2 lines)
- **Notes**: Dead code in this file; the coefficient function `formalGroupLaw_coeff` is used directly downstream.

---

## Section 6: Invariant differential ω

### `noncomputable def formalGroupLaw_dX_at_zero`
- **Type**: `WeierstrassCurve R → ℕ → R`
- **What**: The n-th coefficient of `∂F/∂z₁ |_{z₁=0}(z₂)`, i.e., the coefficient `F_{1,n}` of `z₁^1 · z₂^n` in the formal group law — used to build the invariant differential.
- **How**: Directly reads off `formalGroupLaw_coeff W (Finsupp.single 0 1 + Finsupp.single 1 n)`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `formalGroupLaw_coeff`
- **Used by**: `formalDiffCoeff`
- **Visibility**: public
- **Lines**: 139–140 (def, ~2 lines)

---

### `noncomputable def formalDiffCoeff`
- **Type**: `WeierstrassCurve R → ℕ → R`
- **What**: The n-th coefficient of the invariant differential `ω(z)/dz = 1/F_X(0,z)`; computed by well-founded recursion as the inverse of `formalGroupLaw_dX_at_zero`.
- **How**: `WellFoundedRelation.wf.fix`; base case 1, recursion is `-Σ_{k<n} formalDiffCoeff(k) * formalGroupLaw_dX_at_zero(n-k)`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `formalGroupLaw_dX_at_zero`
- **Used by**: `formalDiff`, `formalDiffCoeff_zero`
- **Visibility**: public
- **Lines**: 142–147 (def, ~6 lines)

---

### `noncomputable def formalDiff`
- **Type**: `WeierstrassCurve R → PowerSeries R`
- **What**: The formal invariant differential `ω(z)/dz ∈ R⟦z⟧`.
- **How**: `PowerSeries.mk (formalDiffCoeff W)`.
- **Hypotheses**: `[CommRing R]`
- **Uses from project**: `formalDiffCoeff`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 148–149 (def, ~2 lines)
- **Notes**: Leaf definition; no properties proved in this file beyond `formalDiffCoeff_zero`.

---

## Section 7: Properties

### `theorem formalW_coeff_three`
- **Type**: `formalW_coeff W 3 = 1`
- **What**: The third coefficient of `w(z)` equals 1 (the leading term `z³`).
- **How**: `simp [formalW_coeff, WellFounded.fix_eq, formalW_step]`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`
- **Uses from project**: `formalW_coeff`, `formalW_step`
- **Used by**: `formalU_coeff_zero`, `conv₂_truncate`, `conv₂_truncate'`, `conv₃_truncate`, `formalW_recurrence`; also `LocalExpansion.lean`
- **Visibility**: public
- **Lines**: 155–157, proof 2 lines

---

### `theorem formalW_coeff_zero`
- **Type**: `formalW_coeff W 0 = 0`
- **What**: The zeroth coefficient of `w(z)` is 0.
- **How**: `simp [formalW_coeff, WellFounded.fix_eq, formalW_step]`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`
- **Uses from project**: `formalW_coeff`, `formalW_step`
- **Used by**: `conv₂_truncate`, `conv₂_truncate'`, `conv₃_truncate`, `formalW_recurrence`; also `LocalExpansion.lean`
- **Visibility**: public
- **Lines**: 158–160, proof 2 lines

---

### `theorem formalW_coeff_one`
- **Type**: `formalW_coeff W 1 = 0`
- **What**: The first coefficient of `w(z)` is 0.
- **How**: `simp [formalW_coeff, WellFounded.fix_eq, formalW_step]`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`
- **Uses from project**: `formalW_coeff`, `formalW_step`
- **Used by**: `formalW_recurrence`; also `LocalExpansion.lean`
- **Visibility**: public
- **Lines**: 161–163, proof 2 lines

---

### `theorem formalW_coeff_two`
- **Type**: `formalW_coeff W 2 = 0`
- **What**: The second coefficient of `w(z)` is 0.
- **How**: `simp [formalW_coeff, WellFounded.fix_eq, formalW_step]`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`
- **Uses from project**: `formalW_coeff`, `formalW_step`
- **Used by**: `formalW_recurrence`; also `LocalExpansion.lean`
- **Visibility**: public
- **Lines**: 164–166, proof 2 lines

---

### `theorem formalU_coeff_zero`
- **Type**: `formalU_coeff W 0 = 1`
- **What**: The zeroth coefficient of `u(z)` is 1, i.e., `u(0) = 1`.
- **How**: Definitional equality `formalU_coeff W 0 = formalW_coeff W 3 = 1`, using `formalW_coeff_three`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`
- **Uses from project**: `formalU_coeff`, `formalW_coeff_three`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 167–168, proof 0 lines (term-mode)

---

### `theorem formalDiffCoeff_zero`
- **Type**: `formalDiffCoeff W 0 = 1`
- **What**: The constant term of the invariant differential coefficient series is 1.
- **How**: `simp [formalDiffCoeff, WellFounded.fix_eq]`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`
- **Uses from project**: `formalDiffCoeff`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 169–170, proof 1 line

---

### `theorem formalW_coeff_eq_step`
- **Type**: `formalW_coeff W n = formalW_step W n (fun m _ => formalW_coeff W m)`
- **What**: Unfolding lemma: the well-founded recursion for `formalW_coeff` agrees with one step of `formalW_step` applied to itself.
- **How**: Uses `WellFoundedRelation.wf.fix_eq` and `rfl`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`, `n : ℕ`
- **Uses from project**: `formalW_coeff`, `formalW_step`
- **Used by**: `formalW_recurrence`
- **Visibility**: public
- **Lines**: 180–185, proof 5 lines

---

### `theorem conv₂_truncate`
- **Type**: `conv₂ (fun m => if m < n then formalW_coeff W m else 0) n = conv₂ (formalW_coeff W) n`
- **What**: The truncated convolution (zeroing out terms ≥ n) equals the full convolution, because `formalW_coeff W k = 0` for k < 3.
- **How**: `Finset.sum_congr rfl`; case split on `i < n` vs `i = n`, using `formalW_coeff_zero`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`, `n : ℕ`
- **Uses from project**: `conv₂`, `formalW_coeff`, `formalW_coeff_zero`
- **Used by**: `formalW_recurrence`
- **Visibility**: public
- **Lines**: 189–213, proof 23 lines

---

### `theorem conv₂_truncate'`
- **Type**: `conv₂ (fun m => if m < n then formalW_coeff W m else 0) (n - 1) = conv₂ (formalW_coeff W) (n - 1)` (for `1 ≤ n`)
- **What**: Variant of `conv₂_truncate` for index `n-1`: truncation at `n` does not affect the convolution at `n-1`.
- **How**: `Finset.sum_congr rfl`; since `i < n-1 < n` and `n-1-i < n`, both conditionals are positive.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`, `n : ℕ`, `hn : 1 ≤ n`
- **Uses from project**: `conv₂`, `formalW_coeff`
- **Used by**: `formalW_recurrence`
- **Visibility**: public
- **Lines**: 215–228, proof 13 lines

---

### `theorem coeff_formalW_sq`
- **Type**: `PowerSeries.coeff n (formalW W * formalW W) = conv₂ (formalW_coeff W) n`
- **What**: The n-th coefficient of `w(z)²` equals the convolution `conv₂`.
- **How**: Uses `PowerSeries.coeff_mul`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, and `PowerSeries.coeff_mk`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`, `n : ℕ`
- **Uses from project**: `formalW`, `formalW_coeff`, `conv₂`
- **Used by**: `coeff_formalW_pow_two`, `coeff_formalW_cube`, `formalW_recurrence`
- **Visibility**: public
- **Lines**: 231–243, proof 13 lines

---

### `theorem coeff_formalW_pow_two`
- **Type**: `PowerSeries.coeff n ((formalW W) ^ 2) = conv₂ (formalW_coeff W) n`
- **What**: The n-th coefficient of `w(z)^2` (written as `^2`) equals `conv₂`.
- **How**: Uses `sq` to reduce to `coeff_formalW_sq`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`, `n : ℕ`
- **Uses from project**: `formalW`, `formalW_coeff`, `conv₂`, `coeff_formalW_sq`
- **Used by**: `formalW_recurrence`
- **Visibility**: public
- **Lines**: 246–248, proof 2 lines

---

### `theorem coeff_formalW_cube`
- **Type**: `PowerSeries.coeff n (formalW W * (formalW W * formalW W)) = conv₃ (formalW_coeff W) n`
- **What**: The n-th coefficient of `w(z)³` (written as `w*(w*w)`) equals `conv₃`.
- **How**: Uses `PowerSeries.coeff_mul`, `sum_antidiagonal_eq_sum_range_succ`, `coeff_formalW_sq`, and distributivity.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`, `n : ℕ`
- **Uses from project**: `formalW`, `formalW_coeff`, `conv₂`, `conv₃`, `coeff_formalW_sq`
- **Used by**: `coeff_formalW_pow_three`, `formalW_recurrence`
- **Visibility**: public
- **Lines**: 251–269, proof 18 lines

---

### `theorem coeff_formalW_pow_three`
- **Type**: `PowerSeries.coeff n ((formalW W) ^ 3) = conv₃ (formalW_coeff W) n`
- **What**: The n-th coefficient of `w(z)^3` (written as `^3`) equals `conv₃`.
- **How**: Shows `(formalW W)^3 = formalW W * (formalW W * formalW W)` via `pow_succ, sq, mul_comm`; applies `coeff_formalW_cube`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`, `n : ℕ`
- **Uses from project**: `formalW`, `conv₃`, `coeff_formalW_cube`
- **Used by**: `formalW_recurrence`
- **Visibility**: public
- **Lines**: 272–278, proof 6 lines

---

### `theorem conv₃_truncate`
- **Type**: `conv₃ (fun m => if m < n then formalW_coeff W m else 0) n = conv₃ (formalW_coeff W) n`
- **What**: The truncated triple convolution equals the full one, exploiting the vanishing of `formalW_coeff W k` for k < 3.
- **How**: Double `Finset.sum_congr rfl`; case split on `i=n` vs `i<n`, then `j=n-i` vs `j<n-i`; uses `formalW_coeff_zero`.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`, `n : ℕ`
- **Uses from project**: `conv₃`, `formalW_coeff`, `formalW_coeff_zero`
- **Used by**: `formalW_recurrence`
- **Visibility**: public
- **Lines**: 282–324, proof ~51 lines
- **Notes**: Proof longer than 30 lines; a 3-case split with sub-cases at each level.

---

### `theorem formalW_recurrence`
- **Type**: `formalW W = X^3 + C(a₁)*X*(formalW W) + C(a₂)*X^2*(formalW W) + C(a₃)*(formalW W)^2 + C(a₄)*X*(formalW W)^2 + C(a₆)*(formalW W)^3`
- **What**: Silverman IV.1.1: the power series `w(z)` satisfies the formal Weierstrass recurrence as an identity in `R⟦X⟧`.
- **How**: Coefficient-by-coefficient via `PowerSeries.ext`; uses `formalW_coeff_eq_step` to unfold the LHS, `coeff_formalW_pow_two`/`_three` and `conv₂_truncate`/`conv₂_truncate'`/`conv₃_truncate` for the RHS; then case splits n<3, n=3, n≥4.
- **Hypotheses**: `[CommRing R]`, `W : WeierstrassCurve R`
- **Uses from project**: `formalW`, `formalW_coeff`, `formalW_step`, `formalW_coeff_eq_step`, `coeff_formalW_pow_two`, `coeff_formalW_pow_three`, `conv₂_truncate`, `conv₂_truncate'`, `conv₃_truncate`, `formalW_coeff_zero`, `formalW_coeff_one`, `formalW_coeff_two`, `conv₂`, `conv₃`
- **Used by**: used in `LocalExpansion.lean` (`formalW_recurrence_lift`)
- **Visibility**: public
- **Lines**: 336–439, proof ~104 lines (the longest proof in the file)
- **Notes**: Proof longer than 30 lines (approximately 104 lines). The n<3 cases are handled by `interval_cases` + simp; the n=3 case by direct computation; n≥4 by the truncation lemmas + `ring`. The main mathlib-provided tool is `PowerSeries.coeff_X_pow_mul'` and `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`.
