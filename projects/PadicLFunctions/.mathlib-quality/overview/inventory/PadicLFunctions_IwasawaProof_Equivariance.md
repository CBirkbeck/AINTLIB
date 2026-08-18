# Inventory: PadicLFunctions/IwasawaProof/Equivariance.lean

Equivariance of the Coleman map (RJW §12.1): the `ℤ_p`/Teichmüller structure on the unit tower, the killing of `μ_{p−1}` by `Col`, and the `Λ(𝒢)`-module equivariance statement. File opens `noncomputable section` in `namespace PadicLFunctions.Coleman`, with `variable (p : ℕ) [hp : Fact p.Prime]`.

Imports: `PadicLFunctions.IwasawaProof.GaloisAction`, `PadicLFunctions.Iwasawa.ResidueField`.

---

### theorem dlog_mul
- Type: `{g h : PowerSeries ℤ_[p]} (hg : IsUnit g) (hh : IsUnit h) : dlog p (g * h) = dlog p g + dlog p h`
- What: The logarithmic derivative `∂log` is additive on products of unit power series.
- How: Product rule `(gh)' = g'h + gh'`; rewrites with `PowerSeries.derivativeFun_mul`, cancels via `Ring.mul_inverse_cancel`, and closes a bookkeeping identity with `ring`. In-file re-derivation of `LogDerivative.dlog_mul`.
- Hypotheses: `g` and `h` are units in `ℤ_[p]⟦X⟧`.
- Uses from project: [`dlog`]
- Used by: `dlog_pow`
- Visibility: private
- Lines: 41–52 (proof ≈10)
- Notes: none

### theorem dlog_one
- Type: `dlog p (1 : PowerSeries ℤ_[p]) = 0`
- What: The logarithmic derivative of the constant unit `1` is zero.
- How: `PowerSeries.derivativeFun_one` makes the derivative `0`, then `mul_zero`/`zero_mul`. In-file re-derivation of `LogDerivative.dlog_one`.
- Hypotheses: none.
- Uses from project: [`dlog`]
- Used by: `dlog_pow`, `Col_eq_zero_of_torsion`
- Visibility: private
- Lines: 54–56 (proof 1)
- Notes: none

### theorem dlog_pow
- Type: `{g : PowerSeries ℤ_[p]} (hg : IsUnit g) (k : ℕ) : dlog p (g ^ k) = (k : ℤ) • dlog p g`
- What: `∂log(gᵏ) = k·∂log g` for a unit power series `g`.
- How: Induction on `k`; base via `dlog_one`, step via `pow_succ` + `dlog_mul` (on `g^m` and `g`) + `push_cast; ring`. Re-derivation of `LogDerivative.dlog_pow`.
- Hypotheses: `g` a unit in `ℤ_[p]⟦X⟧`; `k` a natural number.
- Uses from project: [`dlog`]
- Used by: `Col_eq_zero_of_torsion`
- Visibility: private
- Lines: 58–63 (proof ≈3)
- Notes: none

### theorem colemanSeries_one
- Type: `colemanSeries p (1 : NormCompatUnits p) = 1`
- What: The Coleman series of the identity norm-compatible unit is the constant series `1`.
- How: `colemanSeries_mul` at `1·1=1` shows `colemanSeries 1` is idempotent; `mul_right_eq_self₀` plus nonzeroness (`colemanSeries_isUnit`) forces it to equal `1`.
- Hypotheses: none.
- Uses from project: [`colemanSeries`, `colemanSeries_mul`, `colemanSeries_isUnit`, `NormCompatUnits`]
- Used by: `colemanSeries_pow`, `Col_eq_zero_of_torsion`
- Visibility: private
- Lines: 65–70 (proof ≈4)
- Notes: none

### theorem colemanSeries_pow
- Type: `(u : NormCompatUnits p) (k : ℕ) : colemanSeries p (u ^ k) = (colemanSeries p u) ^ k`
- What: `colemanSeries` is multiplicative on powers: it carries `uᵏ` to `(f_u)ᵏ`.
- How: Induction on `k`; base via `colemanSeries_one`, step via `pow_succ` + `colemanSeries_mul`.
- Hypotheses: `u` a norm-compatible unit; `k` a natural number.
- Uses from project: [`colemanSeries`, `colemanSeries_mul`, `colemanSeries_one`, `NormCompatUnits`]
- Used by: `Col_eq_zero_of_torsion`
- Visibility: private
- Lines: 72–77 (proof ≈3)
- Notes: none

### theorem elems_pow
- Type: `(u : NormCompatUnits p) (k n : ℕ) : (u ^ k).elems n = (u.elems n) ^ k`
- What: The level-`n` component of a power of a norm-compatible unit is the `k`-th power of its level-`n` component (multiplication is pointwise).
- How: Induction on `k`; both cases reduce by `pow_succ`/`pow_zero` and `rfl` (pointwise structure of `NormCompatUnits`).
- Hypotheses: `u` a norm-compatible unit; `k, n` naturals.
- Uses from project: [`NormCompatUnits`, `NormCompatUnits.elems`]
- Used by: `Col_eq_zero_of_torsion`
- Visibility: private
- Lines: 79–85 (proof ≈3)
- Notes: none

### theorem zsmul_powerSeries_eq_zero
- Type: `{g : PowerSeries ℤ_[p]} {k : ℕ} (hk : k ≠ 0) (h : (k : ℤ) • g = 0) : g = 0`
- What: A nonzero integer scalar annihilates no `ℤ_[p]` power series; torsion-freeness of `ℤ_[p]⟦T⟧`.
- How: Coefficientwise (`ext n`): `map_zsmul` pushes the scalar through `PowerSeries.coeff`, and `smul_eq_zero` with `k ≠ 0` (using `ℤ_[p]` `CharZero`/domain) forces each coefficient to vanish.
- Hypotheses: `k ≠ 0`; `(k:ℤ) • g = 0`.
- Uses from project: []
- Used by: `Col_eq_zero_of_torsion`
- Visibility: private
- Lines: 87–95 (proof ≈6)
- Notes: none

### theorem Col_eq_zero_of_torsion
- Type: `(u : NormCompatUnits p) (htor : ∀ n, (u.elems n) ^ (p - 1) = 1) : Col p u = 0`
- What: RJW §12.1 Lemma — the Teichmüller torsion subgroup `μ_{p−1} ⊂ 𝒰_∞` is killed by the Coleman map `Col`.
- How: Elementwise `(p−1)`-torsion gives `u^{p−1}=1` (`elems_pow`), hence `(f_u)^{p−1}=1` (`colemanSeries_pow`, `colemanSeries_one`); then `(p−1)·∂log f_u = ∂log 1 = 0` (`dlog_pow`, `dlog_one`) and torsion-freeness (`zsmul_powerSeries_eq_zero`, using `p−1≠0` via `hp.out.two_le`) gives `∂log f_u = 0`; finally push through the linear tail of `Col` (`map_zero`, `LinearMap.zero_comp`, `PadicMeasure.unitsCmul`).
- Hypotheses: every level component `u.elems n` is `(p−1)`-torsion (`(u.elems n)^(p−1)=1`).
- Uses from project: [`NormCompatUnits`, `NormCompatUnits.elems`, `Col`, `elems_pow`, `colemanSeries`, `colemanSeries_pow`, `colemanSeries_one`, `colemanSeries_isUnit`, `dlog`, `dlog_pow`, `dlog_one`, `zsmul_powerSeries_eq_zero`, `PadicMeasure.unitsCmul`]
- Used by: unused in file
- Visibility: public
- Lines: 97–120 (proof ≈14)
- Notes: long-ish but under 30; uses `hp.out.two_le`; none

### theorem Col_lambdaG_equivariant
- Type: `(a : ℤ_[p]ˣ) (u : NormCompatUnits p) (_hu : u ∈ unitsTower1 p) : Col p (galNCU p a u) = PadicMeasure.pushforward p (unitsMulLeftCM p a) (Col p u)`
- What: RJW cor:G-eq — `Col` is `Λ(𝒢)`-equivariant on `𝒰_{∞,1}`: applying the Galois action `σ_a` before `Col` equals pushing the measure forward along `v ↦ a·v`.
- How: Direct restatement; proved by `Col_galNCU p a u` (the `𝒢`-equivariance already established in `GaloisAction`).
- Hypotheses: `a` a `p`-adic unit; `u` in the principal-unit subtower `unitsTower1 p`.
- Uses from project: [`Col`, `galNCU`, `unitsTower1`, `unitsMulLeftCM`, `Col_galNCU`, `NormCompatUnits`, `PadicMeasure.pushforward`]
- Used by: unused in file
- Visibility: public
- Lines: 122–130 (proof 1)
- Notes: none

---

## File Summary

- Total decls: 9 (defs: 0 / lemmas+theorems: 9 / instances: 0). All 9 are `theorem`s; 7 `private`, 2 public.
- Key API (used by ≥3 in-file): none. Highest in-file fan-in: `dlog_one` and `colemanSeries_one` (each used by 2). The two public results (`Col_eq_zero_of_torsion`, `Col_lambdaG_equivariant`) are the file's exports and are unused within the file; the seven private helpers feed only `Col_eq_zero_of_torsion`.
- Unused in file: `Col_eq_zero_of_torsion`, `Col_lambdaG_equivariant` (public exports).
- Decls with `sorry`: none. (File is sorry-free; header notes the upstream Teichmüller split `normCompat_eq_teichmuller_mul_principal` is now sorry-free in `Iwasawa/ResidueField.lean`.)
- `set_option`: none.
- Proofs >50 lines (OVER-50): none (count 0).
- Proofs 30–50 lines: none (count 0). Longest proof is `Col_eq_zero_of_torsion` at ≈14 lines.

Output path: /Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_IwasawaProof_Equivariance.md
