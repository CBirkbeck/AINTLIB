# Inventory: PadicLFunctions/KubotaLeopoldt/ZetaValuesComplex.lean

File purpose: the "complex bridge" for `zetaNeg`. Quarantined in its own file so the p-adic development does not transitively import complex analysis. Identifies the rational value `zetaNeg k` with mathlib's complex Riemann zeta at `−k`.

Imports: `PadicLFunctions.KubotaLeopoldt.ZetaValues`, `Mathlib.NumberTheory.LSeries.HurwitzZetaValues`.

---

### theorem zetaNeg_eq_riemannZeta
- Type: `(k : ℕ) : ((zetaNeg k : ℚ) : ℂ) = riemannZeta (-(k : ℂ))`
- What: States that the project's rational special value `zetaNeg k` (the value of the zeta function at `−k`, defined via Bernoulli numbers as `(−1)^k · B_{k+1}/(k+1)`), when coerced into `ℂ`, equals mathlib's complex Riemann zeta function evaluated at the negative integer `−k`.
- How: Rewrites the RHS with mathlib's `riemannZeta_neg_nat_eq_bernoulli` (which expresses `ζ(−k)` via Bernoulli numbers) and unfolds the project definition `zetaNeg`; then closes the resulting numeric identity between the two Bernoulli-number expressions by `push_cast` followed by `ring`.
- Hypotheses: `k : ℕ` (a natural number); no further conditions.
- Uses from project: [`zetaNeg`]
- Used by: unused in file
- Visibility: public
- Lines: 18–22 (proof 3 lines)
- Notes: none

---

## File Summary

- Total decls: 1 (defs: 0 / lemmas+theorems: 1 / instances: 0)
- Key API (used by ≥3 in file): none
- Unused (in file): `zetaNeg_eq_riemannZeta`
- Decls with `sorry`: none
- `set_option`: none
- Proofs >50 lines (OVER-50): none (count: 0)
- Proofs 30–50 lines (long): none (count: 0)
