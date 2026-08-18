# Step 5 — Moral Duplication Detection: NagellLutz

Scope: within-project moral duplicates + duplicates of mathlib. Read from the
`/overview` inventory under `.mathlib-quality/overview/inventory/` plus the Lean
sources under `LutzNagell/`. No local build, so verdicts rest on inventory
signatures/proof-sketches, source heads, import wiring, and web confirmation of
the mathlib originals.

## Headline findings

The project carries **three large, deliberate duplication structures**:

1. **A `General*` (ℤ/ℚ) track vs a `PID*` (UFD / fraction-field) track.** Every
   `General*` declaration has a `PID*` twin with the *same* mathematical content
   and a *parallel* proof; the PID twin is the strict generalisation
   (`ℤ → R` a UFD/PID, `ℚ → K = Frac(R)`, integrality `∃ x₀:ℤ, ↑x₀=x` →
   `IsLocalization.IsInteger R x`). Specialising `R := ℤ, K := ℚ` recovers the
   General track verbatim. This is the dominant duplication in the project.

2. **`EllipticDivisibilitySequenceOriginal.lean` is a dead, near-identical
   sibling of `EllipticDivisibilitySequence.lean`.** Nothing imports `…Original`
   (`grep` finds zero importers); only the non-Original file is used (by
   `DivisionPolynomial.lean`). The non-Original file is a superset (161 vs 138
   decls; adds root-level `complEDS'`/`complEDS` and an `@[expose]`
   restructuring). Whole-file duplication.

3. **DUP-OF-MATHLIB by design.** Both EDS files and `DivisionPolynomial.lean`
   are explicit ports of mathlib originals (author byline *David Kurniadi
   Angdinata*, the mathlib author). `DivisionPolynomial.lean`'s own docstring
   says it "is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.
   DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence`
   instead of the mathlib version, to avoid name conflicts". The `normEDS` /
   `preNormEDS` / `IsEllDivSequence` core is verbatim mathlib
   (`Mathlib.NumberTheory.EllipticDivisibilitySequence`); the *additions*
   (`addMulSub`, `rel₄`, `net`, `complEDS₂`, `compl₂EDS`, the Stange-net API) are
   project-original and are the reason for the fork.

---

## Required pairwise table

Legend: **UNIFY** = collapse to one decl; **special-case** = keep both but the
narrow one should be `:= broad …` (a one-line corollary, not a re-proof);
**DUP-OF-MATHLIB** = exists in mathlib; **keep-both** = genuinely distinct.

### A. General-vs-PID track (the primary overlap)

| Decl A (General, ℤ/ℚ) | Decl B (PID, R/K) | Same statement? | Same proof? | Verdict |
| --- | --- | --- | --- | --- |
| `GeneralCurve.curveQ` | `PIDCurve.curveK` | Yes (mod ℤ/ℚ→R/K) — both `W.map (algebraMap …)` | Yes (defs) | special-case (`curveQ W := curveK ℤ ℚ W`) |
| `GeneralCurve.curveQ_a₁…a₆` | `PIDCurve.curveK_a₁…a₆` | Yes | Yes (`simp [curve…]`) | special-case of PID |
| `GeneralCurve.curveQ_equation_iff` | `PIDCurve.curveK_equation_iff` | Yes | Yes | special-case of PID |
| `GeneralDenominators.not_dvd_sum_of_not_dvd_cube` | `PIDDenominators.not_dvd_sum_of_not_dvd_cube` | Yes (ℤ→R, `Prime`) | Yes (prime divides cube ⇒ divides base) | **UNIFY** (PID one already `omit`s domain/UFD; literally same over any `CommRing`) |
| `GeneralDenominators.den_ne_prime_of_on_general_curve` | `PIDDenominators.den_not_prime_of_on_curve` | Yes (x.den=p ⇒ False vs den prime ⇒ False) | Parallel p-adic descent; PID via `clearing_denominators` + `den_no_simple_prime_factor` | special-case (derive ℚ from PID; General re-proves ~94 lines) |
| — | `PIDDenominators.clearing_denominators` | (no General twin; inlined in General) | — | keep-both (PID factored this out; General inlines the same `field_simp`/`linear_combination` step) |
| — | `PIDDenominators.den_no_simple_prime_factor_of_on_curve` | PID-only powerful-denominator core | — | keep-both (PID strengthens to q∤²den; General only states prime-den) |
| `GeneralIntegralMultiple.x_coord_nsmul_eq_general` | `PIDIntegralMultiple.x_coord_nsmul_eq` | Yes | Yes (Jacobian transport + `zsmul_eq_smulEval` + `X_eq_of_equiv`) | special-case of PID |
| `GeneralIntegralMultiple.monic_Φ_sub_smul_ΨSq_general` | `PIDIntegralMultiple.monic_Φ_sub_smul_ΨSq` | Yes | Yes (`Monic.sub_of_left` + degree calc) | **UNIFY** (identical; PID `c:R`, hypothesis `(n:R)≠0`) |
| `GeneralIntegralMultiple.x_integral_of_nsmul_x_integral_general` | `PIDIntegralMultiple.x_isInteger_of_nsmul_x_isInteger` | Yes | Yes (`isInteger_of_is_root_of_monic`) | special-case of PID |
| `GeneralIntegralMultiple.integral_of_nsmul_integral_general` | `PIDIntegralMultiple.isInteger_of_nsmul_isInteger` | Yes | Yes | special-case of PID |
| `GeneralPrimeOrder.y_integral_of_x_integral_on_general_curve` | `PIDPrimeOrder.y_isInteger_of_x_isInteger_on_curve` | Yes | Yes (monic quadratic in Y + `isInteger_of_is_root_of_monic`) | special-case of PID |
| `GeneralPrimeOrder.evalEval_ψ_eq_zero_of_zsmul_eq_zero_general` | `PIDPrimeOrder.evalEval_ψ_eq_zero_of_zsmul_eq_zero` | Yes | Yes (`zsmul_eq_smulEval`+`Z_eq_zero_of_equiv`) | **UNIFY** (PID `omit`s everything past `CommRing`-curve; works for any field K incl. ℚ) |
| `GeneralPrimeOrder.two_nsmul_eq_zero_of_ψ₂_eq_zero` | `PIDPrimeOrder.two_nsmul_eq_zero_of_ψ₂_eq_zero` | Yes (same name!) | Yes (`add_of_Y_eq`) | **UNIFY** (same name, same proof; PID `omit`s domain/UFD/fraction) |
| `GeneralPrimeOrder.x_integral_of_odd_prime_torsion_general` | `PIDPrimeOrder.x_isInteger_of_odd_prime_torsion_squarefree` | Mostly (PID adds `Squarefree (p:R)`, free over ℤ) | Parallel (`evalEval_ψ_odd`+`leadingCoeff_preΨ`+den bound) | special-case of PID (`Squarefree (p:ℤ)` holds for prime p) |
| `GeneralPrimeOrder.integrality_of_order_four_general` | `PIDPrimeOrder.integrality_of_order_four_squarefree` | Mostly (PID adds `Squarefree (2:R)`) | Parallel (`ψ_four` factor split) | special-case of PID |
| `GeneralPrimeOrder.prime_order_integrality_general` | `PIDPrimeOrder.prime_order_integrality_squarefree` | Mostly (+`Squarefree`) | Yes | special-case of PID |
| `GeneralPrimeOrder.bounded_den_of_order_two_general` (4x,8y∈ℤ) | `PIDPrimeOrder.den_dvd_of_order_two` (den∣4) | Morally yes (2-torsion den bound) | Parallel (`Ψ₂Sq` root + `den_dvd_of_is_root`) | special-case (PID states `den∣4`; General's `4x,8y∈ℤ` is the ℚ unfolding) |
| `GeneralMain.nsmul_eq_zero_affine_to_jac` | `PIDMain.nsmul_eq_zero_affine_to_jac` | Yes (same name!) | Yes (`toAffineAddEquiv` transport) | **UNIFY** (same name/proof; PID `omit`s all extra typeclasses) |
| `GeneralMain.exists_some_of_ne_zero` | `PIDMain.exists_some_of_ne_zero` | Yes (same name!) | Yes (`rcases` on `Affine.Point`) | **UNIFY** (same name/proof) |
| `GeneralMain.integrality_of_odd_prime_factor` | `PIDMain.integrality_of_odd_prime_factor` | Yes (same name!) | Yes (`k•P` order-p reduction) | special-case of PID |
| `GeneralMain.integrality_of_four_dvd_order` | `PIDMain.integrality_of_four_dvd_order` | Yes (same name!) | Yes (`k•P` order-4 reduction) | special-case of PID |
| `GeneralMain.lutz_nagell_integrality_general` | `PIDMain.lutz_nagell_integrality_pid` | Morally yes (PID disjunct `den∣4` vs General `4x,8y∈ℤ`) | Yes (prime-factor case split) | special-case of PID |

### B. Discriminant content duplicated `GeneralDiscriminant.lean` ↔ `PIDMain.lean`

The entire `κ₀²∣4Δ` discriminant argument is present in **both** files (ℤ/ℚ in
`GeneralDiscriminant`, R/K in `PIDMain`).

| Decl A (`GeneralDiscriminant`) | Decl B (`PIDMain`) | Same statement? | Same proof? | Verdict |
| --- | --- | --- | --- | --- |
| `kappa_sq_eq_Psi2Sq_eval_general` | `kappa_sq_eq_Psi2Sq` | Yes | Yes (unfold b's + `linear_combination/nlinarith 4*hcurve`) | **UNIFY** (PID `omit`s domain/PID/CharZero) |
| `h_sq_add_four_prePsi3_eq_general` | (inlined inside `kappa_sq_dvd_four_delta`) | Yes | Yes (`ring` after unfolding b's) | special-case (PID inlines; General names it) |
| `bezout_general` | `bezout_identity` | Yes | Yes (`ring` after unfolding b's,Δ) | **UNIFY** |
| `kappa_sq_dvd_four_delta_of_coord_identity` | `kappa_sq_dvd_four_delta` | Yes | Yes | **UNIFY** |
| `addOrderOf_ne_two_of_kappa_ne_zero` | `addOrderOf_ne_two_of_kappa_ne_zero` | Yes (same name!) | Yes (`evalEval_ψ_…`+ψ₂ vanish) | **UNIFY** |
| `Phi2_eval_eq` | `Phi2_eval_eq` | Yes (same name!) | Yes (`Φ 2 = X·Ψ₂Sq−Ψ₃`) | **UNIFY** |
| `PsiSq_two_eval_eq` | `PsiSq_two_eval_eq` | Yes (same name!) | Yes (`ΨSq_two`) | **UNIFY** |
| `Psi2Sq_eval_eq` | `Psi2Sq_eval_eq` | Yes (same name!) | Yes (`map_Ψ₂Sq`+`eval_map`) | **UNIFY** |
| `Psi3_eval_eq` | `Psi3_eval_eq` | Yes (same name!) | Yes (`map_Ψ₃`+`eval_map`) | **UNIFY** |
| `kappa_sq_dvd_four_Psi3` | `kappa_sq_dvd_four_Psi3_of_torsion` | Yes | Yes (`x_coord_nsmul_eq`+integrality split) | special-case of PID |
| `lutz_nagell_discriminant_general` | `lutz_nagell_pid_discriminant_of_torsion` | Yes | Yes | special-case of PID |
| `curveZ_equation_of_integral` | `PIDMain.curveR_equation_of_isInteger` | Yes | Yes (`curve…_equation_iff`+`exact_mod_cast`/injective) | special-case of PID |

### C. EDS file-vs-file (whole-file duplication)

| Decl A (`EllipticDivisibilitySequence`) | Decl B (`…Original`) | Same statement? | Same proof? | Verdict |
| --- | --- | --- | --- | --- |
| `addMulSub`, `rel₄`, `net`, `Rel₃`, `IsEllSequence`, `invarNum/Denom`, `HaveSameParity₄`, `avg₄`, `OddRec`, `EvenRec`, `dMin`, `cMin`, `Rel₄OfValid`, `relFin4`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS'/preNormEDS`, `complEDS₂`, `normEDS`, `compl₂EDS(Aux)`, `EllSequence.compl'/compl/complEDS`, `Param`, `universalNormEDS`, `redInvarNum/Denom` (+ ~120 lemmas) | identical-named decls in `…Original` | Yes | Yes | **UNIFY — delete `…Original`** (dead; non-Original is a superset) |
| root-level `complEDS'`, `complEDS`, `complEDSRec'`, `complEDSRec`, `map_complEDS_root` | also in `…Original` (top-level `complEDS'`/`complEDS` at 1419/1454) | Yes | Yes | keep in non-Original only |

### D. Duplicates of mathlib

| Project decl(s) | Mathlib original | Same statement? | Verdict |
| --- | --- | --- | --- |
| `EllipticDivisibilitySequence`: `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS'`, `preNormEDS`, `normEDS`, `normEDS_*` seed lemmas, `map_normEDS`, `map_preNormEDS` | `Mathlib.NumberTheory.EllipticDivisibilitySequence` (`IsEllDivSequence`, `preNormEDS'`, `preNormEDS`, `normEDS`, …) | Yes (verbatim port) | **DUP-OF-MATHLIB** (core); kept as a fork *only* to host the project-original `addMulSub`/`rel₄`/`net`/`complEDS₂`/`compl₂EDS` Stange-net API that mathlib lacks |
| `DivisionPolynomial.lean`: `ψ₂`, `Ψ₂Sq`, `Ψ₃`, `preΨ₄`, `preΨ'`, `preΨ`, `ΨSq`, `Φ`, `ψ`, `φ`, and the `map_*`/coordinate-ring `mk_*` lemmas | `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` | Yes (file docstring says "a copy of …Basic") | **DUP-OF-MATHLIB** (intentional fork to swap in local EDS import) |
| `DivisionPolynomialDegree.lean`: `natDegree_Φ`, `natDegree_ΨSq`, `leadingCoeff_Φ`, `leadingCoeff_preΨ`, … | `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` | Mostly (degree/leading-coeff facts) | DUP-OF-MATHLIB-leaning (re-derived against the local copy; verify exact-match before claiming) |
| `Universal.lean`: additions to `Affine.Point` / Jacobian | `Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point` (+ project additions) | Partial | keep-both (genuine additions; not a straight copy) |

### E. Within-file name clashes flagged in `…Original` (independent of the General/PID split)

| Decl A | Decl B | Same statement? | Verdict |
| --- | --- | --- | --- |
| `…Original.map_normEDS` (FunLike, ~1082) | `…Original.map_normEDS` (`@[simp]` `R→+*S`, ~1554) | Reused name, different class | keep-both but **rename** (clash) — moot once `…Original` is deleted |
| `…Original.map_complEDS` / `map_preNormEDS` / `map_preNormEDS'` (each appears twice) | their second copies | Reused names | rename / dedupe — moot once `…Original` is deleted |
| `…Original.complEDS` (`EllSequence.complEDS`, 1058) | `…Original.complEDS` (top-level, 1454) | **Different sequences, same name** | disambiguate — moot once `…Original` is deleted |

---

## Prose action list (priority order)

1. **Delete `LutzNagell/EllipticDivisibilitySequenceOriginal.lean`.** It is
   unimported (zero `grep` hits as an import), and the live
   `EllipticDivisibilitySequence.lean` is a strict superset (161 ≥ 138 decls,
   adds root-level `complEDS'`/`complEDS`). This is the single highest-value,
   lowest-risk action — removes ~1573 lines and a pile of duplicate-name /
   `erw` / stale-docstring debt in one stroke. (Sorry-check: neither EDS file
   has any `sorry`, so this is fleet-eligible once confirmed no other consumer.)

2. **Collapse the General track into the PID track.** The PID development
   (`PIDCurve`/`PIDDenominators`/`PIDIntegralMultiple`/`PIDPrimeOrder`/`PIDMain`)
   already proves everything the General track proves, over an arbitrary
   UFD/PID with fraction field, and the PID lemmas `omit` the extra typeclasses
   wherever ℚ doesn't need them. The General files
   (`GeneralCurve`/`GeneralDenominators`/`GeneralIntegralMultiple`/
   `GeneralPrimeOrder`/`GeneralMain`/`GeneralDiscriminant`) should be **rewritten
   as thin `R:=ℤ, K:=ℚ` specialisations**: each `*_general` becomes a one-line
   corollary `:= PID.* ℤ ℚ …` (plus a `Squarefree (p:ℤ)`/`(2:ℤ)`-for-prime
   discharge and the `IsInteger ℤ ℚ x ↔ ∃ x₀:ℤ, ↑x₀=x` /`den∣4 ↔ 4x∈ℤ`
   translations). This removes the parallel ~94-line `den_ne_prime…`,
   ~84-line `den_no_simple_prime…`-class, ~48-line `kappa_sq_dvd_four_Psi3`,
   and the whole `GeneralDiscriminant` re-proof. **Caveat for the fleet:** this
   *changes statements/structure*, so it is a `/generalise`-lane job (coordinator
   merges), not auto-merge; and it touches `Main.lean`'s façade
   (`lutz_nagell_integrality`, `lutz_nagell_discriminant`,
   `lutz_nagell`)— keep those public endpoints' *statements* fixed, only re-point
   their proofs.

3. **Straight UNIFY (identical statement+proof, no specialisation needed) — do
   these even if the bigger track-merge is deferred.** These pairs are the same
   over a plain `CommRing` and the PID copy already `omit`s the extra
   typeclasses, so a single home suffices:
   - `not_dvd_sum_of_not_dvd_cube` (General = PID, any `CommRing`)
   - `monic_Φ_sub_smul_ΨSq` (General = PID)
   - `evalEval_ψ_eq_zero_of_zsmul_eq_zero` (General = PID)
   - `two_nsmul_eq_zero_of_ψ₂_eq_zero` (same name both files)
   - `nsmul_eq_zero_affine_to_jac`, `exists_some_of_ne_zero` (same name both files)
   - the discriminant helper block duplicated verbatim between
     `GeneralDiscriminant` and `PIDMain`: `kappa_sq_eq_Psi2Sq`, `bezout_*`,
     `kappa_sq_dvd_four_delta(_of_coord_identity)`,
     `addOrderOf_ne_two_of_kappa_ne_zero`, `Phi2_eval_eq`, `PsiSq_two_eval_eq`,
     `Psi2Sq_eval_eq`, `Psi3_eval_eq` (8+ decls literally duplicated, several
     with the **same name** in both namespaces).

4. **Within `PIDMain` itself**, the four `Psi*_eval_eq` / `Phi2_eval_eq` /
   `PsiSq_two_eval_eq` helpers and `bezout_identity`/`kappa_sq_eq_Psi2Sq` are
   `omit`-stripped to pure ring facts — they belong in (or next to)
   `DivisionPolynomial`/`DivisionPolynomialDegree` as curve-level evaluation
   lemmas, shared by both the integrality and discriminant arguments, rather
   than re-stated per track.

5. **DUP-OF-MATHLIB (`DivisionPolynomial*`, EDS core) — do NOT delete; document.**
   These are intentional forks (to swap mathlib's EDS import for the local
   Stange-net-extended one and dodge `normEDS`/`complEDS` name collisions). The
   right long-term move is to upstream the project-original additions
   (`addMulSub`/`rel₄`/`net`/`complEDS₂`/`compl₂EDS` and the `ω`/`ψc`/`invar`
   family in `DivisionPolynomialOmega`) into mathlib so the forks can be dropped
   and the project can import mathlib directly. Until then, keep but add a
   one-line provenance note pointing at the mathlib source module on each forked
   file (the EDS file currently lacks the "copy of mathlib" banner that
   `DivisionPolynomial.lean` has). Flag for a human (`/mathlibable`), not for
   the auto-merge fleet.

### Counts
- General↔PID pairs examined: **~33** (curve 8, denominators 3+, integral-multiple 4, prime-order 7, main 5, discriminant 12).
- **UNIFY** (identical, merge to one): **~14** decls/pairs (table sections A+B straight-unify rows + same-name pairs).
- **special-case** (keep both, narrow := broad): **~22** pairs (the ℤ/ℚ specialisations of PID).
- **DUP-OF-MATHLIB**: **2 whole files** (`DivisionPolynomial.lean`, EDS core) + degree facts; provenance-document, don't delete.
- **Whole-file delete**: **1** (`EllipticDivisibilitySequenceOriginal.lean`, dead).
- `sorry` in any duplicate: **none** (all candidates are fleet-eligible on the sorry bar).
