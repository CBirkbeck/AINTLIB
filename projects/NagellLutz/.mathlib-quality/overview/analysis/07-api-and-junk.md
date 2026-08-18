# NagellLutz — Steps 7+8: API Design & Junk Identification

Scope: all 22 `.lean` files under `LutzNagell/`. Read-only analysis of the inventory
(`../inventory/*.md`) cross-checked against source. Two project deliverables exist as a
**twin-track**: a `ℤ/ℚ` "General" track (root-reachable) and a strictly-more-general "PID/UFD +
NumberField" track (orphaned from the root). This dominates the junk findings.

Architectural facts established (by import-graph inspection):
- Root `LutzNagell.lean` imports **only** `Basic`, `Main`, `GeneralMain`, `GeneralDiscriminant` →
  it pulls in the **General track only**. The PID track (`PIDCurve`/`PIDDenominators`/
  `PIDPrimeOrder`/`PIDIntegralMultiple`/`PIDMain`) is **imported by nothing outside itself**.
- The two tracks share **zero** code: no PID file imports a General file and vice-versa. They are
  parallel re-derivations of the same theorem skeleton.
- `EllipticDivisibilitySequenceOriginal.lean` (1572 lines) is **imported by nothing** — a dead
  fork of the live `EllipticDivisibilitySequence.lean` (1667 lines).

---

## Section A — API Improvements

API-completeness gaps, missing simp/instances, and repeated proof patterns a helper would collapse.
**14 suggestions.**

### A1. Curve base-change coefficient lemmas are triplicated; lift to a mathlib-level `map`/`baseChange` simp-set
`curveQ_a₁..a₆ + curveQ_equation_iff` (GeneralCurve), `curveK_a₁..a₆ + curveK_equation_iff`
(PIDCurve), and `shortCurveZ/Q_a₁..a₆ + shortCurveQ_equation_iff` (ShortWeierstrass) are three
copies of "the `aᵢ` of `W.map f` is `f W.aᵢ`, and the affine equation unfolds explicitly". Every
proof body is the identical `by simp [curve…]` / `equation_iff` + `simp`. **Suggested API:** mathlib
already has per-coefficient `map_a₁ …` simp lemmas on `WeierstrassCurve`; the project should rely on
those plus a single `WeierstrassCurve.Affine.map_equation_iff` helper (the explicit `y²+a₁xy+… `
form for `W.map f`) rather than re-proving per base ring. This would let all three `*_equation_iff`
become one lemma instantiated three ways. (Cross-ref junk J2.)

### A2. `evalEval_…` / `eval_…` bridge family wants a uniform "naturality + eval" combinator
EvalBridge's six lemmas (`evalEval_eq_of_mk_eq`, `evalEval_ψ_eq_evalEval_Ψ`, `evalEval_Ψ_sq_eq_eval_ΨSq`,
`evalEval_φ_eq_eval_Φ`, `evalEval_Ψ_odd`, `evalEval_ψ_odd`) and the `Psi2Sq_eval_eq`/`Psi3_eval_eq`/
`Phi2_eval_eq`/`PsiSq_two_eval_eq` closed-form-evaluation lemmas (duplicated verbatim in BOTH
GeneralDiscriminant and PIDMain) all follow the same recipe: `map_<P>` to push the base change,
`eval_map`, unfold the def, `eval₂_*` simp, `push_cast`/`ring`. **Suggested API:** a generic
`WeierstrassCurve.eval_map_<P>` lemma per division polynomial `P ∈ {Ψ₂Sq, Ψ₃, ΨSq, Φ}` giving the
closed form over any algebra, proved once. Removes 8 duplicated bodies (4 General + 4 PID).

### A3. `isInteger_of_is_root_of_monic` boilerplate ("rational root → integer") repeats ~5×
`y_integral_of_x_integral_on_general_curve`, `x_integral_of_nsmul_x_integral_general`,
`lutz_nagell_integrality_short`, plus the PID twins `y_isInteger_of_x_isInteger_on_curve`,
`x_isInteger_of_nsmul_x_isInteger`, `isInteger_of_root_squarefree_leading_coeff` all hand-build a
monic polynomial via `Monic.add_of_left`/`Monic.sub_of_left` + `monic_X_pow`/`degree_C_mul_X_le`/
`degree_add_eq_left_of_degree_lt` and then call `isInteger_of_is_root_of_monic`. **Suggested API:**
two reusable helpers — (i) `Monic.X_pow_add_C_mul_lt` style "monic quadratic/cubic from coefficient
list" builders, and (ii) `isInteger_of_root_of_monic_quadratic` specialised to `X²+bX+c`. The
y-from-x step in particular is a 12-line proof copied to both tracks for the same monic quadratic.

### A4. Add a doubling-x-coordinate lemma at the `WeierstrassCurve` level
`x_coord_nsmul_eq_general` (GeneralIntegralMultiple) and `x_coord_nsmul_eq` (PIDIntegralMultiple) are
the same theorem (`x'·ΨSq_n(x) = Φ_n(x)`) — the General one over `ℤ/ℚ`, the PID one over `R/K`. The
General proof is literally the PID proof with `omit`s dropped. **Suggested API:** keep only the PID
form (over a fraction ring); it specialises to `ℤ/ℚ` for free. This is the cleanest single
generalisation in the project. (Cross-ref junk J1.)

### A5. `monic_Φ_sub_smul_ΨSq` — keep one, over the general ring
`monic_Φ_sub_smul_ΨSq_general` (ℤ) and `monic_Φ_sub_smul_ΨSq` (R) prove `(Φ n - C c·ΨSq n).Monic`
identically. The general-ring version subsumes the ℤ one. Same comment for the whole
GeneralIntegralMultiple ↔ PIDIntegralMultiple file pair (4 theorems each, 1:1 correspondence).

### A6. `kappa_sq_eq_Psi2Sq`, `bezout_identity`, `kappa_sq_dvd_four_delta` — pure-ring duplicates across tracks
`kappa_sq_eq_Psi2Sq_eval_general` + `bezout_general` + `h_sq_add_four_prePsi3_eq_general` +
`kappa_sq_dvd_four_delta_of_coord_identity` (GeneralDiscriminant) are the same `ring`/`linear_combination`
identities as `kappa_sq_eq_Psi2Sq` + `bezout_identity` + `kappa_sq_dvd_four_delta` (PIDMain). These
are **base-ring-agnostic polynomial identities** (the PID versions carry
`omit [IsDomain] [IsPrincipalIdealRing] [CharZero]`, i.e. need only `CommRing`). They should live
once, in a `CommRing R` section, and be used by both tracks (or only the surviving track). 6+
duplicated proof bodies.

### A7. `not_dvd_sum_of_not_dvd_cube` is duplicated verbatim (ℤ vs `CommRing R`)
GeneralDenominators and PIDDenominators both define this prime-doesn't-divide-cube-plus-tail lemma;
the PID one is over a bare `CommRing` (`omit`s the domain/UFD assumptions). The ℤ copy is redundant.
Belongs in mathlib (`Prime.not_dvd_…`) or at least the project's `Common/`.

### A8. Missing `@[simp]` on the `den ∣ N` / `IsInteger` clearing lemma
`isInteger_mul_of_den_dvd` (PIDMain) — "den x ∣ n → IsInteger (n·x)" — is a clean, reusable
localization fact with no project-specific content. It is general enough for mathlib
(`IsFractionRing`/`IsLocalization` namespace) and would remove the bespoke `field_simp` denominator
clearing in `bounded_den_of_order_two_general` (which does the same thing inline over ℚ without the
lemma — an awkward workaround, see A9).

### A9. `bounded_den_of_order_two_general` does manual denominator-clearing a lemma would one-line
The General order-2 branch builds the witness `4x ∈ ℤ` by explicit `field_simp`/`push_cast`
construction of `α*k` (~33-line proof, the longest in GeneralPrimeOrder). The PID twin
(`den_dvd_of_order_two`) instead cleanly returns `den x ∣ 4` and lets `isInteger_mul_of_den_dvd`
(A8) clear it. The General proof should be replaced by the PID pattern. Awkward-workaround flag.

### A10. `Φ 2` / `ΨSq 2` closed forms belong next to mathlib's division-polynomial defs
`Phi2_eval_eq` (`Φ 2 = X·Ψ₂Sq − Ψ₃`) and `PsiSq_two_eval_eq` (`ΨSq 2 = Ψ₂Sq`) are stated twice
(General + PID) and are pure mathlib-shaped rewrites of `WeierstrassCurve.Φ`/`ΨSq_two`. Candidates
for `WeierstrassCurve.Φ_two_eq` / `ΨSq_two_eq` simp lemmas upstream.

### A11. EDS forks should be upstreamed, not maintained as project copies
`EllipticDivisibilitySequence.lean` carries mathlib's exact copyright/module-docstring (Angdinata)
and extends `Mathlib.NumberTheory.EllipticDivisibilitySequence` with a large new API
(`rel₄`/`net`/`Rel₃`/`complEDS`/`compl₂EDS`/`universalNormEDS`/`redInvar*`). This is the project's
genuine mathlib-completeness contribution. **Suggested action:** PR the additions to mathlib's EDS
file rather than carrying a 1667-line fork; the division-polynomial files then import upstream.

### A12. `DivisionPolynomialOmega` `ω` family is upstream-bound API
`invar`, `ψc`, `ω` and the `ω_neg`/`ω_zero`/`ω_one`/`map_ω`/`ψc_spec` lemmas complete mathlib's
`WeierstrassCurve` division-polynomial development (the missing 2nd-Jacobian-coordinate `ω`). These
have no Nagell-Lutz-specific content and should go to
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`. (API-completeness, not junk.)

### A13. Naming/`@[simp]` collisions inside EllipticDivisibilitySequenceOriginal
(Documented for completeness even though the whole file is junk J0.) `map_preNormEDS`, `map_normEDS`,
`map_complEDS`, `map_preNormEDS'` each declared **twice** (a `FunLike` version and a `RingHom`
`@[simp]` version); `complEDS`/`complEDS'` name two different sequences. If any of this file's API is
salvaged into the live file, these must be disambiguated. The live file appears to have already
fixed most of this (distinct `complEDS'(root)` etc.).

### A14. `expDegree`/`expCoeff` recursion scaffold (DivisionPolynomialDegree) — private, fine as-is
No change needed, but note `natDegree_coeff_preΨ'` (31 lines) and `natDegree_coeff_Φ_ofNat` (30
lines) are `/decompose-proof` candidates; the strong-induction `expDegree`/`expCoeff` engine is
clean and not duplicated. Listed so the consolidation pass doesn't mistake the leaf `leadingCoeff_*`
/ `*_ne_zero` exports (all "unused in file") for dead code — they feed the PrimeOrder rational-root
arguments in BOTH tracks (KEEP).

---

## Section B — Junk / Removable

Per-decl verdict with REMOVE / INLINE / REPLACE. Terminal public exports that are reachable
deliverables are marked **KEEP**. "Unused in file" was cross-checked against the inventory Used-by
fields and a project-wide grep before any REMOVE.

### B0. Genuinely dead (zero references project-wide)

| Decl | File | Verdict | Reason |
|---|---|---|---|
| **entire file `EllipticDivisibilitySequenceOriginal.lean` (1572 lines, 138 decls)** | — | **REMOVE** | Imported by nothing; superseded fork of the live `EllipticDivisibilitySequence.lean`. Single largest cleanup. Confirmed: `grep EllipticDivisibilitySequenceOriginal` → only its own file. |
| `addX_smul_one_smul_one_aux` | ZSMul.lean:252 | **REMOVE** | `private`, referenced exactly once (its own definition). The sibling `addX_smul_one_smul_one` uses `addX_smul_ring_identity`, not this. Dead. (Already flagged in inventory.) |
| `curveField_eq` | Universal.lean:175 | **REMOVE** | `curveField = pointedCurve := rfl`. Zero references outside its own line. The two are defeq so no consumer ever needs it. |
| `map_simp` macro | DivisionPolynomialOmega.lean:29 | **REMOVE** | Local tactic macro, never invoked in any proof body in the file (only `C_simp` is used). Dead scaffold. |

### B1. Twin-track redundancy — the dominant finding (General track vs PID track)

The PID track is a **strict generalization** of the General track (`R=ℤ, K=ℚ` recovers it) and is
where the project's headline `NumberField` deliverables live. The General track exists only because
it predates the PID generalization. **Once the tracks are unified, the entire General track below is
redundant** — every General theorem is the PID theorem at `R=ℤ`. Because the root aggregator
currently wires the General track (and *not* PID), this requires a deliberate re-pointing, so these
are flagged **REDUNDANT-ON-UNIFY** rather than blind REMOVE.

General-track files that are 1:1 generalized by a PID file (whole files redundant on unify):

| General file | PID counterpart | Notes |
|---|---|---|
| `GeneralCurve.lean` (8 decls) | `PIDCurve.lean` | `curveQ` = `curveK` at `ℤ/ℚ`. |
| `GeneralDenominators.lean` (2 decls) | `PIDDenominators.lean` | `den_ne_prime_of_on_general_curve` (~94-line ℚ proof) is subsumed by PID `den_not_prime_of_on_curve`; PID also factored out `clearing_denominators`. The General 94-line monolith is the un-refactored older copy. |
| `GeneralIntegralMultiple.lean` (4) | `PIDIntegralMultiple.lean` | Exact 1:1 (`x_coord_nsmul_eq_general`↔`x_coord_nsmul_eq`, `monic_Φ_sub_smul_ΨSq_general`↔`monic_Φ_sub_smul_ΨSq`, `x_integral…_general`↔`x_isInteger…`, `integral_of_nsmul…_general`↔`isInteger_of_nsmul…`). |
| `GeneralPrimeOrder.lean` (6) | `PIDPrimeOrder.lean` (7) | `y_integral…_general`↔`y_isInteger…`, `evalEval_ψ_eq_zero…_general`↔`…`, `two_nsmul_eq_zero_of_ψ₂_eq_zero`↔ (same name), `prime_order_integrality_general`↔`prime_order_integrality_squarefree`, `integrality_of_order_four_general`↔`…_squarefree`, `bounded_den_of_order_two_general`↔`den_dvd_of_order_two`. PID adds `isInteger_of_root_squarefree_leading_coeff`. |
| `GeneralMain.lean` (5) + `GeneralDiscriminant.lean` (10) | `PIDMain.lean` (22, incl. `NumberField.*`) | PID `lutz_nagell_integrality_pid` ↔ General `lutz_nagell_integrality_general`; PID `lutz_nagell_pid_discriminant_of_torsion` ↔ General `lutz_nagell_discriminant_general`; PID `lutz_nagell_cubicDisc_discriminant` ↔ Main `lutz_nagell_discriminant`/`lutz_nagell`. PID also has the powerful-denominator theorem the General track lacks. |

**Within-track duplicated pure-ring lemmas (redundant regardless of which track survives — same proof,
both tracks):** `not_dvd_sum_of_not_dvd_cube` (A7), `kappa_sq_eq_Psi2Sq(_eval_general)`,
`bezout(_general)/bezout_identity`, `h_sq_add_four_prePsi3_eq_general` + `kappa_sq_dvd_four_delta(_of_coord_identity)`,
`Phi2_eval_eq`, `PsiSq_two_eval_eq`, `Psi2Sq_eval_eq`, `Psi3_eval_eq`, `nsmul_eq_zero_affine_to_jac`,
`exists_some_of_ne_zero`, `addOrderOf_ne_two_of_kappa_ne_zero`. **REDUNDANT-ON-UNIFY → keep the PID
(general-ring) copy.**

**Recommended consolidation:** retain the PID track as the single source of truth; provide thin ℤ/ℚ
specialization wrappers ONLY for the root-reachable headline names (`lutz_nagell`,
`lutz_nagell_discriminant`, `lutz_nagell_integrality` in Main) by instantiating the PID/cubicDisc
theorems at `R=ℤ, K=ℚ`; delete `GeneralCurve`/`GeneralDenominators`/`GeneralIntegralMultiple`/
`GeneralPrimeOrder`/`GeneralMain`/`GeneralDiscriminant`. (This is a producer-side math decision — a
dev ticket, not a mechanical cleanup — because it re-points the root build.)

### B2. Thin wrappers (1–3 mathlib/project calls) — INLINE or KEEP-as-export

| Decl | File | Verdict | Reason |
|---|---|---|---|
| `lutz_nagell_integrality` (Main) | Main.lean | **KEEP** | 1-line delegation to `…_short`, but it is a **terminal root-reachable public export** (part of the headline `lutz_nagell`). Public API surface. |
| `kappa_sq_dvd_four_Psi3_of_integral` | PIDMain.lean | **INLINE** | 1-line `dvd_mul_of_dvd_right ⟨c, hPsi3⟩ 4`; **unused project-wide** (Used-by: none). Either INLINE at its single intended call site or REMOVE if no caller materializes. |
| `lutz_nagell_pid_discriminant` | PIDMain.lean | **REVIEW/REMOVE** | 2-line wrapper; "unused in file" AND no downstream consumer found (the `_of_torsion` variant is the one used by the `NumberField` export). Superseded by `lutz_nagell_pid_discriminant_of_torsion`. Likely dead intermediate. |
| `isEllSequence_ψ` | DivisionPolynomialOmega.lean | **INLINE** | `:= IsEllSequence.normEDS` (pure mathlib re-export); unused project-wide. Inline the mathlib lemma at use sites or drop. |
| `C_Ψ₃_eq` | DivisionPolynomialOmega.lean | **REVIEW** | "unused in file" and no cross-file consumer surfaced; a standalone `simp_rw;C_simp;ring` identity. Confirm a downstream user exists, else REMOVE. |
| `NumberField.lutz_nagell_number_field` / `den_powerful_number_field` / `…_discriminant` / `…_cubicDisc_discriminant` | PIDMain.lean | **KEEP** | 1-line `R := 𝓞 K` specializations, but these are the **project's terminal deliverables** (class-number-1 number-field Nagell-Lutz). Terminal public exports — KEEP even though "unused in file" and currently orphaned from the root aggregator (see note). |

### B3. False-positive "unused in file" — KEEP (verified cross-file consumers)

These appear as "unused in file" in the inventory but a project-wide grep confirms cross-file use,
so they are intended public API — **KEEP**:

- `Universal.lean`: `some_eq_some_iff` (→ ZSMul:363), `Poly.two_ne_zero` (→ DivisionPolynomialOmega:119),
  `curvePoly` (→ ZSMul:437+), `Jacobian.point` (→ ZSMul:402+), `polyEval_apply` (→ ZSMul:89+),
  `curveRing_map_ringEval` (→ ZSMul:574+), `Field.two_ne_zero` (→ ZSMul:369), `CommRing Poly`
  instance + `IsElliptic` instance (used by elaboration). All KEEP.
- All `curveQ_a*`/`curveK_a*`/`shortCurve*_a*`/`*_equation_iff`/`*_delta` coefficient + equation
  lemmas (GeneralCurve/PIDCurve/ShortWeierstrass): `@[simp]`/rewriting API consumed by the PrimeOrder
  and Main files of their track. KEEP (modulo whole-track removal in B1).
- All `leadingCoeff_*` and `*_ne_zero` terminal lemmas (DivisionPolynomialDegree): feed the
  rational-root denominator bounds in both PrimeOrder files. KEEP.
- EvalBridge `evalEval_Ψ_sq_eq_eval_ΨSq`, `evalEval_φ_eq_eval_Φ`, `evalEval_ψ_odd`: the doubling/
  prime-order bridges consumed by IntegralMultiple + PrimeOrder. KEEP.
- DivisionPolynomial/EDS(live) "unused in file" base-value/`map_*`/`baseChange_*` lemmas: library
  boundary API for ZSMul / EvalBridge / DivisionPolynomialDegree. KEEP.
- `hello` (Basic.lean): template stub `def hello := "world"`. **REMOVE** — genuine dead template
  placeholder, zero content, but harmless; trivial cleanup. (Not API, listed here only because the
  inventory flags it; it is the one true "unused" leaf that is safe to delete outright.)

### B4. Long proofs flagged for `/decompose-proof` (not junk, noted for the decompose lane)
`kappa_sq_dvd_four_Psi3` (GeneralDiscriminant, ~58 lines, OVER-50) ·
`den_ne_prime_of_on_general_curve` (GeneralDenominators, ~94, OVER-50) ·
`den_no_simple_prime_factor_of_on_curve` (PIDDenominators, ~84, OVER-50) ·
`kappa_sq_dvd_four_Psi3_of_torsion` (PIDMain, ~37) · `lutz_nagell_cubicDisc_discriminant` (PIDMain, ~43) ·
`bounded_den_of_order_two_general` (~33) · `natDegree_coeff_preΨ'` (31) · `natDegree_coeff_Φ_ofNat` (30) ·
`Affine.zsmul_point_eq_smulX_smulY` (~38) · `zsmul_eq_smulEval` (~33) · `rel₄_of_anti_oddRec_evenRec`
(EDS, ~30). If the General track is removed per B1, the three OVER-50 General proofs vanish with it.

---

## Headline summary

- **Biggest win:** delete `EllipticDivisibilitySequenceOriginal.lean` (1572 dead lines).
- **Biggest structural win:** unify the General and PID tracks onto the PID (general-ring) versions —
  collapses ~6 files / ~35 theorems of near-verbatim ℤ/ℚ duplication; requires re-pointing the root
  aggregator (a producer dev ticket).
- **Upstream-bound (not junk):** the EDS fork's `rel₄`/`net`/`complEDS` extensions and the `ω`
  division-polynomial family belong in mathlib.
- **4 genuinely-dead decls/files** (`…Original.lean`, `addX_smul_one_smul_one_aux`, `curveField_eq`,
  `map_simp` macro) + `hello` stub are safe immediate REMOVEs.
