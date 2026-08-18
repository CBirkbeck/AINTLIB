# Inventory: PadicLFunctions/IwasawaProof/LogDerivative.lean

File namespace: `PadicLFunctions.Coleman`. Variable `(p : ℕ) [hp : Fact p.Prime]` in scope throughout.
Subject: the logarithmic-derivative / Coleman–Coates–Wiles short exact sequence
`0 → μ_{p−1} → (ℤ_p⟦T⟧^×)^{𝒩=id} →[Δ] ℤ_p⟦T⟧^{ψ=id} → 0` (RJW §12.2.1).

---

### def psiIdSeries
- Type: `def psiIdSeries : Submodule ℤ_[p] (PowerSeries ℤ_[p])`
- What: The `ψ = id` subspace `{F | psiSeries p F = F}` of `ℤ_p⟦T⟧`, i.e. RJW's `ℤ_p⟦T⟧^{ψ=id}`, as a `Submodule`.
- How: Carrier is the fixed-point set of `psiSeries`; closure under `+`, `0`, `•` is checked from additivity (`psiSeries_add_padicInt`) and `C`-scaling (`psiSeries_C_mul_padicInt`), with `smul_eq_C_mul`.
- Hypotheses: none beyond ambient `[Fact p.Prime]`.
- Uses from project: [`psiSeries`, `psiSeries_add_padicInt`, `psiSeries_C_mul_padicInt`]
- Used by: `dlog_mem_psiIdSeries`, `dlog_surjective_onto_psiId`, `one_sub_phi_psiId_mem_psiZero`, `exists_one_sub_phi_eq`
- Visibility: public
- Lines: 62–74 (proof-fields ~9 lines)
- Notes: none

### def psiZeroSeries
- Type: `def psiZeroSeries : Submodule ℤ_[p] (PowerSeries ℤ_[p])`
- What: The `ψ = 0` subspace `{F | psiSeries p F = 0}` of `ℤ_p⟦T⟧` (RJW `ℤ_p⟦T⟧^{ψ=0}`) as a `Submodule`.
- How: Same pattern as `psiIdSeries`: kernel of `psiSeries`, with closure from additivity and `C`-scaling.
- Hypotheses: none beyond ambient.
- Uses from project: [`psiSeries`, `psiSeries_add_padicInt`, `psiSeries_C_mul_padicInt`]
- Used by: `one_sub_phi_psiId_mem_psiZero`, `exists_one_sub_phi_eq`
- Visibility: public
- Lines: 76–89 (proof-fields ~11 lines)
- Notes: none

### theorem psiSeries_sub
- Type: `theorem psiSeries_sub (F G : PowerSeries ℤ_[p]) : psiSeries p (F - G) = psiSeries p F - psiSeries p G`
- What: `ψ` is subtractive over `ℤ_[p]`.
- How: Apply additivity `psiSeries_add_padicInt` to `(F − G) + G`, cancel via `sub_add_cancel`, then `ring`.
- Hypotheses: none.
- Uses from project: [`psiSeries`, `psiSeries_add_padicInt`]
- Used by: `dlog_surjective_onto_psiId` (via `hpsib`), `exists_normOp_dlog_modEq`, `exists_approx_step`, `one_sub_phi_psiId_mem_psiZero`, `exists_one_sub_phi_eq`
- Visibility: public
- Lines: 91–96 (proof 3 lines)
- Notes: none

### theorem del_phiHom
- Type: `theorem del_phiHom (f) : PadicMeasure.del p (phiHom p f) = (p : PowerSeries ℤ_[p]) * phiHom p (PadicMeasure.del p f)`
- What: The commutation `Δ ∘ φ = p · φ ∘ Δ` on power series in the additive `del = ∂` form, stated for the ring-hom `phiHom`.
- How: Unfold `phiHom`/`del`, rewrite by `one_add_mul_derivative_phiSeries`, `smul_eq_C_mul`, `map_natCast`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.del`, `phiHom`, `phiHom_apply`, `one_add_mul_derivative_phiSeries`]
- Used by: unused in file (the `del`-shaped variant `del_phiSeries` is used instead)
- Visibility: public
- Lines: 98–106 (proof 3 lines)
- Notes: none

### theorem derivation_finset_prod
- Type: `private theorem derivation_finset_prod {R} [CommRing R] (D : Derivation R (PowerSeries R) (PowerSeries R)) {ι} [DecidableEq ι] (s : Finset ι) (g : ι → PowerSeries R) : D (∏ i ∈ s, g i) = ∑ i ∈ s, (∏ j ∈ s.erase i, g j) • D (g i)`
- What: The Leibniz product rule over a finite set for a derivation `D` on power series.
- How: `Finset.induction` on `s`; insert step uses `D.leibniz`, `Finset.erase_insert`, `Finset.prod_insert`, `mul_smul` to re-associate the new factor.
- Hypotheses: `D` a derivation; `ι` with decidable equality.
- Uses from project: []
- Used by: `derivation_det`
- Visibility: private
- Lines: 117–133 (proof ~11 lines)
- Notes: long-ish (~11 lines); hinges on `Derivation.leibniz`. Under 30.

### theorem derivation_det
- Type: `private theorem derivation_det {R} [CommRing R] {n} (D) (M : Matrix (Fin n) (Fin n) (PowerSeries R)) : D (M.det) = ∑ i, (M.updateRow i (fun j => D (M i j))).det`
- What: Jacobi's formula (row form): the derivative of a determinant is the sum of determinants with one row differentiated.
- How: Expand `Matrix.det_apply'`, apply `derivation_finset_prod` to each Leibniz term `ε(σ)∏ M_{σi,i}`, then reorganise by the substitution `i ↦ σ i` using `Equiv.sum_comp`, `Finset.sum_comm`, `Matrix.updateRow_self`/`updateRow_ne`.
- Hypotheses: `D` a derivation; `M` square over `PowerSeries R`.
- Uses from project: []
- Used by: `del_det_eq_smul_trace`
- Visibility: private
- Lines: 135–175 (proof ~32 lines)
- Notes: long(30-50) — proof body ~32 lines; hinges on `derivation_finset_prod` and `Matrix.det_apply'`.

### theorem det_updateRow_eq_sum_adjugate
- Type: `private theorem det_updateRow_eq_sum_adjugate {R} [CommRing R] {n} (M) (i : Fin n) (v : Fin n → R) : (M.updateRow i v).det = ∑ j, v j * Matrix.adjugate M j i`
- What: Cofactor/Cramer expansion of `det` along a replaced row.
- How: Transpose to a column update, rewrite via `Matrix.cramer_apply` + `cramer_eq_adjugate_mulVec`, unfold `mulVec`/`dotProduct`, re-commute with `adjugate_transpose`.
- Hypotheses: `M` square over a commutative ring.
- Uses from project: []
- Used by: `del_det_eq_smul_trace`
- Visibility: private
- Lines: 177–185 (proof ~4 lines)
- Notes: none

### theorem del_mul
- Type: `private theorem del_mul (a b) : PadicMeasure.del p (a * b) = PadicMeasure.del p a * b + a * PadicMeasure.del p b`
- What: Leibniz rule for `Δ = del` (`= (1+T)∂`).
- How: Unfold `del`, use `derivativeFun_mul`, `smul_eq_mul`, then `ring`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.del`, `derivativeFun_mul`]
- Used by: `digitMatrix_del`
- Visibility: private
- Lines: 199–202 (proof 2 lines)
- Notes: none

### theorem del_one_add_X_pow
- Type: `private theorem del_one_add_X_pow (j : ℕ) : PadicMeasure.del p ((1 + X) ^ j) = (j : PowerSeries ℤ_[p]) * (1 + X) ^ j`
- What: `Δ((1+T)^j) = j·(1+T)^j`.
- How: Compute `∂((1+X)^j)` by `derivative_pow` with `∂(1+X)=1`, then case on `j` and `push_cast; ring`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.del`, `derivativeFun`, `derivativeFun_add`, `derivativeFun_one`]
- Used by: `digitMatrix_del`, `coeff_one_one_add_X_pow`
- Visibility: private
- Lines: 204–217 (proof ~10 lines)
- Notes: none

### theorem del_phiSeries
- Type: `private theorem del_phiSeries (g) : PadicMeasure.del p (phiSeries p g) = (p : PowerSeries ℤ_[p]) * phiSeries p (PadicMeasure.del p g)`
- What: `Δ(φg) = p·φ(Δg)` in the `del = ∂` form (the `del`-shaped `del_phiHom`).
- How: Unfold `del`, rewrite by `one_add_mul_derivative_phiSeries`, `smul_eq_C_mul`, `map_natCast`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.del`, `phiSeries`, `one_add_mul_derivative_phiSeries`]
- Used by: `digitMatrix_del`
- Visibility: private
- Lines: 219–224 (proof 2 lines)
- Notes: none

### theorem del_sum
- Type: `private theorem del_sum {ι} (s : Finset ι) (g : ι → PowerSeries ℤ_[p]) : PadicMeasure.del p (∑ i ∈ s, g i) = ∑ i ∈ s, PadicMeasure.del p (g i)`
- What: `Δ` commutes with finite sums.
- How: `derivativeFun` is additive (`map_sum` of `PowerSeries.derivative`), then `Finset.mul_sum`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.del`, `derivativeFun`]
- Used by: `digitMatrix_del`
- Visibility: private
- Lines: 226–232 (proof ~4 lines)
- Notes: none

### theorem phiSeries_C_padicInt
- Type: `private theorem phiSeries_C_padicInt (a : ℤ_[p]) : phiSeries p (PowerSeries.C a) = PowerSeries.C a`
- What: `φ` fixes constants over `ℤ_[p]`.
- How: Unfold `phiSeries`, apply `PowerSeries.subst_C`.
- Hypotheses: none.
- Uses from project: [`phiSeries`]
- Used by: `digitMatrix_del`
- Visibility: private
- Lines: 234–237 (proof 1 line)
- Notes: none

### theorem phiSeries_add'
- Type: `private theorem phiSeries_add' (a b) : phiSeries p (a + b) = phiSeries p a + phiSeries p b`
- What: `φ` is additive over `ℤ_[p]`.
- How: Transport through the ring-hom `phiHom` via `phiHom_apply` and `map_add`.
- Hypotheses: none.
- Uses from project: [`phiSeries`, `phiHom_apply`]
- Used by: `digitMatrix_del`
- Visibility: private
- Lines: 239–241 (proof 1 line)
- Notes: none

### theorem phiSeries_mul'
- Type: `private theorem phiSeries_mul' (a b) : phiSeries p (a * b) = phiSeries p a * phiSeries p b`
- What: `φ` is multiplicative over `ℤ_[p]`.
- How: Transport through `phiHom` via `phiHom_apply` and `map_mul`.
- Hypotheses: none.
- Uses from project: [`phiSeries`, `phiHom_apply`]
- Used by: `digitMatrix_del`
- Visibility: private
- Lines: 243–245 (proof 1 line)
- Notes: none

### theorem digitMatrix_del
- Type: `private theorem digitMatrix_del (f) (i j : Fin p) : (digitMatrix (PadicMeasure.del p f)) i j = ((i : ℤ_[p]) - (j : ℤ_[p])) • (digitMatrix f) i j + (p : PowerSeries ℤ_[p]) * PadicMeasure.del p ((digitMatrix f) i j)`
- What: **Identity K** — the digit-matrix derivative identity: `(digitMatrix(Δf))_{ij} = (i−j)·M_{ij} + p·Δ(M_{ij})` where `M = digitMatrix f`.
- How: Differentiate the column-digit identity `digitMatrix_col_isDigitDecomp` (`f·(1+T)^j = Σ_i (1+T)^i φ(M_{ij})`); the LHS Leibniz-expands (`del_mul`, `del_one_add_X_pow`, `del_sum`), each summand uses `del_phiSeries`/`phiSeries_add'`/`phiSeries_mul'`; then digit uniqueness `existsUnique_digits_padicInt … .unique` equates the two digit families. Hinges on `digitMatrix_col_isDigitDecomp` and `existsUnique_digits_padicInt`.
- Hypotheses: none (general `f`, indices `i,j : Fin p`).
- Uses from project: [`digitMatrix`, `PadicMeasure.del`, `digitMatrix_col_isDigitDecomp`, `existsUnique_digits_padicInt`, `IsDigitDecomp`, `phiSeries`, `del_mul`, `del_one_add_X_pow`, `del_sum`, `del_phiSeries`, `phiSeries_add'`, `phiSeries_mul'`, `phiSeries_C_padicInt`, `phiHom_apply`]
- Used by: `dlog_mem_psiIdSeries`
- Visibility: private
- Lines: 247–306 (proof ~50 lines)
- Notes: OVER-50 borderline — proof body ~50 lines (252→306). Flag for /decompose-proof. Hinges on digit-decomposition uniqueness.

### theorem del_row_smul
- Type: `private theorem del_row_smul {n} (M) (i : Fin n) : (1 + X) * (M.updateRow i (fun j => PowerSeries.derivative ℤ_[p] (M i j))).det = (M.updateRow i (fun j => PadicMeasure.del p (M i j))).det`
- What: Pulling the `(1+T)` of `Δ = (1+T)∂` into a differentiated row of a determinant.
- How: `Matrix.det_updateRow_smul` (scalar multiple of a row scales the det), then `rfl` to identify `Δ = (1+T)·∂` rowwise.
- Hypotheses: `M` square over `PowerSeries ℤ_[p]`.
- Uses from project: [`PadicMeasure.del`]
- Used by: `del_det_eq_smul_trace`
- Visibility: private
- Lines: 308–315 (proof 1 line)
- Notes: none

### theorem adjugate_eq_det_smul_inv
- Type: `private theorem adjugate_eq_det_smul_inv {n} (M N) (hNM : N * M = 1) : Matrix.adjugate M = M.det • N`
- What: For a two-sided inverse `N` of `M`, `adj M = det M • N`.
- How: From `adjugate_mul` (`adj M · M = det M • 1`); multiply by `M·N=1` (using `mul_eq_one_comm`) and cancel.
- Hypotheses: `N·M = 1` (with the matrices square over `PowerSeries ℤ_[p]`).
- Uses from project: []
- Used by: `del_det_eq_smul_trace`
- Visibility: private
- Lines: 317–326 (proof ~5 lines)
- Notes: none

### theorem del_det_eq_smul_trace
- Type: `private theorem del_det_eq_smul_trace {n} (M N) (hNM : N * M = 1) : PadicMeasure.del p (M.det) = M.det • Matrix.trace ((M.map (PadicMeasure.del p)) * N)`
- What: Jacobi in trace form: `Δ(det M) = det M • tr((M.map Δ)·N)` when `N·M = 1`.
- How: From `derivation_det`, pull `(1+T)` into each row (`del_row_smul`), expand each `det(updateRow)` by `det_updateRow_eq_sum_adjugate`, substitute `adjugate_eq_det_smul_inv`, then reduce to `Matrix.trace` via `mul_apply`/`map_apply` and `ring`.
- Hypotheses: `N·M = 1`.
- Uses from project: [`PadicMeasure.del`, `derivation_det`, `del_row_smul`, `det_updateRow_eq_sum_adjugate`, `adjugate_eq_det_smul_inv`, `derivativeFun`]
- Used by: `dlog_mem_psiIdSeries`
- Visibility: private
- Lines: 328–345 (proof ~10 lines)
- Notes: none

### theorem digitMatrix_inverse_mul'
- Type: `private theorem digitMatrix_inverse_mul' {f} (hf : IsUnit f) : digitMatrix (Ring.inverse f) * digitMatrix f = 1`
- What: `digitMatrix(f⁻¹)·digitMatrix(f) = 1` for a unit `f` (digitMatrix is a ring hom).
- How: `digitMatrix_mul` (multiplicativity), `Ring.inverse_mul_cancel`, `digitMatrix_one`.
- Hypotheses: `f` a unit.
- Uses from project: [`digitMatrix`, `digitMatrix_mul`, `digitMatrix_one`]
- Used by: `dlog_mem_psiIdSeries`
- Visibility: private
- Lines: 347–350 (proof 1 line)
- Notes: none

### theorem trace_D_N_zero
- Type: `private theorem trace_D_N_zero {n} (M N) (hMN : M * N = 1) (hNM : N * M = 1) : ∑ i, ∑ k, ((i : ℤ_[p]) - (k : ℤ_[p])) • (M i k * N k i) = 0`
- What: The off-diagonal trace of identity K vanishes: `∑_{i,k} (i−k)•(M_{ik} N_{ki}) = 0` when `M,N` are mutually inverse.
- How: Split `sub_smul`; the `∑ i·(MN)_{ii}` half equals `∑ i·1` (from `M*N=1`, `Matrix.one_apply_eq`) and the `∑ k·(NM)_{kk}` half equals `∑ k·1` (after `Finset.sum_comm`), so the difference cancels (`sub_self`).
- Hypotheses: `M·N = 1` and `N·M = 1`.
- Uses from project: []
- Used by: `dlog_mem_psiIdSeries`
- Visibility: private
- Lines: 352–373 (proof ~16 lines)
- Notes: long-ish (~16 lines); hinges on `Matrix.mul_apply` + `Matrix.one_apply_eq`. Under 30.

### theorem mul_p_cancel
- Type: `private theorem mul_p_cancel {a b} (h : (p : PowerSeries ℤ_[p]) * a = (p : PowerSeries ℤ_[p]) * b) : a = b`
- What: `(p : ℤ_p⟦T⟧)` is a regular (cancellable) element.
- How: `(p : ℤ_p⟦T⟧) = C(p) ≠ 0` (via `C_injective` + `Nat.cast_ne_zero`), then `mul_left_cancel₀`.
- Hypotheses: `p·a = p·b`.
- Uses from project: []
- Used by: `dlog_mem_psiIdSeries`
- Visibility: private
- Lines: 375–381 (proof ~4 lines)
- Notes: none

### theorem dlog_mem_psiIdSeries
- Type: `theorem dlog_mem_psiIdSeries {f} (hf : IsUnit f) (hN : normOp f = f) : dlog p f ∈ psiIdSeries p`
- What: **RJW lem:log der 1** — `Δ(𝒲) ⊆ ℤ_p⟦T⟧^{ψ=id}`: the logarithmic derivative of an `𝒩`-fixed unit is `ψ`-fixed.
- How: Determinant/Jacobi route replacing RJW's `μ_p`-product. With `M = digitMatrix f`, `N = digitMatrix(f⁻¹)`, hypothesis `𝒩f=f` gives `f = det M` (`normOp_eq_det`). Then `digitMatrix(dlog f) = digitMatrix(Δf)·N`; by identity K (`digitMatrix_del`) its trace splits as `tr(D·N) + p·tr(ΔM·N)`, the first vanishing (`trace_D_N_zero`); Jacobi (`del_det_eq_smul_trace`) gives `tr(ΔM·N) = f⁻¹·Δf = dlog f`; `trace_digitMatrix` says `tr(digitMatrix·) = p·ψ(·)`; cancel `p` (`mul_p_cancel`). Hinges on `digitMatrix_del`, `del_det_eq_smul_trace`, `trace_digitMatrix`, `trace_D_N_zero`.
- Hypotheses: `f` a unit; `f` is `𝒩`-fixed (`normOp f = f`).
- Uses from project: [`dlog`, `psiSeries`, `psiIdSeries`, `digitMatrix`, `digitMatrix_mul`, `digitMatrix_one`, `digitMatrix_del`, `digitMatrix_inverse_mul'`, `normOp`, `normOp_eq_det`, `PadicMeasure.del`, `trace_digitMatrix`, `trace_D_N_zero`, `del_det_eq_smul_trace`, `mul_p_cancel`]
- Used by: `exists_normOp_dlog_modEq`, `exists_approx_step`
- Visibility: public
- Lines: 383–440 (proof ~42 lines)
- Notes: long(30-50) — proof body ~42 lines (400→440). Flag for /decompose-proof. Central API.

### theorem modEqPow_iff_map_quot
- Type: `theorem modEqPow_iff_map_quot {k} {f g} : ModEqPow p k f g ↔ map (Ideal.Quotient.mk (Ideal.span {(p:ℤ_[p])^k})) f = map (…) g`
- What: `f ≡ g mod p^k` iff `f, g` agree after coefficientwise reduction mod `p^k` (via the quotient ring hom).
- How: Unfold `ModEqPow` + `PowerSeries.ext_iff`, then per-coefficient: `coeff_map`, `sub_eq_zero`, `RingHom.mem_ker`, `Ideal.mk_ker`, `Ideal.mem_span_singleton`.
- Hypotheses: none.
- Uses from project: [`ModEqPow`]
- Used by: `digitMatrix_entry_modEq`, `normOp_modEq_of_modEq`
- Visibility: public
- Lines: 453–460 (proof ~5 lines)
- Notes: none

### theorem digitMatrix_entry_modEq
- Type: `theorem digitMatrix_entry_modEq {k} {a b} (h : ModEqPow p k a b) (i j : Fin p) : ModEqPow p k ((digitMatrix a) i j) ((digitMatrix b) i j)`
- What: `digitMatrix` respects `ModEqPow` entrywise.
- How: Write `a = b + C(p^k)·q` (`modEqPow_iff_exists_C_mul`); `digitMatrix` is a ring hom so `digitMatrix a = digitMatrix b + C(p^k)•digitMatrix q` (`digitMatrix_add`/`_mul`/`_C`), read off the `(i,j)` entry, conclude via `modEqPow_iff_exists_C_mul`.
- Hypotheses: `a ≡ b mod p^k`.
- Uses from project: [`ModEqPow`, `modEqPow_iff_exists_C_mul`, `digitMatrix`, `digitMatrix_add`, `digitMatrix_mul`, `digitMatrix_C`]
- Used by: `normOp_modEq_of_modEq`
- Visibility: public
- Lines: 462–476 (proof ~10 lines)
- Notes: none

### theorem normOp_modEq_of_modEq
- Type: `theorem normOp_modEq_of_modEq {k} {a b} (h : ModEqPow p k a b) : ModEqPow p k (normOp a) (normOp b)`
- What: **`𝒩` respects `ModEqPow`** — the mod-`p^k` continuity driving lem:A mod p.
- How: Via `normOp_eq_det` + `RingHom.map_det`: the determinant of entrywise-congruent matrices is congruent. Reduces both sides through the quotient hom (`modEqPow_iff_map_quot`), uses `Matrix.ext` + `digitMatrix_entry_modEq` on entries.
- Hypotheses: `a ≡ b mod p^k`.
- Uses from project: [`ModEqPow`, `modEqPow_iff_map_quot`, `normOp`, `normOp_eq_det`, `digitMatrix`, `digitMatrix_entry_modEq`]
- Used by: `exists_normOp_fixed_lift`
- Visibility: public
- Lines: 478–492 (proof ~10 lines)
- Notes: none

### theorem isClosed_dvd_pow
- Type: `theorem isClosed_dvd_pow (k : ℕ) : IsClosed {x : ℤ_[p] | (p : ℤ_[p]) ^ k ∣ x}`
- What: The divisibility set `{x | p^k ∣ x}` is closed in `ℤ_[p]` (it is the norm ball `‖·‖ ≤ p^{−k}`).
- How: Rewrite the set as the preimage of `Set.Iic (p^{−k})` under `‖·‖` (using `PadicInt.norm_le_pow_iff_mem_span_pow`), then `isClosed_Iic.preimage continuous_norm`.
- Hypotheses: none.
- Uses from project: []
- Used by: `modEqPow_of_tendsto`
- Visibility: public
- Lines: 494–502 (proof ~6 lines)
- Notes: none

### theorem modEqPow_of_tendsto
- Type: `theorem modEqPow_of_tendsto {k} {gj : ℕ → …} {g c} (hconv : Tendsto gj atTop (nhds g)) (hmod : ∀ᶠ j in atTop, ModEqPow p k (gj j) c) : ModEqPow p k g c`
- What: `ModEqPow p k · c` passes through coefficientwise limits: a limit of series eventually `≡ c mod p^k` is itself `≡ c mod p^k`.
- How: Per coefficient `m`: the coefficients `coeff m (gj j − c) → coeff m (g − c)` (using `tendsto_coeff`), and each lies in the closed set `isClosed_dvd_pow`, so the limit does (`IsClosed.mem_of_tendsto`).
- Hypotheses: `gj → g` coefficientwise; eventually `gj j ≡ c mod p^k`.
- Uses from project: [`ModEqPow`, `isClosed_dvd_pow`, `tendsto_coeff`]
- Used by: `exists_normOp_fixed_lift`
- Visibility: public (scoped `PowerSeries.WithPiTopology` open)
- Lines: 504–521 (proof ~9 lines)
- Notes: none. `open scoped … in` modifier.

### theorem eq_of_forall_modEqPow
- Type: `theorem eq_of_forall_modEqPow {a b} (h : ∀ k, ModEqPow p k a b) : a = b`
- What: Hausdorff property: agreement mod `p^k` for all `k` forces equality (`⋂_k p^kℤ_[p] = 0`).
- How: Per coefficient, bound `‖coeff m (a−b)‖ ≤ p^{−k}` for all `k` (from `norm_le_pow_iff_mem_span_pow`); since `p^{−k} → 0` (`tendsto_inv_atTop_zero`, `tendsto_pow_atTop_atTop_of_one_lt`), the norm is `0` by `le_of_tendsto_of_tendsto'`.
- Hypotheses: `∀ k, ModEqPow p k a b`.
- Uses from project: [`ModEqPow`]
- Used by: `exists_normOp_fixed_lift`
- Visibility: public
- Lines: 523–537 (proof ~11 lines)
- Notes: none

### theorem exists_normOp_fixed_lift
- Type: `theorem exists_normOp_fixed_lift (f) (hf : IsUnit f) : ∃ g, IsUnit g ∧ normOp g = g ∧ ModEqPow p 1 g f`
- What: **RJW lem:A mod p** — every unit power series over `𝔽_p` lifts to an `𝒩`-fixed unit; i.e. `𝒲 mod p = 𝔽_p⟦T⟧^×`. Stated as lift-existence.
- How: Take a convergent subsequence `𝒩^[φ j] f → g` (`exists_subseq_tendsto`, compactness). `g` is a unit (`isClosed_isUnit.mem_of_tendsto` + `normOp_iterate_isUnit`). `𝒩 g = g` via Hausdorff (`eq_of_forall_modEqPow`): assemble `𝒩 g ≡ g mod p^{k+1}` from `normOp_modEq_of_modEq`, `normOp_iterate_modEq`, `modEqPow_of_tendsto`. `g ≡ f mod p` from `normOp_iterate_modEq_self` passed to the limit.
- Hypotheses: `f` a unit.
- Uses from project: [`normOp`, `ModEqPow`, `exists_subseq_tendsto`, `isClosed_isUnit`, `normOp_iterate_isUnit`, `eq_of_forall_modEqPow`, `modEqPow_of_tendsto`, `normOp_iterate_modEq`, `normOp_modEq_of_modEq`, `normOp_iterate_modEq_self`]
- Used by: `exists_normOp_dlog_modEq`
- Visibility: public (scoped `PowerSeries.WithPiTopology` open)
- Lines: 539–568 (proof ~26 lines)
- Notes: none. `open scoped … in`.

### theorem mem_range_phiSeries_of_dvd
- Type: `private theorem mem_range_phiSeries_of_dvd {c : PowerSeries (ZMod p)} (hc : ∀ n, ¬ p ∣ n → coeff n c = 0) : c ∈ Set.range (phiSeries p (R := ZMod p))`
- What: Over `𝔽_p`, a series supported only on multiples of `p` is in `range φ` (it is a `p`-th power).
- How: Candidate `p`-th root `mk (k ↦ coeff (p*k) c)`; over char `p`, `φ = expand p` (since `(1+T)^p − 1 = T^p` by `add_pow_char`); compare coefficients with `coeff_expand`/`coeff_expand_mul`.
- Hypotheses: `c` supported on multiples of `p`.
- Uses from project: [`phiSeries`]
- Used by: `fp_series_eq_dlog_add_frobC`
- Visibility: private
- Lines: 578–593 (proof ~13 lines)
- Notes: none. Uses `charP_of_injective_algebraMap'`.

### def AWfp
- Type: `private def AWfp (H : PowerSeries (ZMod p)) : ℕ → ZMod p × ZMod p` (well-founded recursion)
- What: The joint `(a_n, w_n)` coefficient recursion solving `T·a′ = a·w` over `𝔽_p` against target `H`: `(a_0,w_0)=(1,0)`; for `n≥1` with `S = Σ_{j=1}^{n−1} a_{n−j} w_j`, `(0,−S)` if `p∣n` else `(n⁻¹(H_n+S), H_n)`.
- How: Direct definition by strong recursion; `decreasing_by` discharges the `Finset.Ico 1 n` index bound.
- Hypotheses: target series `H`.
- Uses from project: []
- Used by: `AfpCoe`, `WfpCoe`, `Sfp_attach_eq`, `AWfp_dvd`, `AWfp_ndvd`, `AfpCoe_zero`, `WfpCoe_zero`
- Visibility: private
- Lines: 598–608 (def ~11 lines)
- Notes: none. Well-founded recursion (`decreasing_by`).

### def AfpCoe
- Type: `private def AfpCoe (H) (n : ℕ) : ZMod p := (AWfp p H n).1`
- What: The `a`-coefficient sequence (first projection of `AWfp`).
- How: Definition.
- Hypotheses: none.
- Uses from project: []
- Used by: `SfpSum`, `coeff_afp_mul_wfp`, `X_deriv_eq_aw`, `AfpCoe_zero`, `AfpCoe_ndvd`, `AfpCoe_dvd`, `fp_series_eq_dlog_add_frobC`
- Visibility: private
- Lines: 610–611 (def 1 line)
- Notes: none

### def WfpCoe
- Type: `private def WfpCoe (H) (n : ℕ) : ZMod p := (AWfp p H n).2`
- What: The `w`-coefficient sequence (second projection of `AWfp`).
- How: Definition.
- Hypotheses: none.
- Uses from project: []
- Used by: `SfpSum`, `coeff_afp_mul_wfp`, `X_deriv_eq_aw`, `WfpCoe_zero`, `WfpCoe_ndvd`, `WfpCoe_dvd`, `fp_series_eq_dlog_add_frobC`
- Visibility: private
- Lines: 612–613 (def 1 line)
- Notes: none

### def SfpSum
- Type: `private def SfpSum (H) (n : ℕ) : ZMod p := ∑ k ∈ Finset.Ico 1 n, AfpCoe p H k * WfpCoe p H (n - k)`
- What: The partial sum `S_n = Σ_{j=1}^{n−1} a_{n−j}·w_j` driving the recursion.
- How: Definition.
- Hypotheses: none.
- Uses from project: []
- Used by: `Sfp_attach_eq`, `AWfp_dvd`, `AWfp_ndvd`, `coeff_afp_mul_wfp`, `WfpCoe_dvd`, `AfpCoe_ndvd`
- Visibility: private
- Lines: 615–616 (def 1 line)
- Notes: none

### theorem Sfp_attach_eq
- Type: `private theorem Sfp_attach_eq (H) (n) : (∑ k ∈ (Ico 1 n).attach, (AWfp p H k.1).1 * (AWfp p H (n − k.1)).2) = SfpSum p H n`
- What: The `attach`-form sum inside `AWfp`'s body equals `SfpSum`.
- How: `Finset.sum_attach` + `rfl`.
- Hypotheses: none.
- Uses from project: []
- Used by: `AWfp_dvd`, `AWfp_ndvd`
- Visibility: private
- Lines: 618–622 (proof ~2 lines)
- Notes: none

### theorem AWfp_dvd
- Type: `private theorem AWfp_dvd (H) {n} (hn : n ≠ 0) (hd : p ∣ n) : AWfp p H n = (0, -SfpSum p H n)`
- What: Unfolds `AWfp` in the `p ∣ n` branch.
- How: `conv … rw [AWfp]`, discharge the `if`s with `if_neg hn` / `if_pos hd` and `Sfp_attach_eq`.
- Hypotheses: `n ≠ 0`, `p ∣ n`.
- Uses from project: []
- Used by: `WfpCoe_dvd`, `AfpCoe_dvd`
- Visibility: private
- Lines: 624–627 (proof ~2 lines)
- Notes: none

### theorem AWfp_ndvd
- Type: `private theorem AWfp_ndvd (H) {n} (hn : n ≠ 0) (hd : ¬ p ∣ n) : AWfp p H n = ((n : ZMod p)⁻¹ * (coeff n H + SfpSum p H n), coeff n H)`
- What: Unfolds `AWfp` in the `p ∤ n` branch.
- How: `conv … rw [AWfp]`, `if_neg hn` / `if_neg hd`, `Sfp_attach_eq`.
- Hypotheses: `n ≠ 0`, `¬ p ∣ n`.
- Uses from project: []
- Used by: `WfpCoe_ndvd`, `AfpCoe_ndvd`
- Visibility: private
- Lines: 629–633 (proof ~2 lines)
- Notes: none

### theorem AfpCoe_zero
- Type: `private theorem AfpCoe_zero (H) : AfpCoe p H 0 = 1`
- What: `a_0 = 1`.
- How: Unfold + `if_pos rfl`.
- Hypotheses: none.
- Uses from project: []
- Used by: `coeff_afp_mul_wfp`, `fp_series_eq_dlog_add_frobC`
- Visibility: private
- Lines: 635–636 (proof 1 line)
- Notes: none

### theorem WfpCoe_zero
- Type: `private theorem WfpCoe_zero (H) : WfpCoe p H 0 = 0`
- What: `w_0 = 0`.
- How: Unfold + `if_pos rfl`.
- Hypotheses: none.
- Uses from project: []
- Used by: `coeff_afp_mul_wfp`, `X_deriv_eq_aw`, `fp_series_eq_dlog_add_frobC`
- Visibility: private
- Lines: 637–638 (proof 1 line)
- Notes: none

### theorem WfpCoe_ndvd
- Type: `private theorem WfpCoe_ndvd (H) {n} (hn : n ≠ 0) (hd : ¬ p ∣ n) : WfpCoe p H n = coeff n H`
- What: `w_n = H_n` in the `p ∤ n` branch.
- How: `WfpCoe` + `AWfp_ndvd`.
- Hypotheses: `n ≠ 0`, `¬ p ∣ n`.
- Uses from project: []
- Used by: `X_deriv_eq_aw`, `fp_series_eq_dlog_add_frobC`
- Visibility: private
- Lines: 639–640 (proof 1 line)
- Notes: none

### theorem AfpCoe_ndvd
- Type: `private theorem AfpCoe_ndvd (H) {n} (hn : n ≠ 0) (hd : ¬ p ∣ n) : AfpCoe p H n = (n : ZMod p)⁻¹ * (coeff n H + SfpSum p H n)`
- What: `a_n` in the `p ∤ n` branch.
- How: `AfpCoe` + `AWfp_ndvd`.
- Hypotheses: `n ≠ 0`, `¬ p ∣ n`.
- Uses from project: []
- Used by: `X_deriv_eq_aw`
- Visibility: private
- Lines: 641–643 (proof 1 line)
- Notes: none

### theorem WfpCoe_dvd
- Type: `private theorem WfpCoe_dvd (H) {n} (hn : n ≠ 0) (hd : p ∣ n) : WfpCoe p H n = - SfpSum p H n`
- What: `w_n = −S_n` in the `p ∣ n` branch.
- How: `WfpCoe` + `AWfp_dvd`.
- Hypotheses: `n ≠ 0`, `p ∣ n`.
- Uses from project: []
- Used by: `X_deriv_eq_aw`
- Visibility: private
- Lines: 644–645 (proof 1 line)
- Notes: none

### theorem AfpCoe_dvd
- Type: `private theorem AfpCoe_dvd (H) {n} (hn : n ≠ 0) (hd : p ∣ n) : AfpCoe p H n = 0`
- What: `a_n = 0` in the `p ∣ n` branch.
- How: `AfpCoe` + `AWfp_dvd`.
- Hypotheses: `n ≠ 0`, `p ∣ n`.
- Uses from project: []
- Used by: `X_deriv_eq_aw`
- Visibility: private
- Lines: 646–647 (proof 1 line)
- Notes: none

### theorem coeff_afp_mul_wfp
- Type: `private theorem coeff_afp_mul_wfp (H) {n} (hn : n ≠ 0) : coeff n (mk (AfpCoe p H) * mk (WfpCoe p H)) = WfpCoe p H n + SfpSum p H n`
- What: `[Tⁿ](a·w) = w_n + S_n` for `n ≥ 1` (the convolution splits off its `j=0` and `j=n` ends).
- How: `coeff_mul` + `sum_antidiagonal_eq_sum_range_succ_mk`, peel `j=n` end (`WfpCoe_zero`) and `j=0` end (`AfpCoe_zero`), middle is `SfpSum` (`Finset.sum_Ico_consecutive`).
- Hypotheses: `n ≠ 0`.
- Uses from project: [`AfpCoe`, `WfpCoe`, `SfpSum`, `AfpCoe_zero`, `WfpCoe_zero`]
- Used by: `X_deriv_eq_aw`
- Visibility: private
- Lines: 649–662 (proof ~8 lines)
- Notes: none

### theorem X_deriv_eq_aw
- Type: `private theorem X_deriv_eq_aw (H) : X * derivativeFun (mk (AfpCoe p H)) = mk (AfpCoe p H) * mk (WfpCoe p H)`
- What: The defining identity `T·a′ = a·w` of the recursion holds coefficientwise.
- How: Per coefficient; `n=0` both sides vanish; for `n=m+1`, `coeff_succ_X_mul` + `coeff_derivativeFun` reduces to `n·a_n = w_n + S_n`, which holds in both the `p∣n` branch (`AfpCoe_dvd`/`WfpCoe_dvd`, both sides 0) and `p∤n` branch (`AfpCoe_ndvd`/`WfpCoe_ndvd`, `n` invertible via `ZMod.natCast_eq_zero_iff`).
- Hypotheses: none.
- Uses from project: [`AfpCoe`, `WfpCoe`, `derivativeFun`, `coeff_afp_mul_wfp`, `WfpCoe_zero`, `AfpCoe_dvd`, `WfpCoe_dvd`, `AfpCoe_ndvd`, `WfpCoe_ndvd`]
- Used by: `fp_series_eq_dlog_add_frobC`
- Visibility: private
- Lines: 664–683 (proof ~16 lines)
- Notes: long-ish (~16 lines); case split with the two recursion branches. Under 30.

### theorem fp_series_eq_dlog_add_frobC
- Type: `theorem fp_series_eq_dlog_add_frobC (g : PowerSeries (ZMod p)) : ∃ a b c, IsUnit a ∧ c ∈ Set.range (phiSeries p (R := ZMod p)) ∧ X * b = (1 + X) * c ∧ g = (1 + X) * derivativeFun a * Ring.inverse a + b`
- What: **RJW lem:B mod p 2** ("the most delicate and technical part") — the faithful `𝔽_p⟦T⟧` decomposition `𝔽_p⟦T⟧ = Δ(𝔽_p⟦T⟧^×) + (T+1)/T·C`: every `g` is `Δa + b` for a unit `a` and a `b` with `X·b = (1+X)·c`, `c ∈ range φ`.
- How: Topology-free coefficient recursion (no infinite product). `u = 1+T`, `H = T·g·u⁻¹`, `a = mk(AfpCoe H)`, `w = mk(WfpCoe H)`. `a` a unit (`a(0)=1`); `T·a′ = a·w` (`X_deriv_eq_aw`) gives `w = T·a′·a⁻¹`; `c := H − w` is supported on `pℕ` (agrees with `H` off `pℕ`), hence in `range φ` (`mem_range_phiSeries_of_dvd`); `b := g − Δa` satisfies `X·b = u·c` from `X·Δa = u·w` and `u·H = T·g`.
- Hypotheses: none (any `g : 𝔽_p⟦T⟧`).
- Uses from project: [`phiSeries`, `derivativeFun`, `AfpCoe`, `WfpCoe`, `AfpCoe_zero`, `WfpCoe_zero`, `WfpCoe_ndvd`, `X_deriv_eq_aw`, `mem_range_phiSeries_of_dvd`]
- Used by: `exists_normOp_dlog_modEq`
- Visibility: public
- Lines: 685–755 (proof ~38 lines)
- Notes: long(30-50) — proof body ~38 lines (718→755). Flag for /decompose-proof. RJW "most delicate and technical part" (now CLOSED, statement-fix authorised per docstring).

### theorem dlog_mul
- Type: `theorem dlog_mul {g h} (hg : IsUnit g) (hh : IsUnit h) : dlog p (g * h) = dlog p g + dlog p h`
- What: The log-derivative `Δ = dlog` is additive on the unit group.
- How: `(gh)' = g'h + gh'` (`derivativeFun_mul`), `Ring.mul_inverse_rev`, then a big `ring`-rewrite cancelling `g·g⁻¹` and `h·h⁻¹` (`Ring.mul_inverse_cancel`).
- Hypotheses: `g, h` units.
- Uses from project: [`dlog`, `derivativeFun`]
- Used by: `dlog_inverse`, `dlog_pow`, `dlog_approxProd`
- Visibility: public
- Lines: 764–774 (proof ~8 lines)
- Notes: none

### theorem dlog_one
- Type: `theorem dlog_one : dlog p (1 : PowerSeries ℤ_[p]) = 0`
- What: `Δ 1 = 0`.
- How: `derivativeFun_one`, then `mul_zero`/`zero_mul`.
- Hypotheses: none.
- Uses from project: [`dlog`, `derivativeFun`]
- Used by: `dlog_inverse`, `dlog_pow`, `dlog_approxProd`
- Visibility: public
- Lines: 776–778 (proof 1 line)
- Notes: none

### theorem dlog_inverse
- Type: `theorem dlog_inverse {g} (hg : IsUnit g) : dlog p (Ring.inverse g) = - dlog p g`
- What: `Δ(g⁻¹) = −Δg` for a unit `g`.
- How: From `dlog_mul` of `g` and `g⁻¹`, `Ring.mul_inverse_cancel` + `dlog_one` give `Δg + Δ(g⁻¹) = 0`; `linear_combination`.
- Hypotheses: `g` a unit.
- Uses from project: [`dlog`, `dlog_mul`, `dlog_one`]
- Used by: `dlog_pow` (indirectly), `dlog_approxFactor`
- Visibility: public
- Lines: 780–785 (proof ~3 lines)
- Notes: none

### theorem dlog_pow
- Type: `theorem dlog_pow {g} (hg : IsUnit g) (n : ℕ) : dlog p (g ^ n) = (n : ℤ) • dlog p g`
- What: `Δ(gⁿ) = n·Δg` for a unit `g`.
- How: Induction on `n`: base `dlog_one`; step `pow_succ` + `dlog_mul` + `push_cast; ring`.
- Hypotheses: `g` a unit.
- Uses from project: [`dlog`, `dlog_mul`, `dlog_one`]
- Used by: `dlog_approxFactor`
- Visibility: public
- Lines: 787–792 (proof ~3 lines)
- Notes: none

### theorem derivativeFun_one_add_X_pow_zmod
- Type: `private theorem derivativeFun_one_add_X_pow_zmod (i : ℕ) : derivativeFun ((1 + X : PowerSeries (ZMod p)) ^ i) = (i : PowerSeries (ZMod p)) * (1 + X) ^ (i - 1)`
- What: `∂((1+T)^i) = i·(1+T)^{i−1}` over `ZMod p`.
- How: `derivative_pow` with `∂(1+X)=1`.
- Hypotheses: none.
- Uses from project: [`derivativeFun`, `derivativeFun_add`, `derivativeFun_one`]
- Used by: `theta_smul_eigen`
- Visibility: private
- Lines: 807–816 (proof ~6 lines)
- Notes: none

### theorem derivativeFun_pow_p_zmod
- Type: `private theorem derivativeFun_pow_p_zmod (g : PowerSeries (ZMod p)) : derivativeFun (g ^ p) = 0`
- What: A `p`-th power has zero derivative over `ZMod p`.
- How: `derivative_pow` gives factor `(p : ZMod p) = 0` (`ZMod.natCast_self`), so the whole thing vanishes.
- Hypotheses: none.
- Uses from project: [`derivativeFun`]
- Used by: `digits_unique_zmod`
- Visibility: private
- Lines: 818–824 (proof ~5 lines)
- Notes: none

### theorem theta_smul_eigen
- Type: `private theorem theta_smul_eigen {E} (hE : derivativeFun E = 0) (i : ℕ) (c : ZMod p) : (1 + X) * derivativeFun (C c * ((1 + X) ^ i * E)) = C (i * c) * ((1 + X) ^ i * E)`
- What: The `θ = (1+T)∂` eigen-identity: `θ(C c·(1+T)^i·E) = C(i·c)·(1+T)^i·E` when `∂E = 0`.
- How: Expand the derivative by Leibniz (`derivativeFun_mul`, `derivativeFun_C`, `derivativeFun_one_add_X_pow_zmod`), case `i=0`/`i>0`, then `pow_succ'` and `ring`.
- Hypotheses: `∂E = 0`.
- Uses from project: [`derivativeFun`, `derivativeFun_one_add_X_pow_zmod`]
- Used by: `sum_pow_smul_eq_zero`
- Visibility: private
- Lines: 826–847 (proof ~18 lines)
- Notes: long-ish (~18 lines); hinges on `derivativeFun_one_add_X_pow_zmod`. Under 30.

### theorem sum_pow_smul_eq_zero
- Type: `private theorem sum_pow_smul_eq_zero {E : Fin p → …} (hE : ∀ i, derivativeFun (E i) = 0) (hsum : ∑ i, (1 + X) ^ i * E i = 0) (k : ℕ) : ∑ i, C ((i : ZMod p) ^ k) * ((1 + X) ^ i * E i) = 0`
- What: If `Σ_i (1+T)^i E_i = 0` with each `∂E_i = 0`, then `Σ_i C(iᵏ)·(1+T)^i E_i = 0` for every `k` (apply `θ` k times).
- How: Induction on `k`; step applies `θ` to the `k`-th identity (`derivativeFun` of a sum is the sum of derivatives) and uses `theta_smul_eigen` summand-wise.
- Hypotheses: each `E_i` in `ker ∂`; the base sum vanishes.
- Uses from project: [`derivativeFun`, `theta_smul_eigen`]
- Used by: `sum_polyEval_smul_eq_zero`
- Visibility: private
- Lines: 849–872 (proof ~18 lines)
- Notes: long-ish (~18 lines); hinges on `theta_smul_eigen`. Under 30.

### theorem sum_polyEval_smul_eq_zero
- Type: `private theorem sum_polyEval_smul_eq_zero {E} (hE) (hsum) (P : Polynomial (ZMod p)) : ∑ i, C (P.eval (i : ZMod p)) * ((1 + X) ^ i * E i) = 0`
- What: Polynomial-evaluation form of the power-sum identity: holds for any `P : 𝔽_p[X]`.
- How: `Polynomial.induction_on'`; additive case splits the sum; monomial case factors out `C c` and applies `sum_pow_smul_eq_zero`.
- Hypotheses: each `E_i ∈ ker ∂`; base sum vanishes.
- Uses from project: [`sum_pow_smul_eq_zero`]
- Used by: `digits_unique_zmod`
- Visibility: private
- Lines: 874–892 (proof ~14 lines)
- Notes: none

### theorem lagrange_delta_eval
- Type: `private theorem lagrange_delta_eval (i j : Fin p) : (1 - (X - C ((j : ℕ) : ZMod p)) ^ (p - 1)).eval ((i : ℕ) : ZMod p) = if i = j then 1 else 0`
- What: The Lagrange `δ`-indicator over `𝔽_p`: `1 − (i − j)^{p−1} = [i = j]` (Fermat).
- How: Evaluate the polynomial; case `i=j` (`ZMod.pow_card_sub_one` → 0, so `1−0=1`) vs `i≠j` (`ZMod.pow_card_sub_one_eq_one` → 1, so `1−1=0`), using `natCast_eq_natCast_iff` + `Fin.ext`.
- Hypotheses: none.
- Uses from project: []
- Used by: `digits_unique_zmod`
- Visibility: private
- Lines: 894–908 (proof ~11 lines)
- Notes: none

### theorem digits_unique_zmod
- Type: `private theorem digits_unique_zmod {G H : Fin p → …} (heq : ∑ i, (1 + X) ^ i * phiSeries p (G i) = ∑ i, (1 + X) ^ i * phiSeries p (H i)) : G = H`
- What: **Digit-decomposition uniqueness over `𝔽_p⟦T⟧`**: equal digit-assembled series force equal digit families.
- How: Differences `E_i = φ(G_i) − φ(H_i)` lie in `ker ∂` (`phiSeries_eq_pow_zmod` + `derivativeFun_pow_p_zmod`); the Lagrange combination `sum_polyEval_smul_eq_zero` with `lagrange_delta_eval` isolates the `j`-th summand `(1+T)^j E_j = 0`; cancel the unit `(1+T)^j`; `φ` injective (`frobenius_inj` over char `p`) gives `G_j = H_j`. Hinges on `sum_polyEval_smul_eq_zero` + `lagrange_delta_eval` + `phiSeries_eq_pow_zmod`.
- Hypotheses: the two digit-assemblies are equal.
- Uses from project: [`phiSeries`, `phiSeries_eq_pow_zmod`, `derivativeFun`, `derivativeFun_pow_p_zmod`, `sum_polyEval_smul_eq_zero`, `lagrange_delta_eval`]
- Used by: `existsUnique_digits_zmod`
- Visibility: private
- Lines: 910–944 (proof ~28 lines)
- Notes: long-ish (~28 lines); hinges on `sum_polyEval_smul_eq_zero`. Under 30. Uses `charP_of_injective_algebraMap'`.

### theorem existsUnique_digits_zmod
- Type: `private theorem existsUnique_digits_zmod (F : PowerSeries (ZMod p)) : ∃! G : Fin p → …, IsDigitDecomp p F G`
- What: **Existence-uniqueness of digits over `𝔽_p⟦T⟧`**: every `F̄` has a unique digit family (makes `psiSeries` honest over `ZMod p`).
- How: Lift `F` to `ℤ_[p]` (`map_surjective` of `toZMod`), use `existsUnique_digits_padicInt` + `isDigitDecomp_map` for existence; uniqueness is `digits_unique_zmod`.
- Hypotheses: none.
- Uses from project: [`existsUnique_digits_padicInt`, `IsDigitDecomp`, `isDigitDecomp_map`, `digits_unique_zmod`]
- Used by: `psiSeries_eq_of_isDigitDecomp_zmod`, `psiSeries_phiSeries_mul_zmod`, `psiSeries_add_zmod`
- Visibility: private
- Lines: 946–961 (proof ~11 lines)
- Notes: none

### theorem psiSeries_eq_of_isDigitDecomp_zmod
- Type: `private theorem psiSeries_eq_of_isDigitDecomp_zmod {F} {G} (hG : IsDigitDecomp p F G) : psiSeries p F = G 0`
- What: Over `ZMod p`, `psiSeries F` is the `0`-th digit of any digit decomposition.
- How: `psiSeries_eq_of_unique` with the uniqueness from `existsUnique_digits_zmod`.
- Hypotheses: `G` is a digit decomposition of `F`.
- Uses from project: [`psiSeries`, `IsDigitDecomp`, `psiSeries_eq_of_unique`, `existsUnique_digits_zmod`]
- Used by: `psiSeries_phi_zmod`, `psiSeries_phiSeries_mul_zmod`, `map_toZMod_psiSeries`, `psiSeries_X_pow_lt`, `psiSeries_add_zmod`
- Visibility: private
- Lines: 963–967 (proof ~2 lines, term-mode)
- Notes: none

### theorem phiSeries_C_zmod
- Type: `private theorem phiSeries_C_zmod (a : ZMod p) : phiSeries p (PowerSeries.C a) = PowerSeries.C a`
- What: `φ` fixes constants over `ZMod p`.
- How: Unfold `phiSeries`, `subst_C`.
- Hypotheses: none.
- Uses from project: [`phiSeries`]
- Used by: `psiSeries_X_pow_lt`
- Visibility: private
- Lines: 969–972 (proof 1 line)
- Notes: none

### theorem psiSeries_phi_zmod
- Type: `private theorem psiSeries_phi_zmod (G : PowerSeries (ZMod p)) : psiSeries p (phiSeries p G) = G`
- What: `ψ ∘ φ = id` over `ZMod p`.
- How: Exhibit the digit family `i ↦ (if i=0 then G else 0)` and apply `psiSeries_eq_of_isDigitDecomp_zmod`; isolate the `i=0` summand (`Finset.sum_eq_single`).
- Hypotheses: none.
- Uses from project: [`psiSeries`, `phiSeries`, `psiSeries_eq_of_isDigitDecomp_zmod`, `phiSeries_zero`]
- Used by: `psiSeries_one_add_X_mul_X_pow`
- Visibility: private
- Lines: 974–984 (proof ~7 lines)
- Notes: none

### theorem psiSeries_phiSeries_mul_zmod
- Type: `private theorem psiSeries_phiSeries_mul_zmod (d F : PowerSeries (ZMod p)) : psiSeries p (phiSeries p d * F) = d * psiSeries p F`
- What: **The series projection formula over `ZMod p`** (`ψ(φd·F) = d·ψF`) — the ξ-free substitute for RJW's `Eqphipsi`-based "ψ fixes `(T+1)/T`".
- How: Take the digit family `GF` of `F` (`existsUnique_digits_zmod`); then `d·GF` is the digit family of `φd·F` (multiplicativity of subst, `subst_mul`), and `ψ` reads off the `0`-th digit.
- Hypotheses: none.
- Uses from project: [`psiSeries`, `phiSeries`, `existsUnique_digits_zmod`, `psiSeries_eq_of_isDigitDecomp_zmod`, `hasSubst_one_add_X_pow_sub_one`]
- Used by: `psiId_one_add_X_div_X_phi_eq_zero`
- Visibility: private
- Lines: 986–999 (proof ~9 lines)
- Notes: none

### theorem map_toZMod_psiSeries
- Type: `private theorem map_toZMod_psiSeries (F : PowerSeries ℤ_[p]) : map toZMod (psiSeries p F) = psiSeries p (map toZMod F)`
- What: `ψ` commutes with reduction mod `p` (`map toZMod`).
- How: Take the digit family of `F` over `ℤ_[p]` (`existsUnique_digits_padicInt`); it reduces to a digit family over `𝔽_p` (`isDigitDecomp_map`), and `ψ` is the `0`-th digit on both sides.
- Hypotheses: none.
- Uses from project: [`psiSeries`, `existsUnique_digits_padicInt`, `psiSeries_eq_of_isDigitDecomp_padicInt`, `psiSeries_eq_of_isDigitDecomp_zmod`, `isDigitDecomp_map`]
- Used by: `exists_normOp_dlog_modEq`
- Visibility: private
- Lines: 1001–1007 (proof ~3 lines)
- Notes: none

### theorem psiSeries_X_pow_lt
- Type: `private theorem psiSeries_X_pow_lt {j : ℕ} (hj : j < p) : psiSeries p ((X : PowerSeries (ZMod p)) ^ j) = PowerSeries.C ((-1) ^ j)`
- What: `ψ(Tʲ) = (−1)ʲ` (constant) for `j < p`.
- How: Build the digit family of `Tʲ = ((1+T)−1)ʲ` via the binomial expansion `add_pow`; the `l ≥ j+1` terms vanish (`Nat.choose_eq_zero_of_lt`); the `0`-th digit is `binom(j,0)(−1)ʲ = (−1)ʲ`.
- Hypotheses: `j < p`.
- Uses from project: [`psiSeries`, `phiSeries_C_zmod`, `IsDigitDecomp`, `phiSeries`, `psiSeries_eq_of_isDigitDecomp_zmod`]
- Used by: `psiSeries_one_add_X_mul_X_pow`
- Visibility: private
- Lines: 1009–1029 (proof ~18 lines)
- Notes: long-ish (~18 lines); binomial-digit construction. Under 30.

### theorem psiSeries_add_zmod
- Type: `private theorem psiSeries_add_zmod (F G : PowerSeries (ZMod p)) : psiSeries p (F + G) = psiSeries p F + psiSeries p G`
- What: `ψ` is additive over `ZMod p`.
- How: Take digit families `GF, GG` of `F, G` (`existsUnique_digits_zmod`); `GF + GG` is the digit family of `F+G` (subst additive, `subst_add`); `ψ` reads off the `0`-th.
- Hypotheses: none.
- Uses from project: [`psiSeries`, `phiSeries`, `existsUnique_digits_zmod`, `psiSeries_eq_of_isDigitDecomp_zmod`, `hasSubst_one_add_X_pow_sub_one`]
- Used by: `psiSeries_one_add_X_mul_X_pow`
- Visibility: private
- Lines: 1031–1042 (proof ~8 lines)
- Notes: none

### theorem X_pow_eq_X_mul
- Type: `private theorem X_pow_eq_X_mul (p : ℕ) [Fact p.Prime] : (X : PowerSeries (ZMod p)) ^ p = X * X ^ (p - 1)`
- What: `X^p = X·X^{p−1}` over `ZMod p`.
- How: `pow_succ'` + `Nat.sub_add_cancel` (using `p ≥ 1`).
- Hypotheses: none (re-binds `p` explicitly).
- Uses from project: []
- Used by: `psiSeries_one_add_X_mul_X_pow`, `psiId_one_add_X_div_X_phi_eq_zero`
- Visibility: private
- Lines: 1044–1047 (proof 1 line)
- Notes: none. Shadows the section variable `p` with its own binder.

### theorem psiSeries_one_add_X_mul_X_pow
- Type: `private theorem psiSeries_one_add_X_mul_X_pow : psiSeries p ((1 + X) * X ^ (p - 1)) = (1 + X : PowerSeries (ZMod p))`
- What: `ψ((1+T)·T^{p−1}) = 1+T` over `ZMod p`.
- How: Expand `(1+T)·T^{p−1} = T^{p−1} + φ(T)` (using `phiSeries_eq_pow_zmod`, `X_pow_eq_X_mul`); then `ψ(T^{p−1}) = C((−1)^{p−1}) = 1` (Fermat `ZMod.pow_card_sub_one_eq_one`) and `ψ(φ T) = T` (`psiSeries_phi_zmod`), added by `psiSeries_add_zmod`.
- Hypotheses: none.
- Uses from project: [`psiSeries`, `phiSeries`, `phiSeries_eq_pow_zmod`, `X_pow_eq_X_mul`, `psiSeries_add_zmod`, `psiSeries_X_pow_lt`, `psiSeries_phi_zmod`]
- Used by: `psiId_one_add_X_div_X_phi_eq_zero`
- Visibility: private
- Lines: 1049–1062 (proof ~10 lines)
- Notes: none

### theorem eq_zero_of_eq_X_pow_mul_pow
- Type: `private theorem eq_zero_of_eq_X_pow_mul_pow {e} (h : e = X ^ (p - 1) * e ^ p) : e = 0`
- What: The order argument: `e = T^{p−1}·e^p` over `𝔽_p⟦T⟧` forces `e = 0` (RJW's `d_n = d_{np}` collapse).
- How: By contradiction; compare orders (`order_mul`, `order_X_pow`, `order_pow`): if `ord e = m < ∞` then `m = (p−1) + p·m`, impossible for `p ≥ 2` (`omega`).
- Hypotheses: `e = X^{p−1}·e^p`.
- Uses from project: []
- Used by: `psiId_one_add_X_div_X_phi_eq_zero`
- Visibility: private
- Lines: 1064–1077 (proof ~10 lines)
- Notes: none

### theorem psiId_one_add_X_div_X_phi_eq_zero
- Type: `private theorem psiId_one_add_X_div_X_phi_eq_zero {b c} (hpsi : psiSeries p b = b) (hXb : X * b = (1 + X) * c) (hc : c ∈ Set.range (phiSeries p (R := ZMod p))) : b = 0`
- What: **`lem:B mod p`'s ψ-killing step** — the `(T+1)/T·C` component is killed by `ψ = id`: a `ψ`-fixed `b` with `X·b = (1+X)·c`, `c ∈ range φ` is zero.
- How: Write `c = φ(X·e) = T^p·φ(e)` (since `c(0)=0 ⟹ d(0)=0 ⟹ X∣d`), so `b = (1+T)·T^{p−1}·φ(e)`; the projection formula (`psiSeries_phiSeries_mul_zmod`) + `psiSeries_one_add_X_mul_X_pow` give `ψ b = e·(1+T)`; with `ψ b = b`, cancel the unit `(1+T)` to get `e = T^{p−1}·e^p`, forcing `e = 0` (`eq_zero_of_eq_X_pow_mul_pow`). Hinges on `psiSeries_phiSeries_mul_zmod`, `psiSeries_one_add_X_mul_X_pow`, `eq_zero_of_eq_X_pow_mul_pow`.
- Hypotheses: `ψ b = b`; `X·b = (1+X)·c`; `c ∈ range φ`.
- Uses from project: [`psiSeries`, `phiSeries`, `phiSeries_eq_pow_zmod`, `constantCoeff_phiSeries`, `hasSubst_one_add_X_pow_sub_one`, `X_pow_eq_X_mul`, `psiSeries_phiSeries_mul_zmod`, `psiSeries_one_add_X_mul_X_pow`, `eq_zero_of_eq_X_pow_mul_pow`]
- Used by: `exists_normOp_dlog_modEq`
- Visibility: private
- Lines: 1079–1129 (proof ~43 lines)
- Notes: long(30-50) — proof body ~43 lines (1086→1129). Flag for /decompose-proof.

### theorem map_toZMod_dlog
- Type: `private theorem map_toZMod_dlog {g} (hg : IsUnit g) : map toZMod (dlog p g) = (1 + X) * derivativeFun (map toZMod g) * Ring.inverse (map toZMod g)`
- What: `Δ = dlog` commutes with reduction mod `p` on units (the `𝔽_p` log-derivative is the reduction of the `ℤ_[p]` one).
- How: `derivativeFun` reduces coefficientwise (`coeff_derivativeFun` + `coeff_map`); `Ring.inverse` of a unit reduces (`Ring.inverse_mul_eq_iff_eq_mul` + `mul_inverse_cancel`); assemble through `dlog` definition with `map_X`.
- Hypotheses: `g` a unit.
- Uses from project: [`dlog`, `derivativeFun`]
- Used by: `exists_normOp_dlog_modEq`
- Visibility: private
- Lines: 1133–1152 (proof ~16 lines)
- Notes: long-ish (~16 lines); two reduction sub-facts. Under 30.

### theorem exists_unit_lift_zmod
- Type: `private theorem exists_unit_lift_zmod {a : PowerSeries (ZMod p)} (ha : IsUnit a) : ∃ A : PowerSeries ℤ_[p], IsUnit A ∧ map toZMod A = a`
- What: Every `𝔽_p`-unit power series lifts to a `ℤ_[p]`-unit with the same reduction.
- How: Surjectivity of `map toZMod` gives a lift `A`; its constant coefficient is not in the maximal ideal (`ker_toZMod`, `notMem_maximalIdeal`) since its reduction `a(0) ≠ 0`, so `A` is a unit.
- Hypotheses: `a` a unit.
- Uses from project: []
- Used by: `exists_normOp_dlog_modEq`
- Visibility: private
- Lines: 1154–1167 (proof ~11 lines)
- Notes: none

### theorem exists_normOp_dlog_modEq
- Type: `private theorem exists_normOp_dlog_modEq {f} (hf : psiSeries p f = f) : ∃ g, IsUnit g ∧ normOp g = g ∧ ModEqPow p 1 (dlog p g) f`
- What: **`B ⊆ A` mod `p` (RJW lem:B mod p)** — every `ψ`-fixed series is, mod `p`, the log-derivative of an `𝒩`-fixed unit.
- How: Apply `fp_series_eq_dlog_add_frobC` to `F = f̄` to get `f̄ = Δā + b̄`; lift `ā` to `A` (`exists_unit_lift_zmod`) then to `g ∈ 𝒲` (`exists_normOp_fixed_lift`); `b̄ = (f − Δg) mod p` is `ψ`-fixed (using `dlog_mem_psiIdSeries`, `map_toZMod_psiSeries`, `psiSeries_sub`), so `b̄ = 0` (`psiId_one_add_X_div_X_phi_eq_zero`), leaving `Δg ≡ f mod p`. Hinges on `fp_series_eq_dlog_add_frobC`, `exists_normOp_fixed_lift`, `psiId_one_add_X_div_X_phi_eq_zero`, `dlog_mem_psiIdSeries`.
- Hypotheses: `f` is `ψ`-fixed.
- Uses from project: [`psiSeries`, `dlog`, `normOp`, `ModEqPow`, `fp_series_eq_dlog_add_frobC`, `exist
s_unit_lift_zmod`, `exists_normOp_fixed_lift`, `modEqPow_one_iff_map_toZMod`, `map_toZMod_dlog`, `derivativeFun`, `map_toZMod_psiSeries`, `psiSeries_sub`, `dlog_mem_psiIdSeries`, `psiId_one_add_X_div_X_phi_eq_zero`]
- Used by: `exists_approx_step`
- Visibility: private
- Lines: 1169–1194 (proof ~21 lines)
- Notes: none

### theorem exists_approx_step
- Type: `private theorem exists_approx_step {f} (hf : psiSeries p f = f) : ∃ (g f'), IsUnit g ∧ normOp g = g ∧ psiSeries p f' = f' ∧ dlog p g = f + PowerSeries.C (p : ℤ_[p]) * f'`
- What: **The one-step refinement (lem:log der red mod p)** — a `ψ`-fixed `f` admits `g ∈ 𝒲` and a `ψ`-fixed `f'` with `Δg = f + p·f'`.
- How: From `exists_normOp_dlog_modEq`, `Δg ≡ f mod p`; write the difference as `C(p)·f'` (`modEqPow_iff_exists_C_mul`); `f'` is `ψ`-fixed because `C(p)·(ψf' − f') = 0` (apply `ψ` to `C(p)f' = Δg − f`, using `dlog_mem_psiIdSeries`) and `C(p)` is a non-zero-divisor.
- Hypotheses: `f` is `ψ`-fixed.
- Uses from project: [`psiSeries`, `dlog`, `normOp`, `exists_normOp_dlog_modEq`, `modEqPow_iff_exists_C_mul`, `psiSeries_C_mul_padicInt`, `psiSeries_sub`, `dlog_mem_psiIdSeries`]
- Used by: `exists_approx_seq`
- Visibility: private
- Lines: 1196–1224 (proof ~22 lines)
- Notes: none

### theorem exists_approx_seq
- Type: `private theorem exists_approx_seq {F} (hF : psiSeries p F = F) : ∃ (gseq fseq : ℕ → …), fseq 0 = F ∧ (∀ n, psiSeries p (fseq n) = fseq n) ∧ (∀ n, IsUnit (gseq n)) ∧ (∀ n, normOp (gseq n) = gseq n) ∧ (∀ n, dlog p (gseq (n+1)) = fseq n + C(p)·fseq (n+1))`
- What: **The successive-approximation sequences** — `gₙ ∈ 𝒲`, `fₙ ∈ (ψ=id)`, `f₀ = F`, with `Δ(g_{n+1}) = f_n + p·f_{n+1}`.
- How: Build via `Nat.rec` over `Q = {f // ψf=f}` using `Classical.choose` of `exists_approx_step` for the step data (`stepG`/`stepF`); extract the four conjuncts by case on `n` (zero gives `gₙ=1`, `normOp 1 = 1`; succ gives the step properties via `choose_spec`).
- Hypotheses: `F` is `ψ`-fixed.
- Uses from project: [`psiSeries`, `dlog`, `normOp`, `normOp_one`, `exists_approx_step`]
- Used by: `dlog_surjective_onto_psiId`
- Visibility: private
- Lines: 1226–1253 (proof ~22 lines)
- Notes: none. Uses `Classical.choose`/`choose_spec`.

### theorem normOp_pow
- Type: `private theorem normOp_pow {g} (h : normOp g = g) (n : ℕ) : normOp (g ^ n) = g ^ n`
- What: `𝒩(gⁿ) = gⁿ` for an `𝒩`-fixed `g` (`𝒩` multiplicative).
- How: Transport through the monoid hom `normOpHom` (`map_pow`), then `h`.
- Hypotheses: `g` is `𝒩`-fixed.
- Uses from project: [`normOp`, `normOpHom_apply`]
- Used by: `approxProd_normOp`
- Visibility: private
- Lines: 1255–1258 (proof 1 line)
- Notes: none

### theorem normOp_inverse
- Type: `private theorem normOp_inverse {g} (hg : IsUnit g) (h : normOp g = g) : normOp (Ring.inverse g) = Ring.inverse g`
- What: `𝒩(g⁻¹) = g⁻¹` for an `𝒩`-fixed unit `g`.
- How: Show `𝒩(g⁻¹)·g = 1` (from `normOp_mul`, `inverse_mul_cancel`, `normOp_one`, then `h`); rearrange.
- Hypotheses: `g` a unit and `𝒩`-fixed.
- Uses from project: [`normOp`, `normOp_mul`, `normOp_one`]
- Used by: `approxProd_normOp`
- Visibility: private
- Lines: 1260–1268 (proof ~6 lines)
- Notes: none

### def approxFactor
- Type: `private def approxFactor (gseq : ℕ → PowerSeries ℤ_[p]) (n : ℕ) : PowerSeries ℤ_[p]`
- What: The `n`-th factor `g_{n+1}^{(−1)ⁿ pⁿ}` of the successive-approximation product (negative-sign factors via `Ring.inverse`).
- How: `if Even n then g_{n+1}^{p^n} else Ring.inverse (g_{n+1}^{p^n})`.
- Hypotheses: a sequence `gseq`.
- Uses from project: []
- Used by: `approxProd`, `approxFactor_isUnit`, `approxProd_normOp`, `dlog_approxFactor`
- Visibility: private
- Lines: 1270–1273 (def ~2 lines)
- Notes: none

### def approxProd
- Type: `private def approxProd (gseq : ℕ → PowerSeries ℤ_[p]) : ℕ → PowerSeries ℤ_[p]`
- What: The partial products `hₙ = ∏_{k=1}^n g_k^{(−1)^{k−1}p^{k−1}}` (recursive: `h_0 = 1`, `h_{n+1} = h_n · approxFactor n`).
- How: Structural recursion on `n`.
- Hypotheses: a sequence `gseq`.
- Uses from project: [`approxFactor`]
- Used by: `approxProd_isUnit`, `approxProd_normOp`, `dlog_approxProd`, `dlog_surjective_onto_psiId`
- Visibility: private
- Lines: 1275–1278 (def ~3 lines)
- Notes: none

### theorem approxFactor_isUnit
- Type: `private theorem approxFactor_isUnit {gseq} (hg : ∀ n, IsUnit (gseq n)) (n) : IsUnit (approxFactor p gseq n)`
- What: Each `approxFactor` is a unit.
- How: Case on `Even n`; `IsUnit.pow` or `isUnit_ringInverse` of a power.
- Hypotheses: each `gseq n` a unit.
- Uses from project: [`approxFactor`]
- Used by: `approxProd_isUnit`, `dlog_approxProd`
- Visibility: private
- Lines: 1280–1285 (proof ~4 lines)
- Notes: none

### theorem approxProd_isUnit
- Type: `private theorem approxProd_isUnit {gseq} (hg : ∀ n, IsUnit (gseq n)) (n) : IsUnit (approxProd p gseq n)`
- What: Each partial product `hₙ` is a unit.
- How: Induction on `n`; `isUnit_one` and `IsUnit.mul` with `approxFactor_isUnit`.
- Hypotheses: each `gseq n` a unit.
- Uses from project: [`approxProd`, `approxFactor_isUnit`]
- Used by: `dlog_approxProd`, `dlog_surjective_onto_psiId`
- Visibility: private
- Lines: 1287–1291 (proof ~3 lines)
- Notes: none

### theorem approxProd_normOp
- Type: `private theorem approxProd_normOp {gseq} (hg : ∀ n, IsUnit (gseq n)) (hN : ∀ n, normOp (gseq n) = gseq n) (n) : normOp (approxProd p gseq n) = approxProd p gseq n`
- What: Each partial product `hₙ` is `𝒩`-fixed.
- How: Induction on `n`; each factor is `𝒩`-fixed (`normOp_pow`/`normOp_inverse` per parity), and `normOp_mul` distributes.
- Hypotheses: each `gseq n` a unit and `𝒩`-fixed.
- Uses from project: [`normOp`, `approxProd`, `approxFactor`, `normOp_pow`, `normOp_inverse`, `normOp_mul`]
- Used by: `dlog_surjective_onto_psiId`
- Visibility: private
- Lines: 1293–1304 (proof ~10 lines)
- Notes: none

### theorem dlog_approxFactor
- Type: `private theorem dlog_approxFactor {gseq fseq} (hg : ∀ n, IsUnit (gseq n)) (hstep : ∀ n, dlog p (gseq (n+1)) = fseq n + C(p)·fseq (n+1)) (n) : dlog p (approxFactor p gseq n) = (- C p)^n * (fseq n + C(p)·fseq (n+1))`
- What: `Δ(approxFactor n) = (−Cp)ⁿ·(f_n + p·f_{n+1})` (the `n`-th telescope summand).
- How: `dlog_pow` gives `Δ(g_{n+1}^{p^n}) = p^n·Δg_{n+1}`; substitute `hstep`, handle sign by parity (`Even.neg_one_pow`/`Odd.neg_one_pow`, `dlog_inverse` for odd `n`).
- Hypotheses: each `gseq n` a unit; the step identity `hstep`.
- Uses from project: [`dlog`, `approxFactor`, `dlog_pow`, `dlog_inverse`]
- Used by: `dlog_approxProd`
- Visibility: private
- Lines: 1306–1321 (proof ~9 lines)
- Notes: none

### theorem dlog_approxProd
- Type: `private theorem dlog_approxProd {gseq fseq} (hg) (hstep) (n) : dlog p (approxProd p gseq n) = fseq 0 - (- C p)^n * fseq n`
- What: **The telescoping identity (lem:log der red mod p)**: `Δ hₙ = f₀ − (−p)ⁿ·f_n`.
- How: Induction on `n`; `dlog_mul` (product into sum) + `dlog_approxFactor`, `pow_succ`, `ring` telescopes.
- Hypotheses: each `gseq n` a unit; the step identity.
- Uses from project: [`dlog`, `approxProd`, `dlog_mul`, `dlog_one`, `approxProd_isUnit`, `approxFactor_isUnit`, `dlog_approxFactor`]
- Used by: `dlog_surjective_onto_psiId`
- Visibility: private
- Lines: 1323–1335 (proof ~6 lines)
- Notes: none

### theorem continuous_of_coeff
- Type: `theorem continuous_of_coeff {X} [TopologicalSpace X] (g : X → PowerSeries ℤ_[p]) (h : ∀ n, Continuous (fun x => coeff n (g x))) : Continuous g`
- What: A map into `ℤ_p⟦T⟧` is continuous iff continuous in every coefficient.
- How: `continuous_iff_continuousAt` + `WithPiTopology.tendsto_iff_coeff_tendsto`.
- Hypotheses: each coefficient map continuous.
- Uses from project: []
- Used by: `phiSeries_continuous`
- Visibility: public (in `section Continuity`, `variable {p}`)
- Lines: 1352–1358 (proof ~4 lines)
- Notes: none

### theorem coeff_phiSeries_finite
- Type: `private theorem coeff_phiSeries_finite (G : PowerSeries ℤ_[p]) (n : ℕ) : coeff n (phiSeries p G) = ∑ d ∈ range (n+1), (coeff d G) • coeff n (((1+X)^p − 1)^d)`
- What: `coeff n (φG) = Σ_{d ≤ n} G_d · coeff n(S^d)` (finite substitution-coefficient formula; `S = (1+T)^p−1` has order 1).
- How: `coeff_subst'` then restrict the finsum support to `range (n+1)` (terms `d > n` vanish since `S^d` has order `d`, via `X_dvd_iff` + `coeff_X_pow_mul'`).
- Hypotheses: none.
- Uses from project: [`phiSeries`, `hasSubst_one_add_X_pow_sub_one`]
- Used by: `phiSeries_continuous`, `coeff_phiSeries_split`
- Visibility: private
- Lines: 1362–1376 (proof ~10 lines)
- Notes: none. Uses `push Not`.

### theorem phiSeries_continuous
- Type: `theorem phiSeries_continuous : Continuous (phiSeries p : PowerSeries ℤ_[p] → PowerSeries ℤ_[p])`
- What: `φ = subst((1+T)^p−1)` is continuous (each output coefficient is a finite `ℤ_[p]`-linear combination of inputs).
- How: `continuous_of_coeff`; per output coefficient, rewrite via `coeff_phiSeries_finite` as a finite sum of scalar multiples of input coefficients (`continuous_coeff`).
- Hypotheses: none.
- Uses from project: [`phiSeries`, `continuous_of_coeff`, `coeff_phiSeries_finite`]
- Used by: `digitAssembly_continuous`
- Visibility: public
- Lines: 1378–1389 (proof ~8 lines)
- Notes: none

### def digitAssembly
- Type: `private def digitAssembly : (Fin p → PowerSeries ℤ_[p]) ≃ PowerSeries ℤ_[p]`
- What: The digit-assembly bijection `(G_i) ↦ Σ_i (1+T)^i φ(G_i)` (an `Equiv`).
- How: `toFun` the assembly sum, `invFun` the chosen digit family; left/right inverse from `existsUnique_digits_padicInt.choose_spec`.
- Hypotheses: none.
- Uses from project: [`phiSeries`, `existsUnique_digits_padicInt`]
- Used by: `digitAssembly_continuous`, `digitHomeo`
- Visibility: private
- Lines: 1393–1400 (def ~6 lines)
- Notes: none

### theorem digitAssembly_continuous
- Type: `private theorem digitAssembly_continuous : Continuous (digitAssembly p)`
- What: The digit-assembly map is continuous.
- How: It is a finite sum of `const · φ(G_i)`; `continuous_finsetSum` + `phiSeries_continuous.comp (continuous_apply i)`.
- Hypotheses: none.
- Uses from project: [`digitAssembly`, `phiSeries`, `phiSeries_continuous`]
- Used by: `digitHomeo`
- Visibility: private
- Lines: 1402–1406 (proof ~3 lines)
- Notes: none

### def digitHomeo
- Type: `private noncomputable def digitHomeo : (Fin p → PowerSeries ℤ_[p]) ≃ₜ PowerSeries ℤ_[p]`
- What: The digit map as a homeomorphism (continuous bijection of compact Hausdorff spaces).
- How: `Continuous.homeoOfEquivCompactToT2` applied to `digitAssembly` + `digitAssembly_continuous`.
- Hypotheses: none.
- Uses from project: [`digitAssembly`, `digitAssembly_continuous`]
- Used by: `digitMatrix_eq_symm`, `digitMatrix_continuous`
- Visibility: private
- Lines: 1408–1410 (def ~1 line)
- Notes: none

### theorem digitMatrix_eq_symm
- Type: `private theorem digitMatrix_eq_symm (f) (j : Fin p) : (fun i => digitMatrix f i j) = (digitHomeo p).symm (f * (1 + X) ^ (j : ℕ))`
- What: The `j`-th column of `digitMatrix f` is `digitHomeo.symm(f·(1+T)^j)` (the digit family of `f·(1+T)^j`).
- How: `existsUnique_digits_padicInt … .unique` of `digitMatrix_col_isDigitDecomp` against `digitHomeo.apply_symm_apply`.
- Hypotheses: none.
- Uses from project: [`digitMatrix`, `digitHomeo`, `existsUnique_digits_padicInt`, `digitMatrix_col_isDigitDecomp`]
- Used by: `digitMatrix_continuous`
- Visibility: private
- Lines: 1412–1418 (proof ~3 lines)
- Notes: none

### theorem digitMatrix_continuous
- Type: `theorem digitMatrix_continuous (i j : Fin p) : Continuous (fun f : PowerSeries ℤ_[p] => digitMatrix f i j)`
- What: Each entry of `digitMatrix` is continuous in `f`.
- How: Rewrite the entry as `(digitHomeo.symm (f·(1+T)^j)) i` (`digitMatrix_eq_symm`); continuous as `apply i ∘ homeo.symm ∘ (·*const)`.
- Hypotheses: none.
- Uses from project: [`digitMatrix`, `digitHomeo`, `digitMatrix_eq_symm`]
- Used by: `normOp_continuous`
- Visibility: public
- Lines: 1420–1426 (proof ~4 lines)
- Notes: none

### theorem normOp_continuous
- Type: `theorem normOp_continuous : Continuous (normOp (p := p))`
- What: **`𝒩` is continuous** for the coefficientwise topology.
- How: `normOp = det ∘ digitMatrix` (`normOp_eq_det`); `det` is a finite sum of products of entries (`Matrix.det_apply`), each entry continuous (`digitMatrix_continuous`).
- Hypotheses: none.
- Uses from project: [`normOp`, `normOp_eq_det`, `digitMatrix`, `digitMatrix_continuous`]
- Used by: `dlog_surjective_onto_psiId`
- Visibility: public
- Lines: 1428–1435 (proof ~5 lines)
- Notes: none

### theorem dlog_surjective_onto_psiId
- Type: `theorem dlog_surjective_onto_psiId {F} (hF : F ∈ psiIdSeries p) : ∃ g, IsUnit g ∧ normOp g = g ∧ dlog p g = F`
- What: **RJW thm:log der — the Coleman–Coates–Wiles short exact sequence, surjectivity half**: every `ψ`-fixed series is the log-derivative of an `𝒩`-fixed unit.
- How: From `exists_approx_seq` get `gₙ ∈ 𝒲`, `fₙ ∈ (ψ=id)`; form `hₙ = approxProd`, with `Δ hₙ = F − (−p)ⁿ fₙ` (`dlog_approxProd`); clear to `(1+T)∂(hₙ) = (F − (−p)ⁿfₙ)·hₙ`; take a convergent subsequence `h_{φj} → h` (`exists_subseq_tendsto`); `h` a unit (`isClosed_isUnit`) and `𝒩`-fixed (`normOp_continuous` + `tendsto_nhds_unique`); pass the cleared form through the limit (∂ continuous, `(−p)^{φj}f_{φj} → 0` by `squeeze_zero`/`tendsto_pow_atTop_nhds_zero_of_lt_one`) to get `(1+T)∂h = F·h`, hence `Δh = F`. Hinges on `exists_approx_seq`, `dlog_approxProd`, `normOp_continuous`, `exists_subseq_tendsto`.
- Hypotheses: `F ∈ psiIdSeries p` (`ψ`-fixed).
- Uses from project: [`psiIdSeries`, `dlog`, `normOp`, `normOp_continuous`, `derivativeFun`, `exists_approx_seq`, `approxProd`, `approxProd_isUnit`, `approxProd_normOp`, `dlog_approxProd`, `exists_subseq_tendsto`, `isClosed_isUnit`, `tendsto_coeff`]
- Used by: unused in file (top-level result)
- Visibility: public (scoped `PowerSeries.WithPiTopology` open)
- Lines: 1439–1534 (proof ~73 lines)
- Notes: OVER-50 — proof body ~73 lines (1462→1534). Needs /decompose-proof. `open scoped … in`. The headline theorem of the file.

### theorem eq_C_constantCoeff_of_derivativeFun_zero
- Type: `private theorem eq_C_constantCoeff_of_derivativeFun_zero (g) (h : derivativeFun g = 0) : g = PowerSeries.C (constantCoeff g)`
- What: A power series with vanishing formal derivative equals its constant coefficient.
- How: Per coefficient; `n=0` trivial, `n=m+1` uses `coeff_derivativeFun` (`(m+1)·coeff_{m+1} g = 0`) with `(m+1)` a non-zero-divisor (`Nat.cast_add_one_ne_zero`).
- Hypotheses: `∂g = 0`.
- Uses from project: [`derivativeFun`]
- Used by: `dlog_eq_zero_normOp_fixed`
- Visibility: private
- Lines: 1536–1549 (proof ~11 lines)
- Notes: none

### theorem normOp_C
- Type: `theorem normOp_C (c : ℤ_[p]) : normOp (PowerSeries.C c) = PowerSeries.C (c ^ p)`
- What: `𝒩(C c) = C(c^p)`.
- How: `normOp_eq_det`, `digitMatrix_C` (`C c • 1`), `det_smul` + `det_one`, `Fintype.card_fin`, `map_pow`.
- Hypotheses: none.
- Uses from project: [`normOp`, `normOp_eq_det`, `digitMatrix_C`]
- Used by: `dlog_eq_zero_normOp_fixed`
- Visibility: public
- Lines: 1551–1555 (proof ~2 lines)
- Notes: none

### theorem dlog_eq_zero_normOp_fixed
- Type: `theorem dlog_eq_zero_normOp_fixed {g} (hg : IsUnit g) (hN : normOp g = g) (hd : dlog p g = 0) : ∃ c : ℤ_[p], c ^ p = c ∧ g = PowerSeries.C c`
- What: **RJW rem:ker Δ** — the kernel of `Δ` on `𝒩`-fixed units is `μ_{p−1}`: a constant `𝒩`-fixed unit `f` satisfies `f^p = f`.
- How: `dlog g = (1+X)·g'·g⁻¹ = 0` with `(1+X)`, `g⁻¹` units forces `g' = 0`, so `g = C c` (`eq_C_constantCoeff_of_derivativeFun_zero`); `𝒩 g = g` + `normOp_C` gives `C(c^p) = C c`, hence `c^p = c` (`C_injective`).
- Hypotheses: `g` a unit, `𝒩`-fixed, with `dlog g = 0`.
- Uses from project: [`normOp`, `dlog`, `normOp_C`, `derivativeFun`, `eq_C_constantCoeff_of_derivativeFun_zero`]
- Used by: unused in file (top-level result)
- Visibility: public
- Lines: 1557–1578 (proof ~16 lines)
- Notes: long-ish (~16 lines). Under 30.

### theorem coeff_one_one_add_X_pow
- Type: `private theorem coeff_one_one_add_X_pow : coeff 1 ((1 + X : PowerSeries ℤ_[p]) ^ p) = (p : ℤ_[p])`
- What: `[T¹]((1+T)^p) = p`.
- How: From `del_one_add_X_pow p p` (`Δ((1+T)^p) = p(1+T)^p`), take `[T⁰]`; use `[T¹]f = [T⁰](∂f)` after splitting `(1+X)·∂ = ∂ + X·∂`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.del`, `del_one_add_X_pow`, `derivativeFun`]
- Used by: `coeff_S_pow_diag`
- Visibility: private
- Lines: 1591–1607 (proof ~12 lines)
- Notes: none

### theorem coeff_S_pow_vanish
- Type: `private theorem coeff_S_pow_vanish {d n} (hdn : n < d) : coeff n (((1 + X)^p − 1)^d) = 0`
- What: `[Tⁿ](S^d) = 0` for `n < d` (`S = (1+T)^p−1` has order 1).
- How: `X_dvd_iff` writes `S = X·U`, so `S^d = X^d·U^d`; `coeff_X_pow_mul'` with `n < d` gives 0.
- Hypotheses: `n < d`.
- Uses from project: []
- Used by: unused in file (companion to `coeff_S_pow_diag`; `coeff_phiSeries_split` uses `coeff_phiSeries_finite` directly)
- Visibility: private
- Lines: 1609–1614 (proof ~3 lines)
- Notes: none

### theorem coeff_S_pow_diag
- Type: `private theorem coeff_S_pow_diag {d} : coeff d (((1 + X)^p − 1)^d) = (p : ℤ_[p]) ^ d`
- What: `[Tᵈ](S^d) = pᵈ` (leading coefficient: `S = pT + O(T²)`).
- How: `S = X·U` with `U(0) = p` (from `coeff_one_one_add_X_pow`); `S^d = X^d·U^d`, so `[Tᵈ] = [T⁰](U^d) = U(0)^d = p^d`.
- Hypotheses: none.
- Uses from project: [`coeff_one_one_add_X_pow`]
- Used by: `mk_solCoeff_sub_phi`
- Visibility: private
- Lines: 1616–1634 (proof ~14 lines)
- Notes: none

### theorem coeff_phiSeries_split
- Type: `private theorem coeff_phiSeries_split (G) (n) : coeff n (phiSeries p G) = ∑ d ∈ range (n+1), (coeff d G) • coeff n (((1+X)^p − 1)^d)`
- What: Restatement (alias) of `coeff_phiSeries_finite` — the substitution coefficient formula.
- How: `:= coeff_phiSeries_finite`.
- Hypotheses: none.
- Uses from project: [`phiSeries`, `coeff_phiSeries_finite`]
- Used by: `mk_solCoeff_sub_phi`
- Visibility: private
- Lines: 1636–1642 (term-mode, 1 line)
- Notes: none

### theorem isUnit_one_sub_p_pow
- Type: `private theorem isUnit_one_sub_p_pow {n} (hn : 1 ≤ n) : IsUnit (1 - (p : ℤ_[p]) ^ n)`
- What: `1 − pⁿ` is a unit of `ℤ_[p]` for `n ≥ 1`.
- How: `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits`: `pⁿ` is a non-unit since `‖pⁿ‖ = ‖p‖ⁿ < 1`.
- Hypotheses: `n ≥ 1`.
- Uses from project: []
- Used by: `solCoeff`(implicitly), `mk_solCoeff_sub_phi`
- Visibility: private
- Lines: 1644–1650 (proof ~5 lines)
- Notes: none

### def solCoeff
- Type: `private def solCoeff (F : PowerSeries ℤ_[p]) : ℕ → ℤ_[p]` (well-founded recursion)
- What: The recursively-defined coefficients of the solution `G` to `(1 − φ)G = F`: `G₀ = 0`, `Gₙ = (1−pⁿ)⁻¹·(Fₙ + Σ_{d<n} G_d·[Tⁿ](S^d))` for `n ≥ 1`.
- How: Strong recursion; `decreasing_by` discharges `d < n` from `Finset.mem_range`.
- Hypotheses: target `F`.
- Uses from project: []
- Used by: `solCoeff_zero`, `solCoeff_eq`, `mk_solCoeff_sub_phi`, `exists_one_sub_phi_eq`
- Visibility: private
- Lines: 1652–1659 (def ~6 lines)
- Notes: none. Well-founded recursion.

### theorem solCoeff_zero
- Type: `private theorem solCoeff_zero (F) : solCoeff p F 0 = 0`
- What: `G₀ = 0`.
- How: Unfold + `if_pos rfl`.
- Hypotheses: none.
- Uses from project: [`solCoeff`]
- Used by: `mk_solCoeff_sub_phi`
- Visibility: private
- Lines: 1661–1662 (proof 1 line)
- Notes: none

### theorem solCoeff_eq
- Type: `private theorem solCoeff_eq (F) {n} (hn : n ≠ 0) : solCoeff p F n = Ring.inverse (1 − pⁿ) * (coeff n F + ∑ d ∈ range n, (solCoeff p F d) * coeff n (S^d))`
- What: The unfolded recursion for `n ≥ 1` (with the `attach`-sum collapsed to a plain `range` sum).
- How: Unfold + `if_neg hn`, then `Finset.sum_attach`.
- Hypotheses: `n ≠ 0`.
- Uses from project: [`solCoeff`]
- Used by: `mk_solCoeff_sub_phi`
- Visibility: private
- Lines: 1664–1670 (proof ~3 lines)
- Notes: none

### theorem mk_solCoeff_sub_phi
- Type: `private theorem mk_solCoeff_sub_phi (F) (h0 : constantCoeff F = 0) : PowerSeries.mk (solCoeff p F) - phiSeries p (PowerSeries.mk (solCoeff p F)) = F`
- What: The constructed series `G = mk(solCoeff F)` solves `(1 − φ)G = F` when `F(0) = 0`.
- How: Per coefficient; `n=0` uses `constantCoeff_phiSeries` and `F(0)=0`; `n ≥ 1` uses `coeff_phiSeries_split` peeling the diagonal `d=n` term (`coeff_S_pow_diag` gives `pⁿ`), then `solCoeff_eq` and `isUnit_one_sub_p_pow` cancel `(1−pⁿ)` (`linear_combination`).
- Hypotheses: `F(0) = 0`.
- Uses from project: [`solCoeff`, `phiSeries`, `solCoeff_zero`, `solCoeff_eq`, `constantCoeff_phiSeries`, `coeff_phiSeries_split`, `coeff_S_pow_diag`, `isUnit_one_sub_p_pow`]
- Used by: `exists_one_sub_phi_eq`
- Visibility: private
- Lines: 1672–1700 (proof ~24 lines)
- Notes: none

### theorem one_sub_phi_psiId_mem_psiZero
- Type: `theorem one_sub_phi_psiId_mem_psiZero {F} (hF : F ∈ psiIdSeries p) : F - phiHom p F ∈ psiZeroSeries p`
- What: **RJW lem:rest zp* (forward half)**: `(1−φ)` maps `ℤ_p⟦T⟧^{ψ=id}` into `ℤ_p⟦T⟧^{ψ=0}`.
- How: `ψ(F − φF) = ψF − ψφF = F − F = 0` (`psiSeries_sub`, `psiSeries_phi_padicInt`, `ψF = F`).
- Hypotheses: `F` is `ψ`-fixed.
- Uses from project: [`psiIdSeries`, `psiZeroSeries`, `psiSeries`, `phiHom_apply`, `psiSeries_sub`, `psiSeries_phi_padicInt`]
- Used by: unused in file (top-level result)
- Visibility: public
- Lines: 1702–1709 (proof ~4 lines)
- Notes: none

### theorem exists_one_sub_phi_eq
- Type: `theorem exists_one_sub_phi_eq {F} (hF : F ∈ psiZeroSeries p) (h0 : constantCoeff F = 0) : ∃ G ∈ psiIdSeries p, G - phiHom p G = F`
- What: **The converse half of lem:rest zp***: every `ψ=0` series with `F(0)=0` is `(1−φ)G` for some `ψ`-fixed `G`.
- How: `G = mk(solCoeff F)` solves `(1−φ)G = F` (`mk_solCoeff_sub_phi`); `ψG = G` follows by applying `ψ` to `G − φG = F` (`psiSeries_sub`, `psiSeries_phi_padicInt`, `ψF = 0`), giving `ψG − G = 0`.
- Hypotheses: `F ∈ psiZeroSeries p` and `F(0) = 0`.
- Uses from project: [`psiIdSeries`, `psiZeroSeries`, `psiSeries`, `solCoeff`, `phiHom_apply`, `mk_solCoeff_sub_phi`, `psiSeries_sub`, `psiSeries_phi_padicInt`]
- Used by: unused in file (top-level result)
- Visibility: public
- Lines: 1711–1727 (proof ~11 lines)
- Notes: none

---

## File Summary

**Total declarations: 80**
- defs: 7 (`psiIdSeries`, `psiZeroSeries`, `AWfp`, `AfpCoe`, `WfpCoe`, `SfpSum`, `approxFactor`, `approxProd`, `digitAssembly`, `digitHomeo`, `solCoeff` — note these include both `Submodule` defs and the `Equiv`/`Homeo`/recursion defs; **11 defs** total) → corrected: **defs = 11**
- lemmas + theorems: **67**
- instances: **0**
- (structures/classes/abbrevs/inductives: 0)

(Decl-kind tally: 11 `def` + 69 `theorem` = 80 declarations. Two of the 80 are `def`-as-`Submodule` (`psiIdSeries`, `psiZeroSeries`); the `theorem` count includes the headline results and all private helpers.)

**Key API (used by ≥3 decls in this file):**
- `psiSeries_sub` (5+)
- `psiIdSeries` (4)
- `dlog_mem_psiIdSeries` (used by `exists_normOp_dlog_modEq`, `exists_approx_step`; also the conceptual `A ⊆ B`)
- `dlog_mul`, `dlog_one` (3 each)
- `AWfp`, `AfpCoe`, `WfpCoe`, `SfpSum` (recursion family, each used by ≥3 helpers)
- `existsUnique_digits_zmod` (3), `psiSeries_eq_of_isDigitDecomp_zmod` (5)
- `solCoeff` (4)

**Unused in file (no in-file consumer; several are exported top-level results):**
- `del_phiHom` (superseded internally by `del_phiSeries`)
- `coeff_S_pow_vanish` (companion lemma; the split uses `coeff_phiSeries_finite`)
- Top-level results with no in-file consumer (intended for downstream import): `dlog_surjective_onto_psiId`, `dlog_eq_zero_normOp_fixed`, `one_sub_phi_psiId_mem_psiZero`, `exists_one_sub_phi_eq`

**Declarations with `sorry`: NONE.** The file is closed sorry-free in this pass (per header "Status T1203"). The two leaves mentioned in the header docstring (`fp_series_eq_dlog_add_frobC`, `dlog_surjective_onto_psiId`) are stated as **now CLOSED** and contain no `sorry`.

**`set_option`: NONE.** No `set_option`, no `admit`, no `TODO` markers in declarations.

**Proofs > 50 lines (need /decompose-proof): 2**
- `dlog_surjective_onto_psiId` — ~73-line proof (1462→1534), the headline CCW exact-sequence theorem.
- `digitMatrix_del` — ~50-line proof (252→306), identity K (borderline-at-50; flag).

**Proofs 30–50 lines: 4**
- `dlog_mem_psiIdSeries` — ~42 lines (lem:log der 1).
- `fp_series_eq_dlog_add_frobC` — ~38 lines (lem:B mod p 2, "most delicate and technical part").
- `psiId_one_add_X_div_X_phi_eq_zero` — ~43 lines (lem:B mod p ψ-killing step).
- `derivation_det` — ~32 lines (Jacobi's formula).

(Several further proofs sit in the high-20s — `digits_unique_zmod` ~28, `mk_solCoeff_sub_phi` ~24, `exists_approx_step`/`exists_approx_seq`/`exists_normOp_dlog_modEq` ~21–22, `exists_normOp_fixed_lift` ~26 — under the 30-line threshold but candidates if golfing pressure increases.)
