/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Coleman.Map

/-!
# The logarithmic derivative: the Coleman–Coates–Wiles exact sequence (RJW §12.2.1) — E12.2

`thm:log der` (TeX 3280–3379): the short exact sequence
`0 → μ_{p−1} → (ℤ_p⟦T⟧^×)^{𝒩=id} →[Δ] ℤ_p⟦T⟧^{ψ=id} → 0`. This is the hardest
mathematics in Part II; `lem:B mod p 2` (the explicit `𝔽_p⟦T⟧` construction) is, per the
authors, "the most delicate and technical part". The kernel `μ_{p−1}` is `rem:ker Δ`
(constants `𝒩`-fixed force `f^p = f`); surjectivity reduces mod `p` (`lem:log der red
mod p`, successive approximation + `ℤ_p⟦T⟧^×` compactness from §10) to `A = B`
(`lem:A mod p` + `lem:B mod p`).

Status (T1203 execution). Closed sorry-free in this pass:
* the `ψ`-`Submodule` proof-fields (`psiIdSeries`, `psiZeroSeries`);
* `del_phiHom` (`Δ ∘ φ = p · φ ∘ Δ`, from `one_add_mul_derivative_phiSeries`);
* `dlog_eq_zero_normOp_fixed` (`rem:ker Δ`: `dlog g = 0`, `𝒩 g = g` ⟹ `g = C c`, `c^p = c`);
* `one_sub_phi_psiId_mem_psiZero` (forward half of `lem:rest zp*`);
* `exists_normOp_fixed_lift` (`lem:A mod p`), with its new mod-`p^k` continuity layer
  (`normOp_modEq_of_modEq`, `modEqPow_of_tendsto`, `eq_of_forall_modEqPow`);
* `exists_one_sub_phi_eq` (converse half of `lem:rest zp*`), via the coefficientwise
  `(1−pⁿ)`-recursion `solCoeff` solving `(1−φ)G = F` (`mk_solCoeff_sub_phi`);
* **`dlog_mem_psiIdSeries` (`lem:log der 1`) — now CLOSED** via the determinant/Jacobi
  route (replacing RJW's non-formal `μ_p`-product `φ(f) = ∏_η f((1+T)η−1)`, replan R10.4).
  New reusable infrastructure: `derivation_det` (Jacobi's `D(det M) = ∑_i det(M[row i↦D])`,
  built from the Leibniz `derivation_finset_prod`), `det_updateRow_eq_sum_adjugate`
  (cofactor expansion), `digitMatrix_del` (identity K:
  `(digitMatrix Δf)_{ij} = (i−j)·M_{ij} + p·Δ(M_{ij})`), `del_det_eq_smul_trace`
  (`Δ(det M) = det M • tr((M.map Δ)·N)`), `trace_D_N_zero`, and the `Δ`-Leibniz API
  (`del_mul`, `del_sum`, `del_phiSeries`, `del_one_add_X_pow`). The proof: with `M = digitMatrix f`,
  `N = M⁻¹`, `f = det M`, one gets `tr(digitMatrix(dlog f)) = 0 + p·dlog f` (identity K's
  off-diagonal trace vanishes, diagonal gives `p·dlog f`), and `tr(digitMatrix·) = p·ψ(·)`
  (`trace_digitMatrix`) plus `p`-cancellation give `ψ(dlog f) = dlog f`.

Two leaves remain (see the per-declaration obstacle notes), both entangled with the
project's deferred non-formal `Eqphipsi` (`φ∘ψ(F) = p⁻¹∑_ξ F((1+T)ξ−1)`, FormalPsi.lean):
* `fp_series_eq_dlog_add_frobC` (`lem:B mod p 2`, "the most delicate and technical part")
  — restated to the faithful `𝔽_p⟦T⟧ = Δ(𝔽_p⟦T⟧^×) + (T+1)/T·C`; needs the inductive
  `α`-filtration (`d_n=d_{np}` invariant) + the `∏(1−α_n Tⁿ)` T-adic product (mathlib hook
  `multipliable` via `order → ∞`). ~200 LOC of `𝔽_p`-combinatorics; not blocked by
  `Eqphipsi`, but also needs `dlog`-continuity for the product's log-derivative.
* `dlog_surjective_onto_psiId` (`thm:log der`) — `A = B` mod `p` + successive approximation
  `h_n = ∏ g_k^{(−1)^{k−1}p^{k−1}}` (the `dlog`-homomorphism layer `dlog_mul`/`dlog_pow`
  below is in place) + the `ℤ_p⟦T⟧^×` compactness limit (§10 substrate present; still needs
  `dlog`-continuity). The `B ⊆ A` input (`lem:B mod p`) uses the `Eqphipsi`-based
  "`ψ` fixes `(T+1)/T`" (`LemmaPsiInvariant`, TeX 1521).
-/

open PadicLFunctions PadicLFunctions.Coleman PowerSeries

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `ψ = id` subspace of `ℤ_p⟦T⟧` (RJW `ℤ_p⟦T⟧^{ψ=id}`), via the series trace
operator `psiSeries`. -/
def psiIdSeries : Submodule ℤ_[p] (PowerSeries ℤ_[p]) where
  carrier := {F | psiSeries p F = F}
  add_mem' {F G} hF hG := by
    change psiSeries p (F + G) = F + G
    rw [psiSeries_add_padicInt, hF, hG]
  zero_mem' := by
    change psiSeries p (0 : PowerSeries ℤ_[p]) = 0
    simpa using (psiSeries_add_padicInt (p := p) 0 0).symm
  smul_mem' c F hF := by
    change psiSeries p (c • F) = c • F
    rw [PowerSeries.smul_eq_C_mul, psiSeries_C_mul_padicInt, show psiSeries p F = F from hF]

/-- The `ψ = 0` subspace of `ℤ_p⟦T⟧` (RJW `ℤ_p⟦T⟧^{ψ=0}`). -/
def psiZeroSeries : Submodule ℤ_[p] (PowerSeries ℤ_[p]) where
  carrier := {F | psiSeries p F = 0}
  add_mem' {F G} hF hG := by
    change psiSeries p (F + G) = 0
    rw [psiSeries_add_padicInt, show psiSeries p F = 0 from hF,
      show psiSeries p G = 0 from hG, add_zero]
  zero_mem' := by
    change psiSeries p (0 : PowerSeries ℤ_[p]) = 0
    simpa using (psiSeries_add_padicInt (p := p) 0 0).symm
  smul_mem' c F hF := by
    change psiSeries p (c • F) = 0
    rw [PowerSeries.smul_eq_C_mul, psiSeries_C_mul_padicInt, show psiSeries p F = 0 from hF,
      mul_zero]

/-- `ψ` is subtractive over `ℤ_[p]` (from additivity). -/
theorem psiSeries_sub (F G : PowerSeries ℤ_[p]) :
    psiSeries p (F - G) = psiSeries p F - psiSeries p G := by
  have h := psiSeries_add_padicInt (p := p) (F - G) G
  rw [sub_add_cancel] at h
  rw [h]; ring

/-- `Δ ∘ φ = p · φ ∘ Δ` on power series (RJW TeX 3301, "easy to see from the
definitions") — the engine of `lem:log der 1`. Stated for the additive `del = ∂`
(`PadicMeasure.del`). -/
theorem del_phiHom (f : PowerSeries ℤ_[p]) :
    PadicMeasure.del p (phiHom p f)
      = (p : PowerSeries ℤ_[p]) * phiHom p (PadicMeasure.del p f) := by
  rw [phiHom_apply, PadicMeasure.del, PadicMeasure.del,
    one_add_mul_derivative_phiSeries, phiHom_apply, PowerSeries.smul_eq_C_mul,
    map_natCast]

/-! ### Jacobi's formula for the derivative of a determinant (for `lem:log der 1`)

RJW prove `lem:log der 1` from the `μ_p`-product `φ(f) = ∏_η f((1+T)η−1)` (replan R10.4:
*not* a formal power-series identity). The formal substitute is **Jacobi's formula**
`Δ(det M) = ∑_i det(M[row i ↦ Δ(row i)])`, derived here over `ℤ_p⟦T⟧`-matrices from the
Leibniz rule for the derivation `PowerSeries.derivative` applied to the Leibniz determinant
expansion `det M = ∑_σ ε(σ) ∏_i M_{σi,i}`. Mathlib has no determinant-derivative lemma, so
we build it. -/

/-- **Leibniz rule over a `Finset` product** for a derivation on power series:
`D(∏_{i∈s} g i) = ∑_{i∈s} (∏_{j∈s\{i}} g j) • D(g i)`. -/
private theorem derivation_finset_prod {R : Type*} [CommRing R]
    (D : Derivation R (PowerSeries R) (PowerSeries R)) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → PowerSeries R) :
    D (∏ i ∈ s, g i) = ∑ i ∈ s, (∏ j ∈ s.erase i, g j) • D (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha, Finset.smul_sum,
      Finset.erase_insert ha, add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hia.symm, Finset.prod_insert
      (fun h => ha (Finset.mem_of_mem_erase h)), mul_smul]

/-- **Jacobi's formula** (row form): for a square matrix `M` over `ℤ_p⟦T⟧` and a derivation
`D`, `D(det M) = ∑_i det(M with row i differentiated)`. From `derivation_finset_prod`
applied to the Leibniz expansion `det M = ∑_σ ε(σ) ∏_i M_{σi,i}`, reorganised by the
substitution `i ↦ σ i`. -/
private theorem derivation_det {R : Type*} [CommRing R] {n : ℕ}
    (D : Derivation R (PowerSeries R) (PowerSeries R))
    (M : Matrix (Fin n) (Fin n) (PowerSeries R)) :
    D (M.det) = ∑ i, (M.updateRow i (fun j => D (M i j))).det := by
  classical
  rw [Matrix.det_apply', map_sum]
  have hLHS : ∀ σ : Equiv.Perm (Fin n),
      D (((Equiv.Perm.sign σ : ℤ) : PowerSeries R) * ∏ i, M (σ i) i)
        = ∑ i, ((Equiv.Perm.sign σ : ℤ) : PowerSeries R) *
            ((∏ k ∈ Finset.univ.erase i, M (σ k) k) * D (M (σ i) i)) := by
    intro σ
    rw [D.leibniz, Derivation.map_intCast, smul_zero, add_zero, derivation_finset_prod,
      Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [smul_eq_mul, smul_eq_mul])
  rw [Finset.sum_congr rfl (fun σ _ => hLHS σ)]
  have hRHS : ∀ i : Fin n, (M.updateRow i (fun j => D (M i j))).det
      = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : PowerSeries R) *
          ((∏ k ∈ Finset.univ.erase (σ.symm i), M (σ k) k) * D (M i (σ.symm i))) := by
    intro i
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (σ.symm i))]
    have hdiag : (M.updateRow i (fun j => D (M i j))) (σ (σ.symm i)) (σ.symm i)
        = D (M i (σ.symm i)) := by rw [Equiv.apply_symm_apply, Matrix.updateRow_self]
    rw [hdiag]
    congr 1
    refine Finset.prod_congr rfl (fun k hk => ?_)
    have hki : σ k ≠ i := fun h =>
      (Finset.ne_of_mem_erase hk) (by rw [← h, Equiv.symm_apply_apply])
    rw [Matrix.updateRow_ne hki]
  rw [Finset.sum_congr rfl (fun i _ => hRHS i)]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← Equiv.sum_comp σ (fun i => ((Equiv.Perm.sign σ : ℤ) : PowerSeries R) *
    ((∏ k ∈ Finset.univ.erase (σ.symm i), M (σ k) k) * D (M i (σ.symm i))))]
  exact Finset.sum_congr rfl (fun i _ => by rw [Equiv.symm_apply_apply])

/-- `det(M with row `i` replaced by `v`) = ∑_j v_j · adjugate(M)_{j,i}` (cofactor/Cramer
expansion along the replaced row, via `cramer_eq_adjugate_mulVec` on the transpose). -/
private theorem det_updateRow_eq_sum_adjugate {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (i : Fin n) (v : Fin n → R) :
    (M.updateRow i v).det = ∑ j, v j * Matrix.adjugate M j i := by
  rw [← Matrix.det_transpose, ← Matrix.updateCol_transpose, ← Matrix.cramer_apply,
    Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl
    (fun j _ => by rw [mul_comm, ← Matrix.adjugate_transpose, Matrix.transpose_apply])

/-! ### `Δ = (1+T)∂` as a Leibniz operator, and the digit-matrix derivative identity

`Δ = del` is `(1+T)` times the derivation `derivativeFun`, so it satisfies a Leibniz rule
(`del_mul`) and commutes with finite sums (`del_sum`). The key new lemma is `digitMatrix_del`
(identity **K**): differentiating the column-digit identity
`f·(1+T)^j = ∑_i (1+T)^i φ((digitMatrix f)_{ij})` (`digitMatrix_col_isDigitDecomp`) and
re-extracting digits (`existsUnique_digits_padicInt`) gives
`(digitMatrix(Δf))_{ij} = (i−j)·(digitMatrix f)_{ij} + p·Δ((digitMatrix f)_{ij})`.
On the diagonal this is `p·Δ(M_{ii})`, the formal shadow of the chain-rule step
`Δ(f((1+T)η−1)) = (Δf)((1+T)η−1)` that RJW sum over `μ_p`. -/

/-- Leibniz rule for `Δ = del`: `Δ(ab) = (Δa)·b + a·(Δb)`. -/
private theorem del_mul (a b : PowerSeries ℤ_[p]) :
    PadicMeasure.del p (a * b) = PadicMeasure.del p a * b + a * PadicMeasure.del p b := by
  rw [PadicMeasure.del, PadicMeasure.del, PadicMeasure.del, derivativeFun_mul,
    smul_eq_mul, smul_eq_mul]; ring

/-- `Δ((1+T)^j) = j·(1+T)^j`. -/
private theorem del_one_add_X_pow (j : ℕ) :
    PadicMeasure.del p ((1 + PowerSeries.X) ^ j : PowerSeries ℤ_[p])
      = (j : PowerSeries ℤ_[p]) * (1 + PowerSeries.X) ^ j := by
  have hDoneX : derivativeFun (1 + PowerSeries.X : PowerSeries ℤ_[p]) = 1 := by
    rw [derivativeFun_add, derivativeFun_one, zero_add]; exact derivative_X
  rw [PadicMeasure.del]
  induction j with
  | zero => simp [derivativeFun_one]
  | succ a ih =>
    rw [pow_succ, derivativeFun_mul, hDoneX, smul_eq_mul, smul_eq_mul, mul_one]
    have hpow : (1 + PowerSeries.X) * ((1 + PowerSeries.X) ^ a
        + (1 + PowerSeries.X) * derivativeFun ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ a))
        = (1 + PowerSeries.X) ^ (a + 1) + (1 + PowerSeries.X)
          * ((1 + PowerSeries.X) * derivativeFun ((1 + PowerSeries.X) ^ a)) := by
      rw [pow_succ]; ring
    rw [hpow, mul_left_comm (1 + PowerSeries.X) (1 + PowerSeries.X) (derivativeFun _), ih]
    push_cast; ring

/-- `Δ(φg) = p·φ(Δg)` in the additive `Δ = del` form (the `del`-shaped `del_phiHom`). -/
private theorem del_phiSeries (g : PowerSeries ℤ_[p]) :
    PadicMeasure.del p (phiSeries p g)
      = (p : PowerSeries ℤ_[p]) * phiSeries p (PadicMeasure.del p g) := by
  rw [PadicMeasure.del, PadicMeasure.del, one_add_mul_derivative_phiSeries, smul_eq_C_mul,
    map_natCast]

/-- `Δ` commutes with finite sums. -/
private theorem del_sum {ι : Type*} (s : Finset ι) (g : ι → PowerSeries ℤ_[p]) :
    PadicMeasure.del p (∑ i ∈ s, g i) = ∑ i ∈ s, PadicMeasure.del p (g i) := by
  rw [PadicMeasure.del,
    show (∑ i ∈ s, g i).derivativeFun = ∑ i ∈ s, (g i).derivativeFun from
      map_sum (PowerSeries.derivative ℤ_[p]) g s, Finset.mul_sum]
  rfl

/-- `φ(C a) = C a` over `ℤ_[p]` (φ fixes constants). -/
private theorem phiSeries_C_padicInt (a : ℤ_[p]) :
    phiSeries p (PowerSeries.C a) = PowerSeries.C a := by
  rw [phiSeries]; exact PowerSeries.subst_C a

private theorem phiSeries_add' (a b : PowerSeries ℤ_[p]) :
    phiSeries p (a + b) = phiSeries p a + phiSeries p b := by
  rw [← phiHom_apply, map_add, phiHom_apply, phiHom_apply]

private theorem phiSeries_mul' (a b : PowerSeries ℤ_[p]) :
    phiSeries p (a * b) = phiSeries p a * phiSeries p b := by
  rw [← phiHom_apply, map_mul, phiHom_apply, phiHom_apply]

/-- **Identity K** — the digit-matrix derivative: `(digitMatrix(Δf))_{ij} = (i−j)·M_{ij}
+ p·Δ(M_{ij})` for `M = digitMatrix f`. Differentiate the column-digit identity
`f·(1+T)^j = ∑_i (1+T)^i φ(M_{ij})`; the LHS Leibniz-expands to `Δf·(1+T)^j + j·f(1+T)^j`,
giving digit family `(digitMatrix(Δf))_{ij} + j·M_{ij}`, while the RHS (using `del_phiSeries`)
gives `i·M_{ij} + p·Δ(M_{ij})`; digit uniqueness equates them. -/
private theorem digitMatrix_del (f : PowerSeries ℤ_[p]) (i j : Fin p) :
    (digitMatrix (PadicMeasure.del p f)) i j
      = ((i : ℤ_[p]) - (j : ℤ_[p])) • (digitMatrix f) i j
        + (p : PowerSeries ℤ_[p]) * PadicMeasure.del p ((digitMatrix f) i j) := by
  have hdiff := congrArg (PadicMeasure.del p) (digitMatrix_col_isDigitDecomp f j)
  rw [del_mul, del_one_add_X_pow, del_sum] at hdiff
  have hsummand : ∀ k : Fin p,
      PadicMeasure.del p ((1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p ((digitMatrix f) k j))
        = (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p ((k : ℤ_[p]) • (digitMatrix f) k j
            + (p : PowerSeries ℤ_[p]) * PadicMeasure.del p ((digitMatrix f) k j)) := by
    intro k
    have hpphi : phiSeries p (p : PowerSeries ℤ_[p]) = (p : PowerSeries ℤ_[p]) := by
      rw [← phiHom_apply, map_natCast]
    rw [del_mul, del_one_add_X_pow, del_phiSeries, phiSeries_add', smul_eq_C_mul,
      phiSeries_mul', phiSeries_C_padicInt, phiSeries_mul', hpphi,
      show (PowerSeries.C ((k : ℕ) : ℤ_[p]) : PowerSeries ℤ_[p]) = ((k : ℕ) : PowerSeries ℤ_[p])
        from (map_natCast (PowerSeries.C : ℤ_[p] →+* PowerSeries ℤ_[p]) k)]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hsummand k)] at hdiff
  set Dlf := digitMatrix (PadicMeasure.del p f) with hDlf
  set M := digitMatrix f with hM
  have hLHS2 : f * ((j : PowerSeries ℤ_[p]) * (1 + PowerSeries.X) ^ (j : ℕ))
      = ∑ k : Fin p, (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p ((j : ℤ_[p]) • M k j) := by
    rw [show f * ((j : PowerSeries ℤ_[p]) * (1 + PowerSeries.X) ^ (j : ℕ))
        = (j : PowerSeries ℤ_[p]) * (f * (1 + PowerSeries.X) ^ (j : ℕ)) from by ring,
      digitMatrix_col_isDigitDecomp f j, hM, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_eq_C_mul, phiSeries_mul', phiSeries_C_padicInt,
      show (PowerSeries.C ((j : ℕ) : ℤ_[p]) : PowerSeries ℤ_[p]) = ((j : ℕ) : PowerSeries ℤ_[p])
        from (map_natCast (PowerSeries.C : ℤ_[p] →+* PowerSeries ℤ_[p]) j)]
    ring
  have hLHS1 : PadicMeasure.del p f * (1 + PowerSeries.X) ^ (j : ℕ)
      = ∑ k : Fin p, (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p (Dlf k j) := by
    rw [hDlf, digitMatrix_col_isDigitDecomp (PadicMeasure.del p f) j]
  rw [hLHS1, hLHS2, ← Finset.sum_add_distrib] at hdiff
  rw [show (∑ k : Fin p, ((1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p (Dlf k j)
        + (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p ((j : ℤ_[p]) • M k j)))
      = ∑ k : Fin p, (1 + PowerSeries.X) ^ (k : ℕ)
          * phiSeries p (Dlf k j + (j : ℤ_[p]) • M k j) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [phiSeries_add']; ring] at hdiff
  have hfamL : IsDigitDecomp p
      (∑ k : Fin p, (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p (Dlf k j + (j : ℤ_[p]) • M k j))
      (fun k => Dlf k j + (j : ℤ_[p]) • M k j) := rfl
  have hfamR : IsDigitDecomp p
      (∑ k : Fin p, (1 + PowerSeries.X) ^ (k : ℕ) * phiSeries p (Dlf k j + (j : ℤ_[p]) • M k j))
      (fun k => (k : ℤ_[p]) • M k j + (p : PowerSeries ℤ_[p]) * PadicMeasure.del p (M k j)) := by
    rw [hdiff]; rfl
  have huniq := (existsUnique_digits_padicInt p _).unique hfamL hfamR
  have hthis := congrFun huniq i
  rw [sub_smul]
  have hrw : Dlf i j = (i : ℤ_[p]) • M i j
      + (p : PowerSeries ℤ_[p]) * PadicMeasure.del p (M i j) - (j : ℤ_[p]) • M i j := by
    rw [eq_sub_iff_add_eq]; exact hthis
  rw [hrw]; ring

/-- `Δ` of a row pulls into a row-update: `(1+T)·det(M[row i ↦ ∂ row i]) = det(M[row i ↦ Δ row i])`
(`det_updateRow_smul`, with `Δ = (1+T)·∂`). -/
private theorem del_row_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) (PowerSeries ℤ_[p]))
    (i : Fin n) :
    ((1 + PowerSeries.X) : PowerSeries ℤ_[p])
        * (M.updateRow i (fun j => PowerSeries.derivative ℤ_[p] (M i j))).det
      = (M.updateRow i (fun j => PadicMeasure.del p (M i j))).det := by
  rw [← Matrix.det_updateRow_smul]; rfl

/-- `adjugate M = det M • N` when `N` is the (two-sided) inverse of `M`
(`adjugate_mul : adj M · M = det M • 1`, then cancel `M·N = 1`). -/
private theorem adjugate_eq_det_smul_inv {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) (PowerSeries ℤ_[p])) (hNM : N * M = 1) :
    Matrix.adjugate M = M.det • N := by
  have h : Matrix.adjugate M * (M * N)
      = (M.det • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℤ_[p]))) * N := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul]
  rw [Matrix.smul_mul, Matrix.one_mul, mul_eq_one_comm.mp hNM, Matrix.mul_one] at h
  exact h

/-- **Jacobi → trace form**: `Δ(det M) = det M • trace((M.map Δ)·N)` when `N·M = 1`.
From `derivation_det`, pull `(1+T)` into each row (`del_row_smul`), expand each
`det(updateRow …)` by cofactors (`det_updateRow_eq_sum_adjugate`), and use
`adjugate M = det M • N`. -/
private theorem del_det_eq_smul_trace {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) (PowerSeries ℤ_[p])) (hNM : N * M = 1) :
    PadicMeasure.del p (M.det)
      = M.det • Matrix.trace ((M.map (PadicMeasure.del p)) * N) := by
  rw [PadicMeasure.del,
    show M.det.derivativeFun = (PowerSeries.derivative ℤ_[p]) M.det from rfl,
    derivation_det (PowerSeries.derivative ℤ_[p]) M, Finset.mul_sum,
    Finset.sum_congr rfl (fun i _ => del_row_smul p M i),
    Finset.sum_congr rfl (fun i _ => det_updateRow_eq_sum_adjugate M i
      (fun j => PadicMeasure.del p (M i j))),
    adjugate_eq_det_smul_inv p M N hNM, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- `digitMatrix(f⁻¹)·digitMatrix f = 1` for a unit `f` (digitMatrix is a ring hom). -/
private theorem digitMatrix_inverse_mul' {f : PowerSeries ℤ_[p]} (hf : IsUnit f) :
    digitMatrix (Ring.inverse f) * digitMatrix f = 1 := by
  rw [← digitMatrix_mul, Ring.inverse_mul_cancel _ hf, digitMatrix_one]

/-- `trace(D·N) = 0` for `D_{ij} = (i−j)•(M_{ij}·N_{ji})` when `M·N = N·M = 1`: the two
half-sums `∑ i·(M N)_{ii}` and `∑ k·(N M)_{kk}` are both `∑ i·1`, and cancel. -/
private theorem trace_D_N_zero {n : ℕ} (M N : Matrix (Fin n) (Fin n) (PowerSeries ℤ_[p]))
    (hMN : M * N = 1) (hNM : N * M = 1) :
    ∑ i : Fin n, ∑ k : Fin n,
      ((i : ℤ_[p]) - (k : ℤ_[p])) • (M i k * N k i) = 0 := by
  simp only [sub_smul, Finset.sum_sub_distrib]
  have hA : (∑ i : Fin n, ∑ k : Fin n, (i : ℤ_[p]) • (M i k * N k i))
      = ∑ i : Fin n, (i : ℤ_[p]) • (1 : PowerSeries ℤ_[p]) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.smul_sum]; congr 1
    have hii := congrFun (congrFun hMN i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hii; exact hii
  have hB : (∑ i : Fin n, ∑ k : Fin n, (k : ℤ_[p]) • (M i k * N k i))
      = ∑ k : Fin n, (k : ℤ_[p]) • (1 : PowerSeries ℤ_[p]) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.smul_sum]; congr 1
    have hkk := congrFun (congrFun hNM k) k
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hkk
    rw [← hkk]; exact Finset.sum_congr rfl (fun i _ => by rw [mul_comm])
  rw [hA, hB, sub_self]

/-- `(p : ℤ_p⟦T⟧)` is a regular element: it cancels on the left (it is `C(p)`, `p ≠ 0`). -/
private theorem mul_p_cancel {a b : PowerSeries ℤ_[p]}
    (h : (p : PowerSeries ℤ_[p]) * a = (p : PowerSeries ℤ_[p]) * b) : a = b := by
  have hp0 : (p : PowerSeries ℤ_[p]) ≠ 0 := by
    rw [show (p : PowerSeries ℤ_[p]) = PowerSeries.C (p : ℤ_[p]) from by rw [map_natCast]]
    intro hc
    exact (by exact_mod_cast hp.out.ne_zero : (p : ℤ_[p]) ≠ 0)
      (PowerSeries.C_injective (by rw [hc, map_zero]))
  exact mul_left_cancel₀ hp0 h

/-- **RJW lem:log der 1 (TeX 3292–3306)**: `Δ(𝒲) ⊆ ℤ_p⟦T⟧^{ψ=id}`, where
`𝒲 = (ℤ_p⟦T⟧^×)^{𝒩=id}`.

RJW's proof differentiates the `μ_p`-product `φ(f) = ∏_η f((1+T)η−1)` (replan R10.4: *not*
a formal power-series identity) and deduces `ψ(Δf) = Δf` by `φ`-injectivity. We give the
formal substitute via the **determinant/Jacobi route**. Write `M = digitMatrix f`,
`N = digitMatrix(f⁻¹) = M⁻¹`; the hypothesis `𝒩f = f` reads `f = det M`. Then
`digitMatrix(dlog f) = digitMatrix(Δf)·N`, and by identity K (`digitMatrix_del`),
`digitMatrix(Δf) = D + p·ΔM` with `D_{ij} = (i−j)•M_{ij}` and `ΔM` the entrywise `Δ`. Hence
`trace(digitMatrix(dlog f)) = trace(D·N) + p·trace(ΔM·N)`. The first trace vanishes
(`trace_D_N_zero`, from `MN = NM = 1`), and `Δf = f·trace(ΔM·N)` (Jacobi, `del_det_eq_smul_trace`
with `adjugate M = f•N`) gives `trace(ΔM·N) = f⁻¹·Δf = dlog f`. So
`p·ψ(dlog f) = trace(digitMatrix(dlog f)) = p·dlog f` (`trace_digitMatrix`), and cancelling `p`
(`mul_p_cancel`) yields `ψ(dlog f) = dlog f`. The diagonal `(digitMatrix(Δf))_{ii} = p·Δ(M_{ii})`
of identity K is exactly the formal shadow of RJW's chain-rule step
`Δ(f((1+T)η−1)) = (Δf)((1+T)η−1)`. -/
theorem dlog_mem_psiIdSeries {f : PowerSeries ℤ_[p]} (hf : IsUnit f) (hN : normOp f = f) :
    dlog p f ∈ psiIdSeries p := by
  change psiSeries p (dlog p f) = dlog p f
  set M := digitMatrix f with hM
  set N := digitMatrix (Ring.inverse f) with hN'
  have hNM : N * M = 1 := digitMatrix_inverse_mul' p hf
  have hMN : M * N = 1 := by
    rw [hM, hN', ← digitMatrix_mul, Ring.mul_inverse_cancel _ hf, digitMatrix_one]
  have hfdet : f = M.det := by rw [hM, ← normOp_eq_det, hN]
  have hdlog : dlog p f = PadicMeasure.del p f * Ring.inverse f := by rw [dlog, PadicMeasure.del]
  have hdm : digitMatrix (dlog p f) = digitMatrix (PadicMeasure.del p f) * N := by
    rw [hdlog, digitMatrix_mul, hN']
  have htr := trace_digitMatrix (dlog p f)
  rw [hdm] at htr
  have hKtrace : Matrix.trace (digitMatrix (PadicMeasure.del p f) * N)
      = (∑ i : Fin p, ∑ k : Fin p, ((i : ℤ_[p]) - (k : ℤ_[p])) • (M i k * N k i))
        + (p : PowerSeries ℤ_[p]) * Matrix.trace ((M.map (PadicMeasure.del p)) * N) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by
      rw [digitMatrix_del p f i k, ← hM]))]
    rw [show (∑ i : Fin p, ∑ k : Fin p,
          (((i : ℤ_[p]) - (k : ℤ_[p])) • M i k
            + (p : PowerSeries ℤ_[p]) * PadicMeasure.del p (M i k)) * N k i)
        = (∑ i : Fin p, ∑ k : Fin p, ((i : ℤ_[p]) - (k : ℤ_[p])) • (M i k * N k i))
          + (p : PowerSeries ℤ_[p])
            * ∑ i : Fin p, ∑ k : Fin p, PadicMeasure.del p (M i k) * N k i from by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [add_mul, smul_mul_assoc]; ring]
    rfl
  rw [hKtrace, trace_D_N_zero p M N hMN hNM, zero_add] at htr
  have hdelf : PadicMeasure.del p f
      = f * Matrix.trace ((M.map (PadicMeasure.del p)) * N) := by
    rw [hfdet, del_det_eq_smul_trace p M N hNM, smul_eq_mul, ← hfdet]
  have htrΔ : Matrix.trace ((M.map (PadicMeasure.del p)) * N)
      = Ring.inverse f * PadicMeasure.del p f := by
    rw [hdelf, ← mul_assoc, Ring.inverse_mul_cancel _ hf, one_mul]
  rw [htrΔ, show Ring.inverse f * PadicMeasure.del p f = dlog p f from by rw [hdlog]; ring] at htr
  exact (mul_p_cancel p htr).symm

/-! ### Mod-`p^k` continuity of `𝒩` and limits (for `lem:A mod p`)

The substrate `NormOperator.lean` supplies the iterate congruences `normOp_iterate_modEq`
(part (iv), `𝒩^{k₂}f ≡ 𝒩^{k₁}f mod p^{k₁+1}`) and `normOp_iterate_modEq_self` (part (ii),
`𝒩^n f ≡ f mod p`). Here we add the three further facts the convergence argument needs:
`𝒩` respects `ModEqPow` (so it passes through the limit), `ModEqPow p k · c` is a closed
condition (so limits of `ModEqPow`-congruences stay congruent), and a Hausdorff fact
(`∀ k, ModEqPow p k a b → a = b`). -/

/-- `ModEqPow p k f g` iff `f, g` agree after reduction mod `p^k` (the `C`-factor form
phrased via the quotient `ℤ_[p] ⧸ (p^k)`). -/
theorem modEqPow_iff_map_quot {k : ℕ} {f g : PowerSeries ℤ_[p]} :
    ModEqPow p k f g ↔
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p]) ^ k})) f
        = PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p]) ^ k})) g := by
  rw [ModEqPow, PowerSeries.ext_iff]
  refine forall_congr' (fun m => ?_)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, ← sub_eq_zero, ← map_sub,
    ← RingHom.mem_ker, Ideal.mk_ker, Ideal.mem_span_singleton, map_sub]

/-- `digitMatrix` respects `ModEqPow` entrywise: `a ≡ b mod p^k` gives
`(digitMatrix a)_{ij} ≡ (digitMatrix b)_{ij} mod p^k` (digitMatrix is a ring hom, and
`digitMatrix (C(p^k)·q) = C(p^k) • digitMatrix q`). -/
theorem digitMatrix_entry_modEq {k : ℕ} {a b : PowerSeries ℤ_[p]} (h : ModEqPow p k a b)
    (i j : Fin p) : ModEqPow p k ((digitMatrix a) i j) ((digitMatrix b) i j) := by
  obtain ⟨q, hq⟩ := modEqPow_iff_exists_C_mul.1 h
  have haeq : a = b + PowerSeries.C ((p : ℤ_[p]) ^ k) * q := by rw [← hq]; ring
  have hmat : digitMatrix a
      = digitMatrix b + PowerSeries.C ((p : ℤ_[p]) ^ k) • digitMatrix q := by
    rw [haeq, digitMatrix_add, digitMatrix_mul, digitMatrix_C, smul_mul_assoc, one_mul]
  refine modEqPow_iff_exists_C_mul.2 ⟨(digitMatrix q) i j, ?_⟩
  have := congrFun (congrFun (congrArg
    (fun M => (M : Matrix (Fin p) (Fin p) (PowerSeries ℤ_[p]))) hmat) i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
  rw [this]; ring

/-- **`𝒩` respects `ModEqPow`** (the continuity that drives `lem:A mod p`): `a ≡ b mod p^k`
gives `𝒩 a ≡ 𝒩 b mod p^k`. Via `normOp_eq_det` and `RingHom.map_det`: the determinant of
matrices congruent mod `p^k` entrywise is congruent mod `p^k`. -/
theorem normOp_modEq_of_modEq {k : ℕ} {a b : PowerSeries ℤ_[p]} (h : ModEqPow p k a b) :
    ModEqPow p k (normOp a) (normOp b) := by
  set ρ := (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p]) ^ k})) with hρ
  rw [modEqPow_iff_map_quot]
  have hnorm : ∀ f, PowerSeries.map ρ (normOp f) = Matrix.det
      ((PowerSeries.map ρ).mapMatrix (digitMatrix f)) := fun f => by
    rw [normOp_eq_det, ← RingHom.map_det]
  rw [hnorm, hnorm]
  congr 1
  refine Matrix.ext (fun i j => ?_)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply]
  exact (modEqPow_iff_map_quot (p := p)).1 (digitMatrix_entry_modEq p h i j)

/-- The set `{x : ℤ_[p] | p^k ∣ x}` is closed (it is the closed norm ball `‖·‖ ≤ p^{-k}`). -/
theorem isClosed_dvd_pow (k : ℕ) : IsClosed {x : ℤ_[p] | (p : ℤ_[p]) ^ k ∣ x} := by
  have hset : {x : ℤ_[p] | (p : ℤ_[p]) ^ k ∣ x}
      = (fun x => ‖x‖) ⁻¹' (Set.Iic ((p : ℝ) ^ (-(k : ℤ)))) := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic,
      ← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [hset]
  exact isClosed_Iic.preimage continuous_norm

open scoped PowerSeries.WithPiTopology in
/-- `ModEqPow p k · c` passes through coefficientwise limits: if `gⱼ → g` and eventually
`gⱼ ≡ c mod p^k`, then `g ≡ c mod p^k`. (Each coefficient lands in the closed set
`isClosed_dvd_pow`.) -/
theorem modEqPow_of_tendsto {k : ℕ} {gj : ℕ → PowerSeries ℤ_[p]} {g c : PowerSeries ℤ_[p]}
    (hconv : Filter.Tendsto gj Filter.atTop (nhds g))
    (hmod : ∀ᶠ j in Filter.atTop, ModEqPow p k (gj j) c) :
    ModEqPow p k g c := by
  intro m
  have hcoeffconv : Filter.Tendsto (fun j => PowerSeries.coeff m (gj j - c))
      Filter.atTop (nhds (PowerSeries.coeff m (g - c))) := by
    have h1 := tendsto_coeff hconv m
    have h2 : Filter.Tendsto (fun j => PowerSeries.coeff m (gj j) - PowerSeries.coeff m c)
        Filter.atTop (nhds (PowerSeries.coeff m g - PowerSeries.coeff m c)) :=
      h1.sub tendsto_const_nhds
    simpa only [map_sub] using h2
  refine (isClosed_dvd_pow p k).mem_of_tendsto hcoeffconv ?_
  filter_upwards [hmod] with j hj using hj m

/-- `ℤ_[p]⟦T⟧` is Hausdorff for the `p`-filtration: agreement mod `p^k` for *all* `k`
forces equality (`⋂_k p^k ℤ_[p] = 0`). -/
theorem eq_of_forall_modEqPow {a b : PowerSeries ℤ_[p]} (h : ∀ k, ModEqPow p k a b) :
    a = b := by
  ext m
  rw [← sub_eq_zero, ← map_sub, ← norm_le_zero_iff]
  have hbound : ∀ k : ℕ, ‖PowerSeries.coeff m (a - b)‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := fun k => by
    have := h k m
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow] at this
    rwa [map_sub] at this
  have htend : Filter.Tendsto (fun k : ℕ => (p : ℝ) ^ (-(k : ℤ))) Filter.atTop (nhds 0) := by
    simp only [zpow_neg, zpow_natCast]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hp.out.one_lt))
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds htend (fun k => hbound k)

open scoped PowerSeries.WithPiTopology in
/-- **RJW lem:A mod p (TeX 3337–3343)**: `𝒲 mod p = 𝔽_p⟦T⟧^×` — every unit power
series over `𝔽_p` lifts to a `𝒩`-fixed unit (via `𝒩^k`-convergence, the mod-`p^k`
continuity of `normOp`). Stated as the lift existence. -/
theorem exists_normOp_fixed_lift (f : PowerSeries ℤ_[p]) (hf : IsUnit f) :
    ∃ g : PowerSeries ℤ_[p], IsUnit g ∧ normOp g = g ∧
      PadicLFunctions.Coleman.ModEqPow p 1 g f := by
  -- the sequence `𝒩^[n] f` has a convergent subsequence `𝒩^[φ j] f → g` (compactness)
  obtain ⟨g, φ, hφmono, hconv⟩ := exists_subseq_tendsto (fun n => normOp^[n] f)
  have hφge : ∀ N : ℕ, ∀ᶠ j in Filter.atTop, N ≤ φ j := fun N => by
    filter_upwards [Filter.eventually_ge_atTop N] with j hj using le_trans hj (hφmono.id_le j)
  refine ⟨g, ?_, ?_, ?_⟩
  · -- `g` is a unit: limit of the units `𝒩^[φ j] f`
    refine (isClosed_isUnit (p := p)).mem_of_tendsto hconv ?_
    filter_upwards with j using normOp_iterate_isUnit hf (φ j)
  · -- `𝒩 g = g`: show `𝒩 g ≡ g mod p^{k+1}` for every `k`, then Hausdorff
    refine eq_of_forall_modEqPow p (fun k => ?_)
    have hg_k : ModEqPow p (k + 1) g (normOp^[k] f) := by
      refine modEqPow_of_tendsto p hconv ?_
      filter_upwards [hφge k] with j hj using normOp_iterate_modEq hj hf
    have hNg : ModEqPow p (k + 1) (normOp g) (normOp^[k + 1] f) := by
      have := normOp_modEq_of_modEq p hg_k
      rwa [show normOp (normOp^[k] f) = normOp^[k + 1] f from
        (Function.iterate_succ_apply' normOp k f).symm] at this
    have hstep : ModEqPow p (k + 1) (normOp^[k + 1] f) (normOp^[k] f) :=
      normOp_iterate_modEq (Nat.le_succ k) hf
    exact (hNg.trans (hstep.trans hg_k.symm)).of_le (Nat.le_succ k)
  · -- `g ≡ f mod p`: each `𝒩^[φ j] f ≡ f mod p` (part (ii)), pass to the limit
    refine modEqPow_of_tendsto p hconv ?_
    filter_upwards with j using normOp_iterate_modEq_self f (φ j)

/-! ### `lem:B mod p 2`: the topology-free coefficient construction over `𝔽_p`

The helpers below realise the `𝔽_p⟦T⟧ = Δ(𝔽_p⟦T⟧^×) + (T+1)/T·C` decomposition by a direct
coefficient recursion (no infinite product). See the theorem's docstring for the strategy. -/

/-- Over `𝔽_p`, a series supported only on multiples of `p` is a `p`-th power, hence in
`range φ` (`φ(d) = d^p`, `phiSeries_eq_pow_zmod`; the `p`-th root is the de-`expand`
`d = ∑ c_{pk} T^k`). -/
private theorem mem_range_phiSeries_of_dvd {c : PowerSeries (ZMod p)}
    (hc : ∀ n, ¬ p ∣ n → PowerSeries.coeff n c = 0) :
    c ∈ Set.range (phiSeries p (R := ZMod p)) := by
  haveI : CharP (PowerSeries (ZMod p)) p := charP_of_injective_algebraMap' (ZMod p) p
  refine ⟨PowerSeries.mk (fun k => PowerSeries.coeff (p * k) c), ?_⟩
  have hexp : phiSeries p (PowerSeries.mk (fun k => PowerSeries.coeff (p * k) c))
      = PowerSeries.expand p hp.out.pos.ne' (PowerSeries.mk (fun k => PowerSeries.coeff (p * k) c))
      := by
    have hsub : ((1 + PowerSeries.X) ^ p - 1 : PowerSeries (ZMod p)) = PowerSeries.X ^ p := by
      rw [add_pow_char, one_pow, add_sub_cancel_left]
    rw [phiSeries, hsub, PowerSeries.expand_apply]
  rw [hexp]
  ext m
  rcases em (p ∣ m) with ⟨k, rfl⟩ | hndvd
  · rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_mk]
  · rw [PowerSeries.coeff_expand p hp.out.pos.ne', if_neg hndvd, hc m hndvd]

/-- The joint coefficient recursion for `(a, w)` solving `T·a′ = a·w` over `𝔽_p` against a
target `H`: `(a_0, w_0) = (1, 0)`; for `n ≥ 1`, with `S = ∑_{j=1}^{n−1} a_{n−j}·w_j`, set
`(a_n, w_n) = (0, −S)` if `p ∣ n` and `(n⁻¹(H_n + S), H_n)` otherwise. -/
private def AWfp (H : PowerSeries (ZMod p)) : ℕ → ZMod p × ZMod p
  | n =>
    if n = 0 then (1, 0)
    else
      let S : ZMod p := ∑ k ∈ (Finset.Ico 1 n).attach,
        (AWfp H k.1).1 * (AWfp H (n - k.1)).2
      if p ∣ n then (0, -S)
      else ((n : ZMod p)⁻¹ * (PowerSeries.coeff n H + S), PowerSeries.coeff n H)
  decreasing_by
    · exact (Finset.mem_Ico.1 k.2).2
    · have := (Finset.mem_Ico.1 k.2).1; omega

/-- The `a`-coefficients (`= (AWfp H n).1`). -/
private def AfpCoe (H : PowerSeries (ZMod p)) (n : ℕ) : ZMod p := (AWfp p H n).1
/-- The `w`-coefficients (`= (AWfp H n).2`). -/
private def WfpCoe (H : PowerSeries (ZMod p)) (n : ℕ) : ZMod p := (AWfp p H n).2
/-- The partial sum `S_n = ∑_{j=1}^{n−1} a_{n−j}·w_j` driving the recursion. -/
private def SfpSum (H : PowerSeries (ZMod p)) (n : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Ico 1 n, AfpCoe p H k * WfpCoe p H (n - k)

private theorem Sfp_attach_eq (H : PowerSeries (ZMod p)) (n : ℕ) :
    (∑ k ∈ (Finset.Ico 1 n).attach, (AWfp p H k.1).1 * (AWfp p H (n - k.1)).2)
      = SfpSum p H n := by
  rw [SfpSum, ← Finset.sum_attach (Finset.Ico 1 n)
    (fun k => AfpCoe p H k * WfpCoe p H (n - k))]; rfl

private theorem AWfp_dvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : p ∣ n) :
    AWfp p H n = (0, -SfpSum p H n) := by
  conv_lhs => rw [AWfp]
  rw [if_neg hn]; simp only [Sfp_attach_eq]; rw [if_pos hd]

private theorem AWfp_ndvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : ¬ p ∣ n) :
    AWfp p H n
      = ((n : ZMod p)⁻¹ * (PowerSeries.coeff n H + SfpSum p H n), PowerSeries.coeff n H) := by
  conv_lhs => rw [AWfp]
  rw [if_neg hn]; simp only [Sfp_attach_eq]; rw [if_neg hd]

private theorem AfpCoe_zero (H : PowerSeries (ZMod p)) : AfpCoe p H 0 = 1 := by
  rw [AfpCoe, AWfp, if_pos rfl]
private theorem WfpCoe_zero (H : PowerSeries (ZMod p)) : WfpCoe p H 0 = 0 := by
  rw [WfpCoe, AWfp, if_pos rfl]
private theorem WfpCoe_ndvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : ¬ p ∣ n) :
    WfpCoe p H n = PowerSeries.coeff n H := by rw [WfpCoe, AWfp_ndvd p H hn hd]
private theorem AfpCoe_ndvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : ¬ p ∣ n) :
    AfpCoe p H n = (n : ZMod p)⁻¹ * (PowerSeries.coeff n H + SfpSum p H n) := by
  rw [AfpCoe, AWfp_ndvd p H hn hd]
private theorem WfpCoe_dvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : p ∣ n) :
    WfpCoe p H n = - SfpSum p H n := by rw [WfpCoe, AWfp_dvd p H hn hd]
private theorem AfpCoe_dvd (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) (hd : p ∣ n) :
    AfpCoe p H n = 0 := by rw [AfpCoe, AWfp_dvd p H hn hd]

/-- `[Tⁿ](a·w) = w_n + S_n` for `n ≥ 1` (where `a = mk a_•`, `w = mk w_•`, `a_0 = 1`,
`w_0 = 0`): the convolution splits off its `j = 0` end (`a_n·w_0 = 0`) and `j = n` end
(`a_0·w_n = w_n`), the middle being `S_n`. -/
private theorem coeff_afp_mul_wfp (H : PowerSeries (ZMod p)) {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n (PowerSeries.mk (AfpCoe p H) * PowerSeries.mk (WfpCoe p H))
      = WfpCoe p H n + SfpSum p H n := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  rw [Finset.sum_range_succ, Nat.sub_self, WfpCoe_zero, mul_zero, add_zero]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hn1,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.sub_zero, Finset.sum_range_one, Nat.add_zero, AfpCoe_zero, one_mul]
  rw [SfpSum]

/-- The defining identity `T·a′ = a·w` of the recursion (`a = mk a_•`, `w = mk w_•`):
coefficientwise, `n·a_n = w_n + S_n`, which the recursion makes hold in both the `p∤n`
branch (`n` invertible) and the `p∣n` branch (both sides `0`). -/
private theorem X_deriv_eq_aw (H : PowerSeries (ZMod p)) :
    PowerSeries.X * PowerSeries.derivativeFun (PowerSeries.mk (AfpCoe p H))
      = PowerSeries.mk (AfpCoe p H) * PowerSeries.mk (WfpCoe p H) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, PowerSeries.coeff_mk, PowerSeries.coeff_mk, WfpCoe_zero, mul_zero]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun, PowerSeries.coeff_mk,
      coeff_afp_mul_wfp p H hn]
    by_cases hd : p ∣ (m + 1)
    · rw [AfpCoe_dvd p H hn hd, WfpCoe_dvd p H hn hd, zero_mul, neg_add_cancel]
    · rw [AfpCoe_ndvd p H hn hd, WfpCoe_ndvd p H hn hd]
      have hne : ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact hd
      rw [show ((m : ZMod p) + 1) = ((m + 1 : ℕ) : ZMod p) by push_cast; ring,
        mul_comm, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- **RJW lem:B mod p 2 (TeX 3359–3373) — "the most delicate and technical part"**: the
`𝔽_p⟦T⟧` decomposition `𝔽_p⟦T⟧ = Δ(𝔽_p⟦T⟧^×) + (T+1)/T·C` with
`C = {∑_{n≥1} a_n T^{pn}}`.

Statement note (T1203b, faithful form — statement-fix authorised). The skeleton's
existential was a placeholder (`∃ a c, IsUnit a ∧ c ∈ range φ`, vacuously true). The
faithful claim, with `Δ a = (1+T)·a′·a⁻¹` the `𝔽_p` log-derivative and the `(T+1)/T·c`
factor cleared of its `1/T` pole (`T·b = (T+1)·c`, i.e. `X·b = (1+X)·c`), is: every
`g : 𝔽_p⟦T⟧` is `Δ a + b` for a unit `a` and a `b` with `X·b = (1+X)·c`, `c ∈ φ(𝔽_p⟦T⟧)`
(so `c = ∑ a_n T^{pn} ∈ C`, using `φ(T^m) = T^{pm}` over `𝔽_p`, `phiSeries_eq_pow_zmod`).
This is the precise form `lem:B mod p` consumes: it kills the `b`-part using `ψ b = b`.

Proof note (T1203b, CLOSED). RJW's route (TeX 3366–3373) builds `α_i` so that the unit
`a = ∏(1−α_n T^n)` (a T-adic infinite product, needing `multipliable` + `Δ`-continuity)
has `Δ a = (T+1)/T·h`. We take a topology-free coefficient recursion (the same pattern as
`solCoeff`), building `a` and `w := T·a′·a⁻¹` *directly* by their coefficients rather than
as a product. Write `u = 1+T` (a unit over `𝔽_p`), `H := T·g·u⁻¹`. The map `a ↦ T·a′·a⁻¹`
sends a unit `a` with `a(0)=1` to a series `w` with `w(0)=0` whose `n`-th coefficient
satisfies `n·a_n = w_n + ∑_{j=1}^{n−1} a_{n−j}·w_j` (clear `T·a′ = a·w`). For `(n,p)=1`
the leading `n·a_n` is invertible so `a_n` is determined by a chosen `w_n`; for `p∣n` the
LHS vanishes (`n=0` in `𝔽_p`), forcing `w_n` and freeing `a_n`. So we jointly recurse
(`AWfp`): set `w_n := H_n`, `a_n := n⁻¹(H_n + S_n)` when `(n,p)=1`; `a_n := 0`,
`w_n := −S_n` when `p∣n` (`S_n` the partial sum). Then `T·a′ = a·w` (`X_deriv_eq_aw`),
`a` is a unit (`a(0)=1`), `w = T·a′·a⁻¹`, and `w` agrees with `H` off multiples of `p`, so
`c := H − w` is supported on `pℕ`, hence a `p`-th power `= φ(d)` (over `𝔽_p`,
`range φ = {p-th powers}`; `mem_range_phiSeries_of_dvd`). Finally `b := g − Δa` gives
`X·b = u·c` by `X·Δa = u·w` and `u·H = T·g`, and `g = Δa + b` trivially. No infinite
product, no `Δ`-continuity. -/
theorem fp_series_eq_dlog_add_frobC (g : PowerSeries (ZMod p)) :
    ∃ (a : PowerSeries (ZMod p)) (b : PowerSeries (ZMod p)) (c : PowerSeries (ZMod p)),
      IsUnit a ∧ c ∈ Set.range (phiSeries p (R := ZMod p)) ∧
        PowerSeries.X * b = (1 + PowerSeries.X) * c ∧
        g = (1 + PowerSeries.X) * PowerSeries.derivativeFun a * Ring.inverse a + b := by
  -- `u = 1+T` (a unit), `H = T·g·u⁻¹`, and the recursion's `a = mk a_•`, `w = mk w_•`
  have hu : IsUnit (1 + PowerSeries.X : PowerSeries (ZMod p)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  set H : PowerSeries (ZMod p) :=
    PowerSeries.X * g * Ring.inverse (1 + PowerSeries.X) with hHdef
  set a : PowerSeries (ZMod p) := PowerSeries.mk (AfpCoe p H) with hadef
  set w : PowerSeries (ZMod p) := PowerSeries.mk (WfpCoe p H) with hwdef
  -- `a` is a unit (`a(0) = 1`)
  have ha : IsUnit a := by
    rw [hadef, PowerSeries.isUnit_iff_constantCoeff,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, AfpCoe_zero]
    exact isUnit_one
  have haa : a * Ring.inverse a = 1 := Ring.mul_inverse_cancel _ ha
  have huu : (1 + PowerSeries.X : PowerSeries (ZMod p)) * Ring.inverse (1 + PowerSeries.X) = 1 :=
    Ring.mul_inverse_cancel _ hu
  -- `w = T·a′·a⁻¹` from the recursion's defining identity `T·a′ = a·w`
  have hkey : PowerSeries.X * PowerSeries.derivativeFun a = a * w := X_deriv_eq_aw p H
  have hw : w = PowerSeries.X * PowerSeries.derivativeFun a * Ring.inverse a := by
    have h2 := congrArg (· * Ring.inverse a) hkey
    rw [mul_assoc a w (Ring.inverse a), mul_comm w (Ring.inverse a), ← mul_assoc,
      mul_comm a (Ring.inverse a), Ring.inverse_mul_cancel _ ha, one_mul] at h2
    rw [← h2]
  refine ⟨a, g - (1 + PowerSeries.X) * PowerSeries.derivativeFun a * Ring.inverse a, H - w,
    ha, ?_, ?_, by ring⟩
  · -- `c = H − w ∈ range φ`: supported on multiples of `p` (agrees with `H` off `pℕ`)
    refine mem_range_phiSeries_of_dvd p (fun n hd => ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · rw [map_sub, hHdef, mul_assoc, PowerSeries.coeff_zero_X_mul, hwdef,
        PowerSeries.coeff_mk, WfpCoe_zero, sub_zero]
    · rw [map_sub, hwdef, PowerSeries.coeff_mk, WfpCoe_ndvd p H hn hd, sub_self]
  · -- `X·b = u·c`: `X·Δa = u·w` and `u·H = T·g`
    rw [hw]
    have hcancel : (1 + PowerSeries.X : PowerSeries (ZMod p)) * H = PowerSeries.X * g := by
      rw [hHdef, show (1 + PowerSeries.X : PowerSeries (ZMod p))
          * (PowerSeries.X * g * Ring.inverse (1 + PowerSeries.X))
        = PowerSeries.X * g * ((1 + PowerSeries.X) * Ring.inverse (1 + PowerSeries.X)) by ring,
        huu, mul_one]
    rw [mul_sub, mul_sub, hcancel]; ring

/-! ### `Δ = dlog` turns products into sums (for `lem:log der red mod p`)

The successive-approximation argument forms `h_n = ∏_k g_k^{±p^{k-1}}`; `Δ` of such a
product telescopes via these `dlog`-homomorphism facts. -/

/-- `Δ(gh) = Δg + Δh` for units `g, h` (the log-derivative is additive on the unit group:
`(gh)' = g'h + gh'`, divide by `gh`). -/
theorem dlog_mul {g h : PowerSeries ℤ_[p]} (hg : IsUnit g) (hh : IsUnit h) :
    dlog p (g * h) = dlog p g + dlog p h := by
  have hg' : g * Ring.inverse g = 1 := Ring.mul_inverse_cancel _ hg
  have hh' : h * Ring.inverse h = 1 := Ring.mul_inverse_cancel _ hh
  rw [dlog, dlog, dlog, derivativeFun_mul, smul_eq_mul, smul_eq_mul, Ring.mul_inverse_rev]
  rw [show (1 + PowerSeries.X) * (g * h.derivativeFun + h * g.derivativeFun)
        * (Ring.inverse h * Ring.inverse g)
      = (1 + PowerSeries.X) * g.derivativeFun * Ring.inverse g * (h * Ring.inverse h)
        + (1 + PowerSeries.X) * h.derivativeFun * Ring.inverse h * (g * Ring.inverse g) from by
        ring,
    hg', hh', mul_one, mul_one, add_comm]

/-- `Δ 1 = 0`. -/
theorem dlog_one : dlog p (1 : PowerSeries ℤ_[p]) = 0 := by
  rw [dlog, derivativeFun_one, mul_zero, zero_mul]

/-- `Δ(g⁻¹) = −Δg` for a unit `g`. -/
theorem dlog_inverse {g : PowerSeries ℤ_[p]} (hg : IsUnit g) :
    dlog p (Ring.inverse g) = - dlog p g := by
  have h := dlog_mul p hg (isUnit_ringInverse.mpr hg)
  rw [Ring.mul_inverse_cancel _ hg, dlog_one] at h
  linear_combination -h

/-- `Δ(gⁿ) = n·Δg` for a unit `g`. -/
theorem dlog_pow {g : PowerSeries ℤ_[p]} (hg : IsUnit g) (n : ℕ) :
    dlog p (g ^ n) = (n : ℤ) • dlog p g := by
  induction n with
  | zero => simp [dlog_one]
  | succ m ih => rw [pow_succ, dlog_mul p (hg.pow m) hg, ih]; push_cast; ring

/-! ### Honest `ψ` over `𝔽_p⟦T⟧` (for `lem:B mod p`)

The trace operator `ψ` is junk-totalised off `integerRing K`/`ℤ_[p]` (FormalPsi.lean): it is
honest exactly where the digit decomposition `F = Σ_{i<p} (1+T)^i·φ(G_i)` is unique. The
`lem:B mod p` argument needs `ψ` honest over `𝔽_p⟦T⟧`, so we establish the missing
uniqueness over `ZMod p` directly (existence transports by lifting to `ℤ_[p]`).

Over `ZMod p`, `φ(G) = G^p` (`phiSeries_eq_pow_zmod`) and `(1+T)^p − 1 = T^p`, so a digit
decomposition reads `F = Σ_i (1+T)^i G_i^p`. Uniqueness is the freeness of `𝔽_p⟦T⟧` over
its Frobenius image with basis `(1+T)^i`: the operator `θ = (1+T)∂` acts as the scalar `i`
on `(1+T)^i·ker(∂)` (and `ker(∂) ⊇ range(φ)` over char `p`), so the `p` distinct eigenvalues
`0, …, p−1` separate the summands (Lagrange interpolation `y^{p−1} = [y ≠ 0]`). -/

/-- `∂((1+T)^i) = i·(1+T)^{i−1}` over `ZMod p`. -/
private theorem derivativeFun_one_add_X_pow_zmod (i : ℕ) :
    derivativeFun ((1 + PowerSeries.X : PowerSeries (ZMod p)) ^ i)
      = (i : PowerSeries (ZMod p)) * (1 + PowerSeries.X) ^ (i - 1) := by
  have h1 : derivativeFun (1 + PowerSeries.X : PowerSeries (ZMod p)) = 1 := by
    rw [derivativeFun_add, derivativeFun_one, zero_add]; exact derivative_X
  rw [show derivativeFun ((1 + PowerSeries.X : PowerSeries (ZMod p)) ^ i)
      = d⁄dX (ZMod p) ((1 + PowerSeries.X) ^ i) from rfl, derivative_pow,
    show d⁄dX (ZMod p) (1 + PowerSeries.X : PowerSeries (ZMod p))
      = derivativeFun (1 + PowerSeries.X) from rfl, h1, mul_one]

/-- A `p`-th power has zero derivative over `ZMod p` (`∂(g^p) = p·g^{p−1}·g′ = 0`). -/
private theorem derivativeFun_pow_p_zmod (g : PowerSeries (ZMod p)) :
    derivativeFun (g ^ p) = 0 := by
  rw [show derivativeFun (g ^ p) = d⁄dX (ZMod p) (g ^ p) from rfl, derivative_pow,
    show ((p : ℕ) : PowerSeries (ZMod p)) = PowerSeries.C (R := ZMod p) (p : ZMod p) from by
      rw [map_natCast], show (p : ZMod p) = 0 from by exact_mod_cast (ZMod.natCast_self p),
    map_zero, zero_mul, zero_mul]

/-- The `θ = (1+T)∂` eigen-identity: `θ(C c·(1+T)^i·E) = C(i·c)·(1+T)^i·E` whenever
`∂ E = 0` (so `E` is in the `θ`-eigenspace for eigenvalue `i`). -/
private theorem theta_smul_eigen {E : PowerSeries (ZMod p)} (hE : derivativeFun E = 0)
    (i : ℕ) (c : ZMod p) :
    (1 + PowerSeries.X) * derivativeFun
        (PowerSeries.C c * ((1 + PowerSeries.X) ^ i * E))
      = PowerSeries.C ((i : ZMod p) * c) * ((1 + PowerSeries.X) ^ i * E) := by
  have hd : derivativeFun (PowerSeries.C c * ((1 + PowerSeries.X) ^ i * E))
      = PowerSeries.C c * ((i : PowerSeries (ZMod p)) * (1 + PowerSeries.X) ^ (i - 1) * E) := by
    rw [show PowerSeries.C c * ((1 + PowerSeries.X) ^ i * E)
        = (PowerSeries.C c * (1 + PowerSeries.X) ^ i) * E from by ring, derivativeFun_mul,
      derivativeFun_mul, derivativeFun_C, hE, smul_zero, smul_zero, zero_add, add_zero,
      smul_eq_mul, derivativeFun_one_add_X_pow_zmod]
    ring
  rw [hd, map_mul, show ((i : ℕ) : PowerSeries (ZMod p)) = PowerSeries.C ((i : ℕ) : ZMod p) from
    (map_natCast _ _).symm]
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi; simp
  · have hpow : (1 + PowerSeries.X : PowerSeries (ZMod p)) ^ i
        = (1 + PowerSeries.X) * (1 + PowerSeries.X) ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow]; ring

/-- The power-sum identity driving uniqueness: if `Σ_i (1+T)^i E_i = 0` with each `∂ E_i = 0`,
then `Σ_i C(iᵏ)·(1+T)^i E_i = 0` for every `k` (apply `θ` `k` times). -/
private theorem sum_pow_smul_eq_zero {E : Fin p → PowerSeries (ZMod p)}
    (hE : ∀ i, derivativeFun (E i) = 0)
    (hsum : ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * E i = 0) (k : ℕ) :
    ∑ i : Fin p, PowerSeries.C ((i : ZMod p) ^ k) * ((1 + PowerSeries.X) ^ (i : ℕ) * E i)
      = 0 := by
  induction k with
  | zero => simpa using hsum
  | succ m ih =>
    have hstep : (1 + PowerSeries.X) * derivativeFun
        (∑ i : Fin p, PowerSeries.C ((i : ZMod p) ^ m) * ((1 + PowerSeries.X) ^ (i : ℕ) * E i))
        = 0 := by
      rw [ih, show derivativeFun (0 : PowerSeries (ZMod p)) = 0 from
        map_zero (derivative (ZMod p)), mul_zero]
    rw [show derivativeFun
          (∑ i : Fin p, PowerSeries.C ((i : ZMod p) ^ m) * ((1 + PowerSeries.X) ^ (i : ℕ) * E i))
        = ∑ i : Fin p, derivativeFun
          (PowerSeries.C ((i : ZMod p) ^ m) * ((1 + PowerSeries.X) ^ (i : ℕ) * E i)) from
        map_sum (derivative (ZMod p)) _ _, Finset.mul_sum] at hstep
    rw [← hstep]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [theta_smul_eigen p (hE i) (i : ℕ) ((i : ZMod p) ^ m), pow_succ,
      mul_comm ((i : ZMod p) ^ m) (i : ZMod p), map_mul]

/-- Polynomial-evaluation form of the power-sum identity: `Σ_i C(P(i))·(1+T)^i E_i = 0` for
any `P : 𝔽_p[X]` (linear-combine the `k`-th power sums). -/
private theorem sum_polyEval_smul_eq_zero {E : Fin p → PowerSeries (ZMod p)}
    (hE : ∀ i, derivativeFun (E i) = 0)
    (hsum : ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * E i = 0) (P : Polynomial (ZMod p)) :
    ∑ i : Fin p, PowerSeries.C (P.eval (i : ZMod p)) * ((1 + PowerSeries.X) ^ (i : ℕ) * E i)
      = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [Polynomial.eval_add, map_add, add_mul]
    rw [Finset.sum_add_distrib, hP, hQ, add_zero]
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    rw [show (∑ i : Fin p, PowerSeries.C (c * (i : ZMod p) ^ n)
          * ((1 + PowerSeries.X) ^ (i : ℕ) * E i))
        = PowerSeries.C c * ∑ i : Fin p, PowerSeries.C ((i : ZMod p) ^ n)
          * ((1 + PowerSeries.X) ^ (i : ℕ) * E i) from by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul]; ring]
    rw [sum_pow_smul_eq_zero p hE hsum n, mul_zero]

/-- The Lagrange `δ`-indicator over `𝔽_p`: `1 − (i − j)^{p−1} = [i = j]` (Fermat
`y^{p−1} = [y ≠ 0]`), for `i, j : Fin p`. -/
private theorem lagrange_delta_eval (i j : Fin p) :
    (1 - (Polynomial.X - Polynomial.C ((j : ℕ) : ZMod p)) ^ (p - 1)).eval (((i : ℕ)) : ZMod p)
      = if i = j then 1 else 0 := by
  rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  rcases eq_or_ne i j with h | h
  · subst h; simp [ZMod.pow_card_sub_one]
  · have hij : ((i : ℕ) : ZMod p) ≠ ((j : ℕ) : ZMod p) := by
      intro hc
      rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, Nat.mod_eq_of_lt i.2,
        Nat.mod_eq_of_lt j.2] at hc
      exact h (Fin.ext hc)
    rw [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr hij), sub_self, if_neg h]

/-- **Digit-decomposition uniqueness over `𝔽_p⟦T⟧`**: `Σ_i (1+T)^i φ(G_i) = Σ_i (1+T)^i φ(H_i)`
forces `G_i = H_i`. (The `θ`-eigenvalue/Lagrange argument: the differences `E_i = φ(G_i−H_i)`
lie in `ker ∂` and are separated by the `p` distinct eigenvalues of `θ = (1+T)∂`.) -/
private theorem digits_unique_zmod {G H : Fin p → PowerSeries (ZMod p)}
    (heq : ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (G i)
      = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (H i)) :
    G = H := by
  set E : Fin p → PowerSeries (ZMod p) := fun i => phiSeries p (G i) - phiSeries p (H i) with hE
  have hEval : ∀ i, E i = phiSeries p (G i) - phiSeries p (H i) := fun i => rfl
  have hEzero : ∀ i, derivativeFun (E i) = 0 := fun i => by
    rw [hEval, phiSeries_eq_pow_zmod, phiSeries_eq_pow_zmod,
      show derivativeFun ((G i) ^ p - (H i) ^ p)
        = derivativeFun ((G i) ^ p) - derivativeFun ((H i) ^ p) from
        map_sub (derivative (ZMod p)) _ _, derivativeFun_pow_p_zmod, derivativeFun_pow_p_zmod,
      sub_zero]
  have hsum : ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * E i = 0 := by
    simp only [hEval, mul_sub]
    rw [Finset.sum_sub_distrib, heq, sub_self]
  funext j
  -- the Lagrange combination isolates the `j`-th summand
  have hisolate := sum_polyEval_smul_eq_zero p hEzero hsum
    (1 - (Polynomial.X - Polynomial.C ((j : ℕ) : ZMod p)) ^ (p - 1))
  rw [Finset.sum_eq_single j (fun i _ hij => by
      rw [lagrange_delta_eval p i j, if_neg hij, map_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ j) h), lagrange_delta_eval p j j, if_pos rfl, map_one,
    one_mul] at hisolate
  -- `(1+T)^j E_j = 0` and `1+T` a unit give `E_j = 0`, i.e. `φ(G_j) = φ(H_j)`
  have hunit : IsUnit ((1 + PowerSeries.X : PowerSeries (ZMod p)) ^ (j : ℕ)) := by
    refine IsUnit.pow _ ?_; rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  have hEj : E j = 0 := hunit.mul_right_eq_zero.mp hisolate
  have hphi : phiSeries p (G j) = phiSeries p (H j) := sub_eq_zero.1 (hEval j ▸ hEj)
  -- `φ` is injective over `ZMod p` (it is the Frobenius `g ↦ g^p`)
  haveI : CharP (PowerSeries (ZMod p)) p := charP_of_injective_algebraMap' (ZMod p) p
  rw [phiSeries_eq_pow_zmod, phiSeries_eq_pow_zmod] at hphi
  exact frobenius_inj (PowerSeries (ZMod p)) p (by rw [frobenius_def, frobenius_def]; exact hphi)

/-- **Existence-uniqueness of digits over `𝔽_p⟦T⟧`**: every `F̄ ∈ 𝔽_p⟦T⟧` has a unique digit
family. Existence by lifting to `ℤ_[p]` (`existsUnique_digits_padicInt` + `isDigitDecomp_map`),
uniqueness `digits_unique_zmod`. This makes `psiSeries` honest over `ZMod p`. -/
private theorem existsUnique_digits_zmod (F : PowerSeries (ZMod p)) :
    ∃! G : Fin p → PowerSeries (ZMod p), IsDigitDecomp p F G := by
  obtain ⟨Flift, hFlift⟩ :=
    PowerSeries.map_surjective _ (ZMod.ringHom_surjective PadicInt.toZMod) F
  obtain ⟨G, hG, -⟩ := existsUnique_digits_padicInt p Flift
  refine ⟨fun i => PowerSeries.map PadicInt.toZMod (G i), ?_, ?_⟩
  · have := isDigitDecomp_map p (PadicInt.toZMod : ℤ_[p] →+* ZMod p) hG
    rwa [hFlift] at this
  · intro H hH
    exact digits_unique_zmod p (by
      rw [← hH]
      have := isDigitDecomp_map p (PadicInt.toZMod : ℤ_[p] →+* ZMod p) hG
      rw [hFlift] at this; exact this)

/-- Over `ZMod p`, `psiSeries` is the `0`-th digit of any digit decomposition. -/
private theorem psiSeries_eq_of_isDigitDecomp_zmod {F : PowerSeries (ZMod p)}
    {G : Fin p → PowerSeries (ZMod p)} (hG : IsDigitDecomp p F G) :
    psiSeries p F = G 0 :=
  psiSeries_eq_of_unique p (existsUnique_digits_zmod p F) hG

/-- `φ` fixes constants over `ZMod p`. -/
private theorem phiSeries_C_zmod (a : ZMod p) :
    phiSeries p (PowerSeries.C a : PowerSeries (ZMod p)) = PowerSeries.C a := by
  rw [phiSeries]; exact subst_C a

/-- `ψ ∘ φ = id` over `ZMod p`. -/
private theorem psiSeries_phi_zmod (G : PowerSeries (ZMod p)) :
    psiSeries p (phiSeries p G) = G := by
  refine psiSeries_eq_of_isDigitDecomp_zmod p
    (G := fun i => if i = 0 then G else (0 : PowerSeries (ZMod p))) ?_
  change phiSeries p G = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (if i = 0 then G else 0)
  rw [Finset.sum_eq_single (0 : Fin p)]
  · simp
  · intro i _ hi0; rw [if_neg hi0, phiSeries_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin p)) h

/-- **The series projection formula over `ZMod p`** (`ψ(φd·F) = d·ψF`, the ξ-free substitute
for RJW's `Eqphipsi`-based "ψ fixes `(T+1)/T`"; mirror of `psi_phi_mul`/the `ℤ_[p]` form). -/
private theorem psiSeries_phiSeries_mul_zmod (d F : PowerSeries (ZMod p)) :
    psiSeries p (phiSeries p d * F) = d * psiSeries p F := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits_zmod p F
  rw [psiSeries_eq_of_isDigitDecomp_zmod p hGF]
  refine psiSeries_eq_of_isDigitDecomp_zmod p (G := fun i => d * GF i) ?_
  change phiSeries p d * F = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
      * phiSeries p (d * GF i)
  rw [hGF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phiSeries, phiSeries, phiSeries,
    PowerSeries.subst_mul (hasSubst_one_add_X_pow_sub_one p)]
  ring

/-- `ψ` commutes with reduction `map_toZMod` (digit families reduce; `ψ` is the `0`-th). -/
private theorem map_toZMod_psiSeries (F : PowerSeries ℤ_[p]) :
    PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (psiSeries p F)
      = psiSeries p (PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) F) := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits_padicInt p F
  rw [psiSeries_eq_of_isDigitDecomp_padicInt hGF,
    psiSeries_eq_of_isDigitDecomp_zmod p (isDigitDecomp_map p _ hGF)]

/-- `ψ(Tʲ) = (−1)ʲ` (constant) for `j < p`: from the digit family of `Tʲ` whose `0`-th
digit is the constant `binom(j,0)(−1)ʲ = (−1)ʲ` (binomial expansion `Tʲ = ((1+T)−1)ʲ`). -/
private theorem psiSeries_X_pow_lt {j : ℕ} (hj : j < p) :
    psiSeries p ((PowerSeries.X : PowerSeries (ZMod p)) ^ j) = PowerSeries.C ((-1) ^ j) := by
  have hdecomp : IsDigitDecomp p ((PowerSeries.X : PowerSeries (ZMod p)) ^ j)
      (fun l => PowerSeries.C ((Nat.choose j (l : ℕ) : ZMod p) * (-1) ^ (j - (l : ℕ)))) := by
    rw [IsDigitDecomp, Finset.sum_congr rfl (fun l _ => by rw [phiSeries_C_zmod p])]
    conv_lhs => rw [show (PowerSeries.X : PowerSeries (ZMod p)) = (1 + PowerSeries.X) - 1 from by
      ring, sub_eq_add_neg, add_pow]
    rw [Fin.sum_univ_eq_sum_range (fun l => (1 + PowerSeries.X : PowerSeries (ZMod p)) ^ l
        * PowerSeries.C ((Nat.choose j l : ZMod p) * (-1) ^ (j - l))) p,
      ← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hj : j + 1 ≤ p),
      show (∑ l ∈ Finset.Ico (j + 1) p, (1 + PowerSeries.X : PowerSeries (ZMod p)) ^ l
          * PowerSeries.C ((Nat.choose j l : ZMod p) * (-1) ^ (j - l))) = 0 from by
        refine Finset.sum_eq_zero fun l hl => ?_
        rw [Nat.choose_eq_zero_of_lt (by simp only [Finset.mem_Ico] at hl; omega)]
        simp, add_zero]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [map_mul, map_pow, map_neg, map_one, map_natCast]; ring
  rw [psiSeries_eq_of_isDigitDecomp_zmod p hdecomp]
  simp

/-- `ψ` is additive over `ZMod p`. -/
private theorem psiSeries_add_zmod (F G : PowerSeries (ZMod p)) :
    psiSeries p (F + G) = psiSeries p F + psiSeries p G := by
  obtain ⟨GF, hGF, -⟩ := existsUnique_digits_zmod p F
  obtain ⟨GG, hGG, -⟩ := existsUnique_digits_zmod p G
  rw [psiSeries_eq_of_isDigitDecomp_zmod p hGF, psiSeries_eq_of_isDigitDecomp_zmod p hGG]
  refine psiSeries_eq_of_isDigitDecomp_zmod p (G := fun i => GF i + GG i) ?_
  change F + G = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (GF i + GG i)
  rw [hGF, hGG, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [phiSeries, phiSeries, phiSeries,
    PowerSeries.subst_add (hasSubst_one_add_X_pow_sub_one p), mul_add]

/-- `X^p = X·X^{p−1}` over `ZMod p`. -/
private theorem X_pow_eq_X_mul (p : ℕ) [Fact p.Prime] :
    (PowerSeries.X : PowerSeries (ZMod p)) ^ p = PowerSeries.X * PowerSeries.X ^ (p - 1) := by
  rw [← pow_succ', Nat.sub_add_cancel (Fact.out (p := p.Prime)).one_le]

/-- `ψ((1+T)·T^{p−1}) = 1 + T` over `ZMod p` (`= ψ(T^{p−1}) + ψ(φ(T))`, with
`ψ(T^{p−1}) = C((−1)^{p−1}) = 1` by Fermat and `ψ(φ(T)) = T`). -/
private theorem psiSeries_one_add_X_mul_X_pow :
    psiSeries p ((1 + PowerSeries.X) * PowerSeries.X ^ (p - 1))
      = (1 + PowerSeries.X : PowerSeries (ZMod p)) := by
  have hphiX : phiSeries p (PowerSeries.X : PowerSeries (ZMod p)) = PowerSeries.X ^ p :=
    phiSeries_eq_pow_zmod PowerSeries.X
  have hexpand : (1 + PowerSeries.X : PowerSeries (ZMod p)) * PowerSeries.X ^ (p - 1)
      = PowerSeries.X ^ (p - 1) + phiSeries p PowerSeries.X := by
    rw [hphiX, add_mul, one_mul, X_pow_eq_X_mul p]
  rw [hexpand, psiSeries_add_zmod, psiSeries_X_pow_lt p (by have := hp.out.two_le; omega),
    psiSeries_phi_zmod,
    show ((-1) ^ (p - 1) : ZMod p) = 1 from ZMod.pow_card_sub_one_eq_one (by
      intro hc; rw [neg_eq_zero] at hc; exact one_ne_zero hc), map_one]

/-- The order argument: `e = T^{p−1}·e^p` over `𝔽_p⟦T⟧` forces `e = 0` (else
`ord e = (p−1) + p·ord e`, impossible for `p ≥ 2`). -/
private theorem eq_zero_of_eq_X_pow_mul_pow {e : PowerSeries (ZMod p)}
    (h : e = PowerSeries.X ^ (p - 1) * e ^ p) : e = 0 := by
  by_contra hne
  have hord : e.order = (PowerSeries.X ^ (p - 1) * e ^ p : PowerSeries (ZMod p)).order :=
    congrArg PowerSeries.order h
  rw [PowerSeries.order_mul, PowerSeries.order_X_pow, PowerSeries.order_pow e p] at hord
  rw [← PowerSeries.order_eq_top] at hne
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hm, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_inj] at hord
  have hp2 : 2 ≤ p := hp.out.two_le
  have hmm : m ≤ p * m := Nat.le_mul_of_pos_left m (by omega)
  omega

/-- **`lem:B mod p`'s ψ-killing step (TeX 3352–3356)**: the `(T+1)/T·C` component is killed
by `ψ = id`. Formally: if `ψ b = b`, `X·b = (1+X)·c` and `c ∈ range φ` over `𝔽_p⟦T⟧`, then
`b = 0`. (Write `c = φ(X·e) = T^p·φ(e)`, so `b = (1+T)·T^{p−1}·φ(e)`; the projection formula
gives `ψ b = e·ψ((1+T)T^{p−1}) = e·(1+T)`, and `ψ b = b` reduces to `e = T^{p−1}·e^p`, which
forces `e = 0` by the order argument — RJW's `d_n = d_{np}` invariant collapse.) -/
private theorem psiId_one_add_X_div_X_phi_eq_zero {b c : PowerSeries (ZMod p)}
    (hpsi : psiSeries p b = b) (hXb : PowerSeries.X * b = (1 + PowerSeries.X) * c)
    (hc : c ∈ Set.range (phiSeries p (R := ZMod p))) : b = 0 := by
  obtain ⟨d, hd⟩ := hc
  -- `c(0) = 0` (from `X·b`), so `d(0) = 0`, so `X | d`
  have hc0 : PowerSeries.constantCoeff (R := ZMod p) c = 0 := by
    have h1 : PowerSeries.constantCoeff (R := ZMod p) (PowerSeries.X * b) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_X_mul]
    rwa [hXb, map_mul, map_add, map_one, PowerSeries.constantCoeff_X, add_zero, one_mul] at h1
  have hd0 : PowerSeries.constantCoeff (R := ZMod p) d = 0 := by
    rw [← hd, constantCoeff_phiSeries] at hc0; exact hc0
  obtain ⟨e, he⟩ := (PowerSeries.X_dvd_iff (φ := d)).2 hd0
  -- `c = X^p·φ(e)`, hence `b = (1+X)·X^{p−1}·φ(e)`
  have hphiX : phiSeries p (PowerSeries.X : PowerSeries (ZMod p)) = PowerSeries.X ^ p :=
    phiSeries_eq_pow_zmod PowerSeries.X
  have hcform : c = PowerSeries.X ^ p * phiSeries p e := by
    rw [← hd, he, show phiSeries p (PowerSeries.X * e)
        = phiSeries p PowerSeries.X * phiSeries p e from by
      rw [phiSeries, phiSeries, phiSeries,
        PowerSeries.subst_mul (hasSubst_one_add_X_pow_sub_one p)], hphiX]
  have hbform : b = (1 + PowerSeries.X) * PowerSeries.X ^ (p - 1) * phiSeries p e := by
    have hXb' : PowerSeries.X * b
        = PowerSeries.X * ((1 + PowerSeries.X) * PowerSeries.X ^ (p - 1) * phiSeries p e) := by
      rw [hXb, hcform, X_pow_eq_X_mul p]; ring
    ext n
    have := congrArg (PowerSeries.coeff (n + 1)) hXb'
    rwa [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul] at this
  -- `ψ b = e·ψ((1+X)X^{p−1}) = e·(1+X)`, while `ψ b = b = (1+X)X^{p−1}φ(e)`
  have hpsib : psiSeries p b = e * (1 + PowerSeries.X) := by
    rw [hbform, show (1 + PowerSeries.X) * PowerSeries.X ^ (p - 1) * phiSeries p e
        = phiSeries p e * ((1 + PowerSeries.X) * PowerSeries.X ^ (p - 1)) from by ring,
      psiSeries_phiSeries_mul_zmod, psiSeries_one_add_X_mul_X_pow]
  rw [hpsi] at hpsib
  -- cancel the unit `(1+X)`: `e = X^{p−1}·φ(e) = X^{p−1}·e^p`
  have hunit : IsUnit (1 + PowerSeries.X : PowerSeries (ZMod p)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  -- `e·(1+X) = (1+X)·X^{p−1}·φ(e)`, cancel `(1+X)` (a unit)
  have heq2 : e * (1 + PowerSeries.X)
      = (1 + PowerSeries.X) * (PowerSeries.X ^ (p - 1) * phiSeries p e) := by
    rw [← hpsib, hbform]; ring
  have hecancel : e = PowerSeries.X ^ (p - 1) * phiSeries p e :=
    hunit.mul_right_inj.mp (by rw [mul_comm (1 + PowerSeries.X) e]; exact heq2)
  have he0 : e = 0 :=
    eq_zero_of_eq_X_pow_mul_pow p (hecancel.trans (by rw [phiSeries_eq_pow_zmod]))
  -- `e = 0 ⟹ d = 0 ⟹ c = 0 ⟹ b = 0`
  rw [hbform, he0, phiSeries_zero, mul_zero]

/-! ### `B ⊆ A` modulo `p` (`lem:B mod p`, the surjectivity-mod-`p` input) -/

/-- `Δ = dlog` commutes with reduction `map_toZMod` on units (the `𝔽_p` log-derivative is the
reduction of the `ℤ_[p]` one): `derivativeFun` and `Ring.inverse` (on units) reduce. -/
private theorem map_toZMod_dlog {g : PowerSeries ℤ_[p]} (hg : IsUnit g) :
    PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (dlog p g)
      = (1 + PowerSeries.X) * derivativeFun
          (PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) g)
        * Ring.inverse (PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) g) := by
  have hmapderiv : ∀ f : PowerSeries ℤ_[p],
      PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (derivativeFun f)
        = derivativeFun (PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) f) := fun f => by
    ext n
    rw [PowerSeries.coeff_map, coeff_derivativeFun, coeff_derivativeFun, PowerSeries.coeff_map,
      map_mul, map_add, map_natCast, map_one]
  have hmapinv : PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (Ring.inverse g)
      = Ring.inverse (PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) g) := by
    symm
    rw [← mul_one (Ring.inverse _),
      Ring.inverse_mul_eq_iff_eq_mul _ _ _ (hg.map (PowerSeries.map _)),
      ← map_mul, Ring.mul_inverse_cancel _ hg, map_one]
  rw [dlog, map_mul, map_mul, hmapinv, hmapderiv, map_add, map_one, PowerSeries.map_X]

/-- Every `𝔽_p`-unit power series lifts to a `ℤ_[p]`-unit with the same reduction (the
constant coefficient, a unit mod `p`, is not in the maximal ideal, hence a unit). -/
private theorem exists_unit_lift_zmod {a : PowerSeries (ZMod p)} (ha : IsUnit a) :
    ∃ A : PowerSeries ℤ_[p], IsUnit A ∧
      PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) A = a := by
  obtain ⟨A, hA⟩ := PowerSeries.map_surjective _ (ZMod.ringHom_surjective PadicInt.toZMod) a
  refine ⟨A, ?_, hA⟩
  have ha0 : PowerSeries.constantCoeff (R := ZMod p) a ≠ 0 :=
    (PowerSeries.isUnit_iff_constantCoeff.1 ha).ne_zero
  rw [PowerSeries.isUnit_iff_constantCoeff, ← IsLocalRing.notMem_maximalIdeal,
    ← PadicInt.ker_toZMod, RingHom.mem_ker,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_map, hA,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact ha0

/-- **`B ⊆ A` mod `p` (RJW `lem:B mod p`, TeX 3346–3357)**: every `ψ`-fixed series is, mod `p`,
the logarithmic derivative of a `𝒩`-fixed unit. Apply `lem:B mod p 2`
(`fp_series_eq_dlog_add_frobC`) to `f̄`, lift the unit part `ā` to `g ∈ 𝒲` (`lem:A mod p`),
and kill the residual `(T+1)/T·C` part via the ψ-fixedness (`psiId_one_add_X_div_X_phi_eq_zero`,
since `f − Δg` is `ψ`-fixed over `ℤ_[p]`, hence its reduction is `ψ`-fixed). -/
private theorem exists_normOp_dlog_modEq {f : PowerSeries ℤ_[p]} (hf : psiSeries p f = f) :
    ∃ g : PowerSeries ℤ_[p], IsUnit g ∧ normOp g = g ∧ ModEqPow p 1 (dlog p g) f := by
  set F := PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) f with hF
  obtain ⟨a, b, c, ha, hc, hXb, hdecomp⟩ := fp_series_eq_dlog_add_frobC p F
  obtain ⟨A, hAunit, hAmap⟩ := exists_unit_lift_zmod p ha
  obtain ⟨g, hgunit, hgN, hgmod⟩ := exists_normOp_fixed_lift p A hAunit
  have hgmapa : PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) g = a := by
    rw [← hAmap]; exact (modEqPow_one_iff_map_toZMod (p := p)).1 hgmod
  have hmapdlog : PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (dlog p g)
      = (1 + PowerSeries.X) * derivativeFun a * Ring.inverse a := by
    rw [map_toZMod_dlog p hgunit, hgmapa]
  -- `b = (f − Δg) mod p`, and `f − Δg` is `ψ`-fixed (so `ψ b = b`)
  have hbmap : b = PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (f - dlog p g) := by
    rw [map_sub, hmapdlog, ← hF, hdecomp]; ring
  have hpsib : psiSeries p b = b := by
    rw [hbmap, ← map_toZMod_psiSeries]
    congr 1
    rw [psiSeries_sub p, hf, dlog_mem_psiIdSeries p hgunit hgN]
  have hb0 : b = 0 := psiId_one_add_X_div_X_phi_eq_zero p hpsib hXb hc
  refine ⟨g, hgunit, hgN, ?_⟩
  rw [modEqPow_one_iff_map_toZMod, hmapdlog, ← hF, hdecomp, hb0, add_zero]

/-! ### Successive approximation and the compact limit (`lem:log der red mod p`) -/

/-- The one-step refinement (`lem:log der red mod p`, TeX 3318–3322): a `ψ`-fixed `f` admits
`g ∈ 𝒲` and a `ψ`-fixed `f'` with `Δg = f + p·f'`. (From `exists_normOp_dlog_modEq`,
`Δg ≡ f mod p`, write the difference `C(p)·f'`; `f'` is `ψ`-fixed since `Δg − f` is and
`ℤ_[p]⟦T⟧` is `p`-torsion-free.) -/
private theorem exists_approx_step {f : PowerSeries ℤ_[p]} (hf : psiSeries p f = f) :
    ∃ (g f' : PowerSeries ℤ_[p]), IsUnit g ∧ normOp g = g ∧ psiSeries p f' = f' ∧
      dlog p g = f + PowerSeries.C (p : ℤ_[p]) * f' := by
  obtain ⟨g, hgunit, hgN, hgmod⟩ := exists_normOp_dlog_modEq p hf
  obtain ⟨f', hf'⟩ := modEqPow_iff_exists_C_mul.1 hgmod
  rw [pow_one] at hf'
  -- `Δg = f + C(p)·f'`
  have hdlogeq : dlog p g = f + PowerSeries.C (p : ℤ_[p]) * f' := by
    linear_combination hf'
  refine ⟨g, f', hgunit, hgN, ?_, hdlogeq⟩
  -- `ψ f' = f'`: apply `ψ` to `C(p)·f' = Δg − f`, both `ψ`-fixed; cancel `p`
  have hψC : psiSeries p (PowerSeries.C (p : ℤ_[p]) * f')
      = PowerSeries.C (p : ℤ_[p]) * psiSeries p f' := psiSeries_C_mul_padicInt _ _
  have hdiff : psiSeries p (PowerSeries.C (p : ℤ_[p]) * f')
      = PowerSeries.C (p : ℤ_[p]) * f' := by
    rw [← hf', psiSeries_sub p, dlog_mem_psiIdSeries p hgunit hgN, hf]
  rw [hψC] at hdiff
  -- `C(p)·(ψ f' − f') = 0`, and `C(p)` is a non-zero-divisor, so `ψ f' = f'`
  have hpz : PowerSeries.C (p : ℤ_[p]) * (psiSeries p f' - f') = 0 := by
    rw [mul_sub, hdiff, sub_self]
  have hpne : (PowerSeries.C (p : ℤ_[p]) : PowerSeries ℤ_[p]) ≠ 0 := by
    rw [Ne, ← map_zero (PowerSeries.C (R := ℤ_[p]))]
    exact fun h => (Nat.cast_ne_zero.mpr hp.out.ne_zero) (PowerSeries.C_injective h)
  exact sub_eq_zero.1 ((mul_eq_zero.1 hpz).resolve_left hpne)

/-- The successive-approximation sequences (`lem:log der red mod p`): `gₙ ∈ 𝒲`, `fₙ ∈ (ψ=id)`,
`f₀ = F`, and `Δ(g_{n+1}) = f_n + p·f_{n+1}` for all `n`. -/
private theorem exists_approx_seq {F : PowerSeries ℤ_[p]} (hF : psiSeries p F = F) :
    ∃ (gseq fseq : ℕ → PowerSeries ℤ_[p]), fseq 0 = F ∧ (∀ n, psiSeries p (fseq n) = fseq n) ∧
      (∀ n, IsUnit (gseq n)) ∧ (∀ n, normOp (gseq n) = gseq n) ∧
      (∀ n, dlog p (gseq (n + 1)) = fseq n + PowerSeries.C (p : ℤ_[p]) * fseq (n + 1)) := by
  classical
  set Q := {f : PowerSeries ℤ_[p] // psiSeries p f = f} with hQ
  -- the recursion data: `(gₙ, fₙ)` with `fₙ : Q`
  let stepG : Q → PowerSeries ℤ_[p] := fun q => (exists_approx_step p q.2).choose
  let stepF : Q → Q := fun q =>
    ⟨(exists_approx_step p q.2).choose_spec.choose,
      (exists_approx_step p q.2).choose_spec.choose_spec.2.2.1⟩
  let aux : ℕ → PowerSeries ℤ_[p] × Q := fun n => Nat.rec ((1 : PowerSeries ℤ_[p]), ⟨F, hF⟩)
    (fun _ pr => (stepG pr.2, stepF pr.2)) n
  refine ⟨fun n => (aux n).1, fun n => ((aux n).2 : PowerSeries ℤ_[p]), rfl,
    fun n => (aux n).2.2, ?_, ?_, ?_⟩
  · -- units: `gₙ = 1` at `n = 0`, else from the step
    intro n
    cases n with
    | zero => change IsUnit (1 : PowerSeries ℤ_[p]); exact isUnit_one
    | succ m => exact (exists_approx_step p (aux m).2.2).choose_spec.choose_spec.1
  · intro n
    cases n with
    | zero => change normOp (1 : PowerSeries ℤ_[p]) = 1; exact normOp_one
    | succ m => exact (exists_approx_step p (aux m).2.2).choose_spec.choose_spec.2.1
  · intro n
    exact (exists_approx_step p (aux n).2.2).choose_spec.choose_spec.2.2.2

/-- `𝒩(gⁿ) = gⁿ` for a `𝒩`-fixed `g` (`𝒩` is multiplicative). -/
private theorem normOp_pow {g : PowerSeries ℤ_[p]} (h : normOp g = g) (n : ℕ) :
    normOp (g ^ n) = g ^ n := by
  rw [← normOpHom_apply, map_pow, normOpHom_apply, h]

/-- `𝒩(g⁻¹) = g⁻¹` for a `𝒩`-fixed unit `g`. -/
private theorem normOp_inverse {g : PowerSeries ℤ_[p]} (hg : IsUnit g) (h : normOp g = g) :
    normOp (Ring.inverse g) = Ring.inverse g := by
  have hu : normOp (Ring.inverse g) * g = 1 := by
    have h1 : normOp (Ring.inverse g) * normOp g = 1 := by
      rw [← normOp_mul, Ring.inverse_mul_cancel _ hg, normOp_one]
    rwa [h] at h1
  nth_rewrite 2 [← one_mul (Ring.inverse g)]
  rw [← hu, mul_assoc, Ring.mul_inverse_cancel _ hg, mul_one]

/-- The `n`-th factor `g_{n+1}^{(−1)ⁿ pⁿ}` of `hₙ = ∏_{k=1}^n g_k^{(−1)^{k−1}p^{k−1}}`
(the negative-sign factors realised by `Ring.inverse`). -/
private def approxFactor (gseq : ℕ → PowerSeries ℤ_[p]) (n : ℕ) : PowerSeries ℤ_[p] :=
  if Even n then gseq (n + 1) ^ (p ^ n) else Ring.inverse (gseq (n + 1) ^ (p ^ n))

/-- The partial products `hₙ = ∏_{k=1}^n g_k^{(−1)^{k−1}p^{k−1}}` (built recursively). -/
private def approxProd (gseq : ℕ → PowerSeries ℤ_[p]) : ℕ → PowerSeries ℤ_[p]
  | 0 => 1
  | n + 1 => approxProd gseq n * approxFactor p gseq n

private theorem approxFactor_isUnit {gseq : ℕ → PowerSeries ℤ_[p]} (hg : ∀ n, IsUnit (gseq n))
    (n : ℕ) : IsUnit (approxFactor p gseq n) := by
  rw [approxFactor]
  by_cases hev : Even n
  · rw [if_pos hev]; exact (hg (n + 1)).pow _
  · rw [if_neg hev]; exact isUnit_ringInverse.mpr ((hg (n + 1)).pow _)

private theorem approxProd_isUnit {gseq : ℕ → PowerSeries ℤ_[p]} (hg : ∀ n, IsUnit (gseq n))
    (n : ℕ) : IsUnit (approxProd p gseq n) := by
  induction n with
  | zero => exact isUnit_one
  | succ m ih => exact ih.mul (approxFactor_isUnit p hg m)

private theorem approxProd_normOp {gseq : ℕ → PowerSeries ℤ_[p]} (hg : ∀ n, IsUnit (gseq n))
    (hN : ∀ n, normOp (gseq n) = gseq n) (n : ℕ) :
    normOp (approxProd p gseq n) = approxProd p gseq n := by
  induction n with
  | zero => exact normOp_one
  | succ m ih =>
    have hfac : normOp (approxFactor p gseq m) = approxFactor p gseq m := by
      rw [approxFactor]
      by_cases hev : Even m
      · rw [if_pos hev, normOp_pow p (hN (m + 1))]
      · rw [if_neg hev, normOp_inverse p ((hg (m + 1)).pow _) (normOp_pow p (hN (m + 1)) _)]
    rw [approxProd, normOp_mul, ih, hfac]

/-- `Δ(approxFactor n) = (−C p)ⁿ·(f_n + p·f_{n+1})` (the `n`-th summand of the telescope). -/
private theorem dlog_approxFactor {gseq fseq : ℕ → PowerSeries ℤ_[p]} (hg : ∀ n, IsUnit (gseq n))
    (hstep : ∀ n, dlog p (gseq (n + 1)) = fseq n + PowerSeries.C (p : ℤ_[p]) * fseq (n + 1))
    (n : ℕ) :
    dlog p (approxFactor p gseq n)
      = (- PowerSeries.C (p : ℤ_[p])) ^ n
        * (fseq n + PowerSeries.C (p : ℤ_[p]) * fseq (n + 1)) := by
  have hpow : dlog p (gseq (n + 1) ^ (p ^ n))
      = PowerSeries.C (p : ℤ_[p]) ^ n * dlog p (gseq (n + 1)) := by
    rw [dlog_pow p (hg (n + 1)), zsmul_eq_mul, Int.cast_natCast, Nat.cast_pow,
      show ((p : ℕ) : PowerSeries ℤ_[p]) = PowerSeries.C (p : ℤ_[p]) from (map_natCast _ _).symm]
  rw [approxFactor]
  by_cases hev : Even n
  · rw [if_pos hev, hpow, hstep, neg_pow, Even.neg_one_pow hev, one_mul]
  · rw [if_neg hev, dlog_inverse p ((hg (n + 1)).pow _), hpow, hstep, neg_pow,
      Odd.neg_one_pow (Nat.not_even_iff_odd.1 hev), neg_one_mul, neg_mul]

/-- **The telescoping identity** (`lem:log der red mod p`, TeX 3324–3328):
`Δ hₙ = f₀ − (−p)ⁿ·f_n`. -/
private theorem dlog_approxProd {gseq fseq : ℕ → PowerSeries ℤ_[p]} (hg : ∀ n, IsUnit (gseq n))
    (hstep : ∀ n, dlog p (gseq (n + 1)) = fseq n + PowerSeries.C (p : ℤ_[p]) * fseq (n + 1))
    (n : ℕ) :
    dlog p (approxProd p gseq n)
      = fseq 0 - (- PowerSeries.C (p : ℤ_[p])) ^ n * fseq n := by
  induction n with
  | zero => rw [approxProd, dlog_one]; simp
  | succ m ih =>
    rw [approxProd, dlog_mul p (approxProd_isUnit p hg m) (approxFactor_isUnit p hg m), ih,
      dlog_approxFactor p hg hstep, pow_succ]
    ring

/-! ### Continuity of `𝒩` (for `𝒲` closed under the compact limit)

`𝒲 = (ℤ_p⟦T⟧^×)^{𝒩=id}` is closed in the coefficientwise topology because `𝒩` is continuous
there. `𝒩 = det ∘ digitMatrix`, `det` is a polynomial in the entries, and `digitMatrix` is
continuous as the (coordinatewise) inverse of the continuous digit-assembly map
`G ↦ Σ_i (1+T)^i φ(G_i)` — a continuous bijection of the compact Hausdorff `ℤ_p⟦T⟧`, hence a
homeomorphism. (This is the analytic input RJW package as "`𝒲` is compact".) -/

section Continuity
open scoped PowerSeries.WithPiTopology

variable {p}

/-- A map into `ℤ_p⟦T⟧` is continuous iff continuous in every coefficient
(`tendsto_iff_coeff_tendsto`). -/
theorem continuous_of_coeff {X : Type*} [TopologicalSpace X]
    (g : X → PowerSeries ℤ_[p]) (h : ∀ n, Continuous (fun x => PowerSeries.coeff n (g x))) :
    Continuous g := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  exact fun d => (h d).continuousAt

/-- `coeff n (φ G) = Σ_{d ≤ n} G_d · coeff n (S^d)` (the finite substitution-coefficient
formula; `S = (1+T)^p − 1` has order `1`). -/
private theorem coeff_phiSeries_finite (G : PowerSeries ℤ_[p]) (n : ℕ) :
    PowerSeries.coeff n (phiSeries p G)
      = ∑ d ∈ Finset.range (n + 1), (PowerSeries.coeff d G) •
          PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) := by
  rw [phiSeries, PowerSeries.coeff_subst' (hasSubst_one_add_X_pow_sub_one p)]
  refine finsum_eq_finsetSum_of_support_subset _ (fun d hd => ?_)
  simp only [Function.mem_support] at hd
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hcon
  push Not at hcon
  refine hd ?_
  obtain ⟨U, hU⟩ := (PowerSeries.X_dvd_iff
    (φ := ((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]))).2 (by simp)
  rw [show PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) = 0 from by
    rw [hU, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)], smul_zero]

/-- `φ = subst((1+T)^p−1)` is continuous (each output coefficient is a finite `ℤ_[p]`-linear
combination of input coefficients). -/
theorem phiSeries_continuous :
    Continuous (phiSeries p : PowerSeries ℤ_[p] → PowerSeries ℤ_[p]) := by
  refine continuous_of_coeff _ (fun n => ?_)
  simp_rw [coeff_phiSeries_finite]
  refine continuous_finsetSum _ (fun d _ => ?_)
  rw [show (fun x : PowerSeries ℤ_[p] => (PowerSeries.coeff d x) •
      PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d))
      = fun x => PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d)
        • PowerSeries.coeff d x from by funext x; rw [smul_eq_mul, smul_eq_mul, mul_comm]]
  exact (PowerSeries.WithPiTopology.continuous_coeff ℤ_[p] d).const_smul _

variable (p)

/-- The digit-assembly bijection `(G_i) ↦ Σ_i (1+T)^i φ(G_i)` (bijective by
`existsUnique_digits_padicInt`). -/
private def digitAssembly : (Fin p → PowerSeries ℤ_[p]) ≃ PowerSeries ℤ_[p] where
  toFun G := ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (G i)
  invFun F := (existsUnique_digits_padicInt p F).choose
  left_inv G := (((existsUnique_digits_padicInt p
    (∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (G i))).choose_spec.2 G rfl)).symm
  right_inv F := ((existsUnique_digits_padicInt p F).choose_spec.1).symm

private theorem digitAssembly_continuous : Continuous (digitAssembly p) := by
  change Continuous (fun G : Fin p → PowerSeries ℤ_[p] =>
    ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ) * phiSeries p (G i))
  exact continuous_finsetSum _ (fun i _ =>
    continuous_const.mul (phiSeries_continuous.comp (continuous_apply i)))

/-- The digit map is a homeomorphism (continuous bijection of compact Hausdorff spaces). -/
private noncomputable def digitHomeo : (Fin p → PowerSeries ℤ_[p]) ≃ₜ PowerSeries ℤ_[p] :=
  Continuous.homeoOfEquivCompactToT2 (f := digitAssembly p) (digitAssembly_continuous p)

/-- `digitMatrix f (·) j = digitHomeo.symm (f·(1+T)^j)` (the `j`-th column is the digit family
of `f·(1+T)^j`, `digitMatrix_col_isDigitDecomp`). -/
private theorem digitMatrix_eq_symm (f : PowerSeries ℤ_[p]) (j : Fin p) :
    (fun i => digitMatrix f i j) = (digitHomeo p).symm (f * (1 + PowerSeries.X) ^ (j : ℕ)) := by
  refine (existsUnique_digits_padicInt p (f * (1 + PowerSeries.X) ^ (j : ℕ))).unique
    (digitMatrix_col_isDigitDecomp (p := p) f j) ?_
  exact ((digitHomeo p).apply_symm_apply (f * (1 + PowerSeries.X) ^ (j : ℕ))).symm

theorem digitMatrix_continuous (i j : Fin p) :
    Continuous (fun f : PowerSeries ℤ_[p] => digitMatrix f i j) := by
  rw [show (fun f : PowerSeries ℤ_[p] => digitMatrix f i j)
      = fun f => (digitHomeo p).symm (f * (1 + PowerSeries.X) ^ (j : ℕ)) i from by
    funext f; rw [show digitMatrix f i j = (fun i => digitMatrix f i j) i from rfl,
      digitMatrix_eq_symm p f j]]
  exact (continuous_apply i).comp ((digitHomeo p).symm.continuous.comp
    (continuous_id.mul continuous_const))

/-- **`𝒩` is continuous** for the coefficientwise topology (`det` of the continuous
`digitMatrix`). -/
theorem normOp_continuous : Continuous (normOp (p := p)) := by
  rw [show (normOp (p := p)) = fun f => Matrix.det (digitMatrix f) from by
    funext f; exact normOp_eq_det f]
  simp_rw [Matrix.det_apply]
  exact continuous_finsetSum _ (fun σ _ =>
    (continuous_finsetProd _ (fun i _ => digitMatrix_continuous p (σ i) i)).const_smul _)

end Continuity

open scoped PowerSeries.WithPiTopology in
/-- **RJW thm:log der (TeX 3280–3285) — the Coleman–Coates–Wiles short exact sequence.**
Surjectivity half: every `ψ`-fixed series is the logarithmic derivative of a `𝒩`-fixed
unit. (The kernel half is `rem:ker Δ`: `μ_{p−1}`.)

Proof (T1203c, CLOSED via the `ξ`-free route). RJW reduce surjectivity (`lem:log der red
mod p`, TeX 3315–3332) to the mod-`p` identity `A = B` (`A = Δ(𝒲) mod p`, `B = (ψ=id) mod p`):
* `A ⊆ B` mod `p` is `dlog_mem_psiIdSeries` reduced mod `p` (used inside the step lemma).
* `B ⊆ A` mod `p` (`lem:B mod p`) is `exists_normOp_dlog_modEq`: `lem:B mod p 2`
  (`fp_series_eq_dlog_add_frobC`) writes `f̄ = Δā + b̄`; lift `ā` to `g ∈ 𝒲` (`lem:A mod p`);
  the residual `(T+1)/T·C`-part `b̄` is killed by `psiId_one_add_X_div_X_phi_eq_zero`. The
  `ψ`-fixedness of `(T+1)/T` (RJW's `Eqphipsi`-based `LemmaPsiInvariant`, TeX 1521) is
  replaced by the **`ξ`-free series projection formula** `ψ(φd·F) = d·ψF`
  (`psiSeries_phiSeries_mul_zmod`) together with honest `ψ` over `𝔽_p⟦T⟧`
  (`existsUnique_digits_zmod`, via the `θ = (1+T)∂` eigenvalue argument) and `ψ(T^{p−1}) = 1`.
* The reduction (here) iterates the step (`exists_approx_seq`) to `g_i ∈ 𝒲`, `f_i ∈ (ψ=id)`
  with `Δ(g_i) − f_{i−1} = p f_i`, forms `h_n = ∏_{k=1}^n g_k^{(−1)^{k−1} p^{k−1}}`
  (`approxProd`), so `Δ h_n = f_0 − (−p)^n f_n` (`dlog_approxProd`), and takes a convergent
  subsequence in the compact `ℤ_p⟦T⟧^×` (`exists_subseq_tendsto`) with limit `h ∈ 𝒲`. The
  `Δ`-limit is passed through the **cleared** form `(1+T)·∂h = f_0·h` (avoiding
  inverse-continuity): `(1+T)·∂(h_{φj})` converges both to `(1+T)·∂h` (continuity of `∂`)
  and to `f_0·h` (the `(−p)^{φj}f_{φj}` term `→ 0`), so by limit uniqueness they agree. -/
theorem dlog_surjective_onto_psiId {F : PowerSeries ℤ_[p]} (hF : F ∈ psiIdSeries p) :
    ∃ g : PowerSeries ℤ_[p], IsUnit g ∧ normOp g = g ∧ dlog p g = F := by
  have hFpsi : psiSeries p F = F := hF
  obtain ⟨gseq, fseq, hf0, hfψ, hgu, hgN, hstep⟩ := exists_approx_seq p hFpsi
  -- the partial products `hₙ` and their `Δ`
  set hseq := approxProd p gseq with hhseq
  have hhseqU : ∀ n, IsUnit (hseq n) := fun n => approxProd_isUnit p hgu n
  have hhseqN : ∀ n, normOp (hseq n) = hseq n := fun n => approxProd_normOp p hgu hgN n
  have hdlogh : ∀ n, dlog p (hseq n)
      = F - (- PowerSeries.C (p : ℤ_[p])) ^ n * fseq n := fun n => by
    rw [hhseq, dlog_approxProd p hgu hstep n, hf0]
  -- the cleared form `(1+T)·∂(hₙ) = (F − (−p)ⁿ fₙ)·hₙ`
  have hcleared : ∀ n, (1 + PowerSeries.X) * derivativeFun (hseq n)
      = (F - (- PowerSeries.C (p : ℤ_[p])) ^ n * fseq n) * hseq n := fun n => by
    have h1 : dlog p (hseq n) * hseq n = (1 + PowerSeries.X) * derivativeFun (hseq n) := by
      rw [dlog, mul_assoc, Ring.inverse_mul_cancel _ (hhseqU n), mul_one]
    rw [← h1, hdlogh n]
  -- compactness: a convergent subsequence `h_{φ j} → h`
  obtain ⟨h, φ, hφmono, hconv⟩ := exists_subseq_tendsto hseq
  refine ⟨h, ?_, ?_, ?_⟩
  · -- `h` a unit (limit of units)
    refine (isClosed_isUnit (p := p)).mem_of_tendsto hconv ?_
    filter_upwards with j using hhseqU (φ j)
  · -- `𝒩 h = h`: `𝒩(h_{φj}) = h_{φj} → h` and `𝒩(h_{φj}) → 𝒩 h` (continuity), so equal
    have h1 : Filter.Tendsto (fun j => normOp (hseq (φ j))) Filter.atTop (nhds (normOp h)) :=
      ((normOp_continuous p).tendsto h).comp hconv
    have h2 : Filter.Tendsto (fun j => normOp (hseq (φ j))) Filter.atTop (nhds h) := by
      simp_rw [hhseqN]; exact hconv
    exact tendsto_nhds_unique h1 h2
  · -- `Δ h = F`: pass the cleared form through the limit
    have hLHS : Filter.Tendsto (fun j => (1 + PowerSeries.X) * derivativeFun (hseq (φ j)))
        Filter.atTop (nhds ((1 + PowerSeries.X) * derivativeFun h)) := by
      have hderiv : Filter.Tendsto (fun j => derivativeFun (hseq (φ j))) Filter.atTop
          (nhds (derivativeFun h)) := by
        rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
        intro m
        simp_rw [coeff_derivativeFun]
        exact (tendsto_coeff hconv (m + 1)).mul_const _
      exact Filter.Tendsto.const_mul _ hderiv
    have hWzero : Filter.Tendsto (fun j => (- PowerSeries.C (p : ℤ_[p])) ^ (φ j) * fseq (φ j))
        Filter.atTop (nhds 0) := by
      rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
      intro m
      rw [map_zero]
      have hcoeff : ∀ j, PowerSeries.coeff m
          ((- PowerSeries.C (p : ℤ_[p])) ^ (φ j) * fseq (φ j))
          = (-(p : ℤ_[p])) ^ (φ j) * PowerSeries.coeff m (fseq (φ j)) := fun j => by
        rw [show (- PowerSeries.C (p : ℤ_[p])) ^ (φ j)
            = PowerSeries.C ((-(p : ℤ_[p])) ^ (φ j)) from by rw [map_pow, map_neg],
          PowerSeries.coeff_C_mul]
      simp_rw [hcoeff]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_)
        (g := fun j => ((p : ℝ)⁻¹) ^ (φ j)) ?_
      · rw [norm_mul, norm_pow, norm_neg, PadicInt.norm_p]
        exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)
      · exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
          (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))).comp hφmono.tendsto_atTop
    -- RHS `(F − (−p)^{φj} f_{φj})·h_{φj} → F·h`
    have hRHS : Filter.Tendsto
        (fun j => (F - (- PowerSeries.C (p : ℤ_[p])) ^ (φ j) * fseq (φ j)) * hseq (φ j))
        Filter.atTop (nhds (F * h)) := by
      have hFW : Filter.Tendsto (fun j => F - (- PowerSeries.C (p : ℤ_[p])) ^ (φ j) * fseq (φ j))
          Filter.atTop (nhds F) := by
        have := tendsto_const_nhds (x := F) (f := Filter.atTop (α := ℕ)) |>.sub hWzero
        simpa using this
      exact hFW.mul hconv
    -- `(1+T)·∂h = F·h` by limit uniqueness; then `Δ h = F`
    have hkey : (1 + PowerSeries.X) * derivativeFun h = F * h :=
      tendsto_nhds_unique (by simpa only [hcleared] using hLHS) hRHS
    have hdh : dlog p h = (1 + PowerSeries.X) * derivativeFun h * Ring.inverse h := rfl
    rw [hdh, hkey, mul_assoc, Ring.mul_inverse_cancel _
      ((isClosed_isUnit (p := p)).mem_of_tendsto hconv (by
        filter_upwards with j using hhseqU (φ j))), mul_one]

/-- A power series with vanishing formal derivative is its constant coefficient. -/
private theorem eq_C_constantCoeff_of_derivativeFun_zero (g : PowerSeries ℤ_[p])
    (h : PowerSeries.derivativeFun g = 0) :
    g = PowerSeries.C (PowerSeries.constantCoeff (R := ℤ_[p]) g) := by
  ext n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_C]
  | succ m =>
    rw [PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero m)]
    have hcoeff := congrArg (PowerSeries.coeff m) h
    rw [PowerSeries.coeff_derivativeFun, map_zero] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_right (Nat.cast_add_one_ne_zero m)

/-- `𝒩(C c) = C (c^p)`: the digit matrix of a constant is the scalar `C c • 1`, so its
determinant (`= 𝒩`) is `(C c)^p = C (c^p)`. -/
theorem normOp_C (c : ℤ_[p]) : normOp (PowerSeries.C (R := ℤ_[p]) c) = PowerSeries.C (c ^ p) := by
  rw [normOp_eq_det, digitMatrix_C, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin, ← map_pow]

/-- The kernel of `Δ = ∂log` on `𝒩`-fixed units is `μ_{p−1}` (RJW rem:ker Δ, TeX
3176–3178): a constant `𝒩`-fixed unit `f` satisfies `f^p = f`. Stated as: `dlog g = 0`
and `𝒩 g = g` ⟹ `g` is a `(p−1)`-th root of unity (constant). -/
theorem dlog_eq_zero_normOp_fixed {g : PowerSeries ℤ_[p]} (hg : IsUnit g)
    (hN : normOp g = g) (hd : dlog p g = 0) :
    ∃ c : ℤ_[p], c ^ p = c ∧ g = PowerSeries.C c := by
  have hunit1 : IsUnit (1 + PowerSeries.X : PowerSeries ℤ_[p]) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  -- `dlog g = (1+X)·g'·g⁻¹ = 0`; cancel the two units `(1+X)` and `Ring.inverse g`
  have hgz : PowerSeries.derivativeFun g = 0 := by
    have hd' : (1 + PowerSeries.X) * PowerSeries.derivativeFun g * Ring.inverse g = 0 := hd
    rw [mul_eq_zero, mul_eq_zero] at hd'
    rcases hd' with (h1 | h2) | h3
    · exact absurd h1 hunit1.ne_zero
    · exact h2
    · exact absurd h3 (isUnit_ringInverse.mpr hg).ne_zero
  set c := PowerSeries.constantCoeff (R := ℤ_[p]) g with hc
  have hgC : g = PowerSeries.C c := eq_C_constantCoeff_of_derivativeFun_zero p g hgz
  refine ⟨c, ?_, hgC⟩
  -- `𝒩 g = g` and `g = C c` give `C (c^p) = C c`, hence `c^p = c`
  have : PowerSeries.C (c ^ p) = PowerSeries.C c := by rw [← normOp_C, ← hgC, hN, hgC]
  exact PowerSeries.C_injective this

/-! ### Solving `(1 − φ)G = F` coefficientwise (for the converse of `lem:rest zp*`)

RJW's converse argument constructs `G = Σ_{n≥0} φⁿ(F)` and uses `(p,T)`-adic convergence.
We instead solve `(1 − φ)G = F` by a coefficient recursion that avoids any topology: the
`n`-th coefficient of `φ G = G.subst((1+T)^p − 1)` is `Σ_{d ≤ n} G_d · [Tⁿ]((1+T)^p−1)^d`,
with the diagonal `d = n` term `pⁿ · G_n` (the substituted series has order `1`, leading
coefficient `p`). Hence `[Tⁿ]((1−φ)G) = G_n(1 − pⁿ) − Σ_{d<n} G_d·c_{n,d}`, and since
`1 − pⁿ` is a unit for `n ≥ 1` (`isUnit_one_sub_p_pow`) we may solve for `G_n` recursively
(`solCoeff`). The `n = 0` equation forces `F(0) = 0`. Then `ψ G = G` follows for free by
applying `ψ` (using `ψ φ = id` and `ψ F = 0`). -/

/-- `[T¹]((1+T)^p) = p`: from the cleared identity `(1+T)·∂((1+T)^p) = p(1+T)^p`, taking
the constant coefficient (`[T¹]f = [T⁰](∂f)`). -/
private theorem coeff_one_one_add_X_pow :
    PowerSeries.coeff 1 ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ p) = (p : ℤ_[p]) := by
  have h0 := congrArg (PowerSeries.coeff 0) (del_one_add_X_pow p p)
  rw [PadicMeasure.del] at h0
  rw [show (1 + PowerSeries.X : PowerSeries ℤ_[p]) * derivativeFun ((1 + PowerSeries.X) ^ p)
      = derivativeFun ((1 + PowerSeries.X) ^ p)
        + PowerSeries.X * derivativeFun ((1 + PowerSeries.X) ^ p) from by ring,
    map_add, PowerSeries.coeff_zero_X_mul, add_zero, coeff_derivativeFun,
    show (p : PowerSeries ℤ_[p]) * (1 + PowerSeries.X) ^ p
      = PowerSeries.C (p : ℤ_[p]) * (1 + PowerSeries.X) ^ p from by rw [map_natCast],
    PowerSeries.coeff_C_mul] at h0
  simp only [zero_add] at h0
  rw [show PowerSeries.coeff 0 ((1 + PowerSeries.X : PowerSeries ℤ_[p]) ^ p) = 1 from by simp,
    mul_one] at h0
  simpa using h0

/-- `[Tⁿ](((1+T)^p − 1)^d) = 0` for `n < d` (the substituted series has order `1`). -/
private theorem coeff_S_pow_vanish {d n : ℕ} (hdn : n < d) :
    PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) = 0 := by
  obtain ⟨U, hU⟩ := (PowerSeries.X_dvd_iff
    (φ := ((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]))).2 (by simp)
  rw [hU, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

/-- `[Tⁿ](((1+T)^p − 1)^n) = pⁿ` (the leading coefficient: `((1+T)^p − 1) = pT + O(T²)`). -/
private theorem coeff_S_pow_diag {d : ℕ} :
    PowerSeries.coeff d (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d)
      = (p : ℤ_[p]) ^ d := by
  obtain ⟨U, hU⟩ := (PowerSeries.X_dvd_iff
    (φ := ((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]))).2 (by simp)
  have hU0 : PowerSeries.constantCoeff (R := ℤ_[p]) U = (p : ℤ_[p]) := by
    have h1 : PowerSeries.coeff 1 ((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p])
        = (p : ℤ_[p]) := by
      rw [map_sub, coeff_one_one_add_X_pow, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero]
    rw [hU, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff] at h1
    exact h1
  have hstep : PowerSeries.coeff d (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d)
      = PowerSeries.coeff 0 (U ^ d) := by
    rw [hU, mul_pow]
    have := PowerSeries.coeff_X_pow_mul (U ^ d) d 0
    rwa [zero_add] at this
  rw [hstep, PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hU0]

/-- `[Tⁿ](φ G) = Σ_{d ≤ n} G_d · [Tⁿ](((1+T)^p − 1)^d)` (the substitution coefficient
formula, finite because `((1+T)^p − 1)^d` has order `d`). -/
private theorem coeff_phiSeries_split (G : PowerSeries ℤ_[p]) (n : ℕ) :
    PowerSeries.coeff n (phiSeries p G)
      = ∑ d ∈ Finset.range (n + 1), (PowerSeries.coeff d G) •
          PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) :=
  coeff_phiSeries_finite (p := p) G n

/-- `1 − pⁿ` is a unit of `ℤ_[p]` for `n ≥ 1` (it is `1 − (maximal ideal element)`). -/
private theorem isUnit_one_sub_p_pow {n : ℕ} (hn : 1 ≤ n) : IsUnit (1 - (p : ℤ_[p]) ^ n) := by
  refine IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ?_
  rw [mem_nonunits_iff, PadicInt.isUnit_iff, norm_pow]
  have hlt : ‖(p : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  exact fun hc => absurd hc (ne_of_lt (pow_lt_one₀ (norm_nonneg _) hlt (by omega)))

/-- The recursively-defined coefficients of the solution `G` to `(1 − φ)G = F`:
`G₀ = 0`, and `Gₙ = (1 − pⁿ)⁻¹·(Fₙ + Σ_{d<n} G_d·[Tⁿ](((1+T)^p−1)^d))` for `n ≥ 1`. -/
private def solCoeff (F : PowerSeries ℤ_[p]) : ℕ → ℤ_[p]
  | n => if n = 0 then 0 else
      Ring.inverse (1 - (p : ℤ_[p]) ^ n) *
        (PowerSeries.coeff n F + ∑ d ∈ (Finset.range n).attach, (solCoeff F d.1) *
          PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d.1))
  decreasing_by exact Finset.mem_range.1 d.2

private theorem solCoeff_zero (F : PowerSeries ℤ_[p]) : solCoeff p F 0 = 0 := by
  rw [solCoeff, if_pos rfl]

private theorem solCoeff_eq (F : PowerSeries ℤ_[p]) {n : ℕ} (hn : n ≠ 0) :
    solCoeff p F n = Ring.inverse (1 - (p : ℤ_[p]) ^ n) *
        (PowerSeries.coeff n F + ∑ d ∈ Finset.range n, (solCoeff p F d) *
          PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d)) := by
  rw [solCoeff, if_neg hn]; congr 2
  rw [← Finset.sum_attach (Finset.range n) (fun d => (solCoeff p F d) *
    PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d))]

/-- The constructed series `G = mk (solCoeff F)` solves `(1 − φ)G = F` when `F(0) = 0`. -/
private theorem mk_solCoeff_sub_phi (F : PowerSeries ℤ_[p])
    (h0 : PowerSeries.constantCoeff (R := ℤ_[p]) F = 0) :
    PowerSeries.mk (solCoeff p F) - phiSeries p (PowerSeries.mk (solCoeff p F)) = F := by
  set G := PowerSeries.mk (solCoeff p F) with hG
  have hcoeffG : ∀ m, PowerSeries.coeff m G = solCoeff p F m := fun m => by rw [hG, coeff_mk]
  ext n
  rw [map_sub]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [hcoeffG, solCoeff_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_phiSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeffG,
      solCoeff_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  · rw [hcoeffG, coeff_phiSeries_split, Finset.sum_range_succ]
    simp only [hcoeffG, smul_eq_mul]
    rw [coeff_S_pow_diag, solCoeff_eq p F (by omega)]
    set Sigma := ∑ d ∈ Finset.range n, solCoeff p F d *
      PowerSeries.coeff n (((1 + PowerSeries.X) ^ p - 1 : PowerSeries ℤ_[p]) ^ d) with hSig
    set u := (1 - (p : ℤ_[p]) ^ n) with hu
    have hunit : IsUnit u := isUnit_one_sub_p_pow p (by omega)
    have hexp : Ring.inverse u * (PowerSeries.coeff n F + Sigma)
        - (Sigma + Ring.inverse u * (PowerSeries.coeff n F + Sigma) * (p : ℤ_[p]) ^ n)
        = PowerSeries.coeff n F := by
      have heq : Ring.inverse u * (PowerSeries.coeff n F + Sigma) * (1 - (p : ℤ_[p]) ^ n)
          = PowerSeries.coeff n F + Sigma := by
        rw [mul_assoc, mul_comm (PowerSeries.coeff n F + Sigma) (1 - (p : ℤ_[p]) ^ n),
          ← mul_assoc, ← hu, Ring.inverse_mul_cancel _ hunit, one_mul]
      linear_combination heq
    rw [hexp]

/-- **RJW lem:rest zp* (TeX 3387–3391)**: the exactness
`0 → ℤ_p → ℤ_p⟦T⟧^{ψ=id} →[1−φ] ℤ_p⟦T⟧^{ψ=0} → ℤ_p → 0`. Surjectivity of `eval₀`
half (`1+T ↦ 1`) + kernel-`ℤ_p` half. -/
theorem one_sub_phi_psiId_mem_psiZero {F : PowerSeries ℤ_[p]} (hF : F ∈ psiIdSeries p) :
    F - phiHom p F ∈ psiZeroSeries p := by
  have hFid : psiSeries p F = F := hF
  change psiSeries p (F - phiHom p F) = 0
  rw [psiSeries_sub, phiHom_apply, psiSeries_phi_padicInt, hFid, sub_self]

/-- The converse half of `lem:rest zp*`: every `ψ = 0` series with `F(0) = 0` is `(1−φ)G`
for some `ψ`-fixed `G`. The coefficient recursion `solCoeff` builds `G` with `(1−φ)G = F`
(`mk_solCoeff_sub_phi`); `ψ G = G` is then automatic (apply `ψ` to `G − φG = F`, using
`ψ φ = id` and `ψ F = 0`). -/
theorem exists_one_sub_phi_eq {F : PowerSeries ℤ_[p]} (hF : F ∈ psiZeroSeries p)
    (h0 : constantCoeff F = 0) :
    ∃ G ∈ psiIdSeries p, G - phiHom p G = F := by
  set G := PowerSeries.mk (solCoeff p F) with hG
  have hsub : G - phiHom p G = F := by rw [phiHom_apply]; exact mk_solCoeff_sub_phi p F h0
  refine ⟨G, ?_, hsub⟩
  -- `ψ G = G`: apply `ψ` to `G − φG = F`
  have hFz : psiSeries p F = 0 := hF
  change psiSeries p G = G
  have hψ := congrArg (psiSeries p) hsub
  rw [psiSeries_sub, phiHom_apply, psiSeries_phi_padicInt, hFz] at hψ
  -- `ψ G − G = 0`
  exact sub_eq_zero.1 hψ

end PadicLFunctions.Coleman
