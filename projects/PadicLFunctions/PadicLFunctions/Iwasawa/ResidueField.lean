/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.IwasawaProof.GaloisAction
import PadicLFunctions.Interpolation.Branches

/-!
# The residue field of `𝒪_n` and the Teichmüller section (RJW §12.1/§12.5, TeX 3159–3168)

`K_n = ℚ_p(ξ_{p^n})/ℚ_p` is **totally ramified** of degree `p^{n-1}(p−1)`, so the residue
field of `𝒪_n = O p n` is `𝔽_p` at *every* level `n` — the same as `ℚ_p`'s. Consequences
formalised here:

* **`norm_levelNorm_sub_one_lt_one`** — the relative norm of a principal unit is principal:
  `‖N_{n+1,n}(w) − 1‖ < 1` for `‖w − 1‖ < 1`. This is the norm-residue compatibility (the
  residue extension `k(n+1)/k(n) = 𝔽_p/𝔽_p` is trivial, so the residue-norm is the identity);
  proved via `Algebra.norm_eq_prod_automorphisms` over the (now-Galois) relative extension and
  the spectral-norm isometry of relative `K_n`-automorphisms (`norm_algEquiv_ES`).
* **`residueZp`** — the `ℤ_p`-residue of `u.elems n` (the `a` with `‖u.elems n − toCp a‖ ≤ ‖π_n‖`,
  from `exists_residue_pi`), and its **constancy** `toZMod(residueZp u n) = toZMod(residueZp u 1)`
  across levels (`toZMod_residueZp_eq_one`), the norm-residue compatibility plus Fermat
  `a^p ≡ a mod p`.
* **`omegaNCU b`** — the constant Teichmüller `NormCompatUnits` system `ω(b)` (parallel to
  `FundamentalSequence.teichNCU`), `(p−1)`-torsion (`omegaNCU_torsion`).
* **`normCompat_eq_teichmuller_mul_principal`** — the Teichmüller split `u = v·w` with `v = ω(b)`
  `(p−1)`-torsion (`b = residueZp u 1`) and `w ∈ 𝒰_{∞,1}` principal (RJW §12.1, the deferred
  `Equivariance.lean` blocker, closed here).

`p` is odd throughout the norm collapse (`levelNorm_const_eq_pow`, `Tower.lean`); the residue
arguments themselves are `p`-agnostic.
-/

open PadicLFunctions PadicLFunctions.Coleman

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

private theorem prod_sub_one_lt_one {ι : Type*} (s : Finset ι) (f : ι → ℂ_[p])
    (hle : ∀ i ∈ s, ‖f i‖ ≤ 1) (hone : ∀ i ∈ s, ‖f i - 1‖ < 1) :
    ‖(∏ i ∈ s, f i) - 1‖ < 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha,
      show f a * (∏ i ∈ t, f i) - 1 = f a * ((∏ i ∈ t, f i) - 1) + (f a - 1) by ring]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖f a‖ * ‖(∏ i ∈ t, f i) - 1‖ ≤ 1 * ‖(∏ i ∈ t, f i) - 1‖ :=
            mul_le_mul_of_nonneg_right (hle a (Finset.mem_insert_self a t)) (norm_nonneg _)
        _ = ‖(∏ i ∈ t, f i) - 1‖ := one_mul _
        _ < 1 := ih (fun i hi => hle i (Finset.mem_insert_of_mem hi))
            (fun i hi => hone i (Finset.mem_insert_of_mem hi))
    · exact hone a (Finset.mem_insert_self a t)

private noncomputable def restrictAbsES {n : ℕ} :
    AbsoluteValue (IntermediateField.extendScalars (K_le_succ p n)) ℝ where
  toFun z := ‖(z : ℂ_[p])‖
  map_mul' x y := by push_cast; rw [norm_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by
    rw [norm_eq_zero]; exact ⟨fun h => by exact_mod_cast h, fun h => by rw [h]; rfl⟩
  add_le' x y := by push_cast; exact norm_add_le _ _

set_option synthInstance.maxHeartbeats 1000000 in
-- the `spectralNorm`/`finiteDimensional` reasoning runs through the nested
-- `IntermediateField (K p n) (extendScalars …)` layer; instance synthesis exceeds defaults
private theorem norm_coe_eq_spectralNorm_ES {n : ℕ}
    (z : IntermediateField.extendScalars (K_le_succ p n)) :
    ‖(z : ℂ_[p])‖ = spectralNorm ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) z := by
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) :=
    finiteDimensional_K p (n + 1)
  refine spectralNorm_unique_field_norm_ext (K := ℚ_[p])
    (L := IntermediateField.extendScalars (K_le_succ p n)) (f := restrictAbsES p) (fun k => ?_) z
  change ‖((algebraMap ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) k) : ℂ_[p])‖ = ‖k‖
  rw [show ((algebraMap ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) k) : ℂ_[p])
      = algebraMap ℚ_[p] ℂ_[p] k by rw [← IntermediateField.algebraMap_apply]; rfl]
  simp

set_option synthInstance.maxHeartbeats 1000000 in
-- the `minpoly`/`spectralNorm` reasoning runs through the nested
-- `IntermediateField (K p n) (extendScalars …)` layer; instance synthesis exceeds defaults
private theorem norm_algEquiv_ES {n : ℕ}
    (σ : (IntermediateField.extendScalars (K_le_succ p n)) ≃ₐ[ℚ_[p]]
         (IntermediateField.extendScalars (K_le_succ p n)))
    (z : IntermediateField.extendScalars (K_le_succ p n)) :
    ‖(σ z : ℂ_[p])‖ = ‖(z : ℂ_[p])‖ := by
  rw [norm_coe_eq_spectralNorm_ES p (σ z), norm_coe_eq_spectralNorm_ES p z,
    spectralNorm, spectralNorm, minpoly.algEquiv_eq σ z]

set_option synthInstance.maxHeartbeats 1000000 in
-- the `IsGalois`/`norm_eq_prod_automorphisms` reasoning runs through the nested
-- `IntermediateField (K p n) (extendScalars …)` layer; instance synthesis exceeds defaults
/-- **Norm-residue compatibility** (RJW §12.1, TeX 3162 — totally-ramified ⟹ trivial residue
extension): the relative norm of a principal unit is principal. For `w ∈ K_{n+1}` with
`‖w − 1‖ < 1`, `‖N_{n+1,n}(w) − 1‖ < 1`. -/
theorem norm_levelNorm_sub_one_lt_one {n : ℕ} {w : ℂ_[p]} (hw : w ∈ K p (n + 1))
    (hwone : ‖w - 1‖ < 1) :
    ‖levelNorm p n w - 1‖ < 1 := by
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) :=
    finiteDimensional_K p (n + 1)
  haveI : FiniteDimensional (K p n) (IntermediateField.extendScalars (K_le_succ p n)) :=
    FiniteDimensional.right ℚ_[p] (K p n) _
  haveI hgalQ : IsGalois ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) :=
    isGalois_K p (n + 1)
  haveI : IsGalois (K p n) (IntermediateField.extendScalars (K_le_succ p n)) :=
    IsGalois.tower_top_of_isGalois ℚ_[p] (K p n) _
  set W : IntermediateField.extendScalars (K_le_succ p n) :=
    ⟨w, (IntermediateField.mem_extendScalars (K_le_succ p n)).2 hw⟩
  have hwnorm : ‖w‖ = 1 := by
    have hle : ‖w‖ ≤ 1 := by
      have h := IsUltrametricDist.norm_add_le_max (w - 1) (1 : ℂ_[p])
      rw [sub_add_cancel, norm_one] at h
      exact le_trans h (max_le hwone.le le_rfl)
    have hge : 1 ≤ ‖w‖ := by
      have h := IsUltrametricDist.norm_add_le_max w (1 - w)
      rw [add_sub_cancel, norm_one] at h
      have h1w : ‖(1 : ℂ_[p]) - w‖ < 1 := by rwa [norm_sub_rev]
      rcases le_max_iff.mp h with hh | hh
      · exact hh
      · linarith
    linarith
  have hprod := Algebra.norm_eq_prod_automorphisms (K p n) W
  have hcoe : (levelNorm p n w) = ∏ σ : (IntermediateField.extendScalars (K_le_succ p n))
        ≃ₐ[K p n] (IntermediateField.extendScalars (K_le_succ p n)), (σ W : ℂ_[p]) := by
    rw [levelNorm_apply p n hw]
    have hc := congrArg
      (fun (z : IntermediateField.extendScalars (K_le_succ p n)) => (z : ℂ_[p])) hprod
    rw [IntermediateField.coe_prod] at hc
    rw [← hc]; rfl
  rw [hcoe]
  refine prod_sub_one_lt_one p _ _ (fun σ _ => ?_) (fun σ _ => ?_)
  · rw [show (σ W : ℂ_[p]) = ((σ.restrictScalars ℚ_[p]) W : ℂ_[p]) from rfl,
      norm_algEquiv_ES p (σ.restrictScalars ℚ_[p]) W, show (W : ℂ_[p]) = w from rfl, hwnorm]
  · have hσ1 : (σ W : ℂ_[p]) - 1 = (σ (W - 1) : ℂ_[p]) := by rw [map_sub, map_one]; rfl
    rwa [hσ1, show (σ (W - 1) : ℂ_[p]) = ((σ.restrictScalars ℚ_[p]) (W - 1) : ℂ_[p]) from rfl,
      norm_algEquiv_ES p (σ.restrictScalars ℚ_[p]) (W - 1),
      show ((W - 1 : IntermediateField.extendScalars (K_le_succ p n)) : ℂ_[p]) = w - 1 by
      push_cast; rfl]

private noncomputable def residueZp (u : NormCompatUnits p) (n : ℕ) (hn : 1 ≤ n) : ℤ_[p] :=
  (exists_residue_pi p hn (Subring.mem_inf.1 (u.mem n)).1 (Subring.mem_inf.1 (u.mem n)).2).choose

private theorem residueZp_spec (u : NormCompatUnits p) (n : ℕ) (hn : 1 ≤ n) :
    ‖(u.elems n : ℂ_[p]) - toCp p (residueZp p u n hn)‖ ≤ ‖pi p n‖ :=
  (exists_residue_pi p hn (Subring.mem_inf.1 (u.mem n)).1
    (Subring.mem_inf.1 (u.mem n)).2).choose_spec

-- the `levelNorm`/`norm_levelNorm_sub_one_lt_one` chain elaborates through the nested
-- `IntermediateField (K p n) (extendScalars …)` Galois-product layer, exceeding the default
private theorem toZMod_residueZp_succ (u : NormCompatUnits p) {n : ℕ} (hn : 1 ≤ n)
    (hn1 : 1 ≤ n + 1) :
    PadicInt.toZMod (residueZp p u (n + 1) hn1) = PadicInt.toZMod (residueZp p u n hn) := by
  set c : ℂ_[p] := (u.elems (n + 1) : ℂ_[p])
  set a₁ : ℤ_[p] := residueZp p u (n + 1) hn1
  set a₀ : ℤ_[p] := residueZp p u n hn
  have hcK : c ∈ K p (n + 1) := (Subring.mem_inf.1 (u.mem (n + 1))).1
  have hcnorm : ‖c‖ = 1 := norm_eq_one_of_mem_localUnits p
    ((mem_localUnits_iff p).2
      ⟨u.mem (n + 1), by rw [Units.val_inv_eq_inv_val]; exact u.inv_mem (n + 1)⟩)
  have hsmall1 : ‖c - toCp p a₁‖ < 1 :=
    lt_of_le_of_lt (residueZp_spec p u (n + 1) hn1) (norm_pi_lt_one p (by omega))
  have ha1norm : ‖a₁‖ = 1 := by
    rw [← norm_toCp p a₁]
    have hh := IsUltrametricDist.norm_add_le_max (toCp p a₁) (c - toCp p a₁)
    rw [show toCp p a₁ + (c - toCp p a₁) = c by ring] at hh
    have hle : ‖toCp p a₁‖ ≤ 1 := by rw [norm_toCp]; exact PadicInt.norm_le_one _
    rcases le_max_iff.mp hh with h1 | h1
    · linarith [hcnorm.ge]
    · linarith [hsmall1]
  have ha1ne : toCp p a₁ ≠ 0 := by rw [← norm_pos_iff, norm_toCp, ha1norm]; exact one_pos
  set w : ℂ_[p] := c * (toCp p a₁)⁻¹ with hw
  have hwK : w ∈ K p (n + 1) := mul_mem hcK ((K p (n + 1)).inv_mem (by
    rw [toCp, RingHom.comp_apply, PadicInt.Coe.ringHom_apply]
    exact (K p (n + 1)).algebraMap_mem _))
  have hwone : ‖w - 1‖ < 1 := by
    rw [show w - 1 = (c - toCp p a₁) * (toCp p a₁)⁻¹ by rw [hw, sub_mul, mul_inv_cancel₀ ha1ne],
      norm_mul, norm_inv, norm_toCp, ha1norm, inv_one, mul_one]
    exact hsmall1
  have hcfac : c = toCp p a₁ * w := by
    rw [hw, mul_comm (toCp p a₁), mul_assoc, inv_mul_cancel₀ ha1ne, mul_one]
  have htoa1K : toCp p a₁ ∈ K p (n + 1) := by
    rw [toCp, RingHom.comp_apply, PadicInt.Coe.ringHom_apply]; exact (K p (n + 1)).algebraMap_mem _
  have htoa1Kn : toCp p a₁ ∈ K p n := by
    rw [toCp, RingHom.comp_apply, PadicInt.Coe.ringHom_apply]; exact (K p n).algebraMap_mem _
  have hNc : levelNorm p n c = (toCp p a₁) ^ p * levelNorm p n w := by
    rw [hcfac, levelNorm_mul p n htoa1K hwK, levelNorm_const_eq_pow p hn htoa1Kn]
  have hun : (u.elems n : ℂ_[p]) = levelNorm p n c := (u.compat n hn).symm
  have hun_a0 : ‖(u.elems n : ℂ_[p]) - toCp p a₀‖ < 1 :=
    lt_of_le_of_lt (residueZp_spec p u n hn) (norm_pi_lt_one p hn)
  have hNw : ‖levelNorm p n w - 1‖ < 1 := norm_levelNorm_sub_one_lt_one p hwK hwone
  have hkey2 : ‖toCp p a₀ - (toCp p a₁) ^ p‖ < 1 := by
    rw [show toCp p a₀ - (toCp p a₁) ^ p
        = (toCp p a₀ - (u.elems n : ℂ_[p])) + ((toCp p a₁) ^ p * (levelNorm p n w - 1)) by
      rw [hun, hNc]; ring]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [show toCp p a₀ - (u.elems n : ℂ_[p]) = -((u.elems n : ℂ_[p]) - toCp p a₀) by ring,
        norm_neg]
      exact hun_a0
    · rw [norm_mul, norm_pow, norm_toCp, ha1norm, one_pow, one_mul]
      exact hNw
  have hkey3 : ‖a₀ - a₁ ^ p‖ < 1 := by
    rwa [← norm_toCp p (a₀ - a₁ ^ p), map_sub, map_pow]
  have hmem : a₀ - a₁ ^ p ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton, ← PadicInt.norm_lt_one_iff_dvd]
  have hz : PadicInt.toZMod a₀ = PadicInt.toZMod (a₁ ^ p) := by
    have h0 : PadicInt.toZMod (a₀ - a₁ ^ p) = 0 := by
      rwa [← RingHom.mem_ker, PadicInt.ker_toZMod]
    rwa [map_sub, sub_eq_zero] at h0
  rw [hz, map_pow, ZMod.pow_card]

/-- **Norm-residue constancy** (totally-ramified tower): `toZMod(residueZp u n)` is constant in
`n ≥ 1`, equal to `toZMod(residueZp u 1)` (induction on the constancy step). -/
private theorem toZMod_residueZp_eq_one (u : NormCompatUnits p) {n : ℕ} (hn : 1 ≤ n) :
    PadicInt.toZMod (residueZp p u n hn) = PadicInt.toZMod (residueZp p u 1 (le_refl 1)) := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge 1 (m + 1) with h1 | h1
    · have hm : 1 ≤ m := by omega
      rw [toZMod_residueZp_succ p u hm hn, ih hm]
    · have hm0 : m = 0 := by omega
      subst hm0; congr 1

/-- The constant Teichmüller `NormCompatUnits` system `ω(b)` for `b : ℤ_[p]ˣ`: every level is
`toCp(ω(b))`. Parallel to `FundamentalSequence.teichNCU`, exported here for the §12.1/§12.5
split. -/
noncomputable def omegaNCU (b : ℤ_[p]ˣ) : NormCompatUnits p where
  elems _ := Units.map (toCp p).toMonoidHom (PadicInt.isUnit_teichmullerFun p b).unit
  mem n := by
    change toCp p ((PadicInt.isUnit_teichmullerFun p b).unit : ℤ_[p]) ∈ O p n
    refine Subring.mem_inf.2 ⟨?_, ?_⟩
    · change toCp p _ ∈ K p n
      rw [toCp, RingHom.comp_apply]; exact IntermediateField.algebraMap_mem (K p n) _
    · change ‖toCp p ((PadicInt.isUnit_teichmullerFun p b).unit : ℤ_[p])‖ ≤ 1
      rw [norm_toCp]; exact PadicInt.norm_le_one _
  inv_mem n := by
    rw [← Units.val_inv_eq_inv_val, ← map_inv, Units.coe_map]
    change toCp p (((PadicInt.isUnit_teichmullerFun p b).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ∈ O p n
    refine Subring.mem_inf.2 ⟨?_, ?_⟩
    · change toCp p _ ∈ K p n
      rw [toCp, RingHom.comp_apply]; exact IntermediateField.algebraMap_mem (K p n) _
    · change ‖toCp p (((PadicInt.isUnit_teichmullerFun p b).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])‖ ≤ 1
      rw [norm_toCp]; exact PadicInt.norm_le_one _
  compat n hn := by
    have hmemK : (toCp p ((PadicInt.isUnit_teichmullerFun p b).unit : ℤ_[p])) ∈ K p n := by
      rw [toCp, RingHom.comp_apply]; exact IntermediateField.algebraMap_mem (K p n) _
    change levelNorm p n (toCp p ((PadicInt.isUnit_teichmullerFun p b).unit : ℤ_[p]))
      = toCp p ((PadicInt.isUnit_teichmullerFun p b).unit : ℤ_[p])
    rw [levelNorm_const_eq_pow p hn hmemK, ← map_pow]
    congr 1
    have hpow : ((PadicInt.isUnit_teichmullerFun p b).unit : ℤ_[p]) ^ (p - 1) = 1 := by
      rw [IsUnit.unit_spec]; exact PadicInt.teichmullerFun_pow_card_sub_one p b
    rw [show ((PadicInt.isUnit_teichmullerFun p b).unit : ℤ_[p]) ^ p
        = ((PadicInt.isUnit_teichmullerFun p b).unit : ℤ_[p]) ^ (p - 1)
          * ((PadicInt.isUnit_teichmullerFun p b).unit : ℤ_[p]) by
        rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le],
      hpow, one_mul]

/-- `ω(b)` is `(p−1)`-torsion at every level. -/
theorem omegaNCU_torsion (b : ℤ_[p]ˣ) (n : ℕ) : (omegaNCU p b).elems n ^ (p - 1) = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change (toCp p ((PadicInt.isUnit_teichmullerFun p b).unit : ℤ_[p])) ^ (p - 1) = 1
  rw [IsUnit.unit_spec, ← map_pow, PadicInt.teichmullerFun_pow_card_sub_one p b, map_one]

/-- The `ℂ_p`-value of `ω(b)` at any level is `toCp(ω(b))`. -/
theorem omegaNCU_elems (b : ℤ_[p]ˣ) (n : ℕ) :
    ((omegaNCU p b).elems n : ℂ_[p]) = toCp p (PadicInt.teichmullerFun p (b : ℤ_[p])) := by
  change (toCp p ((PadicInt.isUnit_teichmullerFun p b).unit : ℤ_[p])) = _
  rw [IsUnit.unit_spec]

private theorem norm_residueZp (u : NormCompatUnits p) {n : ℕ} (hn : 1 ≤ n) :
    ‖residueZp p u n hn‖ = 1 := by
  set c : ℂ_[p] := (u.elems n : ℂ_[p])
  have hcnorm : ‖c‖ = 1 := norm_eq_one_of_mem_localUnits p
    ((mem_localUnits_iff p).2 ⟨u.mem n, by rw [Units.val_inv_eq_inv_val]; exact u.inv_mem n⟩)
  have hsmall : ‖c - toCp p (residueZp p u n hn)‖ < 1 :=
    lt_of_le_of_lt (residueZp_spec p u n hn) (norm_pi_lt_one p hn)
  rw [← norm_toCp p (residueZp p u n hn)]
  have hh := IsUltrametricDist.norm_add_le_max (toCp p (residueZp p u n hn))
    (c - toCp p (residueZp p u n hn))
  rw [show toCp p (residueZp p u n hn) + (c - toCp p (residueZp p u n hn)) = c by ring] at hh
  have hle : ‖toCp p (residueZp p u n hn)‖ ≤ 1 := by rw [norm_toCp]; exact PadicInt.norm_le_one _
  rcases le_max_iff.mp hh with h1 | h1
  · linarith [hcnorm.ge]
  · linarith [hsmall]

private noncomputable def teichUnit (u : NormCompatUnits p) : ℤ_[p]ˣ :=
  (PadicInt.isUnit_iff.2 (norm_residueZp p u (le_refl 1))).unit

private theorem teichUnit_val (u : NormCompatUnits p) :
    (teichUnit p u : ℤ_[p]) = residueZp p u 1 (le_refl 1) := IsUnit.unit_spec _

private theorem norm_elems_sub_omega_lt_one (u : NormCompatUnits p) {n : ℕ} (hn : 1 ≤ n) :
    ‖(u.elems n : ℂ_[p]) - toCp p (PadicInt.teichmullerFun p (teichUnit p u : ℤ_[p]))‖ < 1 := by
  set a₀ : ℤ_[p] := residueZp p u n hn
  set b : ℤ_[p] := (teichUnit p u : ℤ_[p]) with hb
  have h1 : ‖(u.elems n : ℂ_[p]) - toCp p a₀‖ < 1 :=
    lt_of_le_of_lt (residueZp_spec p u n hn) (norm_pi_lt_one p hn)
  have hres : PadicInt.toZMod a₀ = PadicInt.toZMod b := by
    rw [hb, teichUnit_val]; exact toZMod_residueZp_eq_one p u hn
  have homega : PadicInt.teichmullerFun p a₀ = PadicInt.teichmullerFun p b := by
    rw [PadicInt.teichmullerFun, PadicInt.teichmullerFun, hres]
  have h2 : ‖toCp p a₀ - toCp p (PadicInt.teichmullerFun p b)‖ < 1 := by
    rw [← homega, ← map_sub, norm_toCp]
    have hmem : a₀ - PadicInt.teichmullerFun p a₀ ∈ Ideal.span {(p : ℤ_[p])} := by
      rw [show a₀ - PadicInt.teichmullerFun p a₀
          = -(PadicInt.teichmullerFun p a₀ - a₀) by ring, neg_mem_iff]
      exact PadicInt.teichmullerFun_sub_self_mem p a₀
    rwa [Ideal.mem_span_singleton, ← PadicInt.norm_lt_one_iff_dvd] at hmem
  rw [show (u.elems n : ℂ_[p]) - toCp p (PadicInt.teichmullerFun p b)
      = ((u.elems n : ℂ_[p]) - toCp p a₀)
        + (toCp p a₀ - toCp p (PadicInt.teichmullerFun p b)) by ring]
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)

/-- **RJW §12.1 Lemma (TeX 3159–3168)**: `𝒰_∞ = μ_{p−1} × 𝒰_{∞,1}` (Teichmüller split of
the reduction-mod-`𝔭_n` SES `1 → 𝒰_{n,1} → 𝒰_n → μ_{p−1} → 1`). Every tower unit `u` splits as
`u = v·w` with `v = ω(b)` `(p−1)`-torsion (`b = residueZp u 1`, the residue Teichmüller lift)
and `w ∈ 𝒰_{∞,1}` principal. -/
theorem normCompat_eq_teichmuller_mul_principal (u : NormCompatUnits p) :
    ∃ v w : NormCompatUnits p, w ∈ unitsTower1 p ∧
      (∀ n, (v.elems n) ^ (p - 1) = 1) ∧ u = v * w := by
  set b : ℤ_[p]ˣ := teichUnit p u
  set v : NormCompatUnits p := omegaNCU p b
  set w : NormCompatUnits p := v⁻¹ * u with hw
  refine ⟨v, w, ?_, fun n => omegaNCU_torsion p b n, ?_⟩
  · intro n hn
    have hwval : ((w.elems n : ℂ_[p]ˣ) : ℂ_[p])
        = (toCp p (PadicInt.teichmullerFun p (b : ℤ_[p])))⁻¹ * (u.elems n : ℂ_[p]) := by
      change ((v⁻¹.elems n * u.elems n : ℂ_[p]ˣ) : ℂ_[p]) = _
      rw [Units.val_mul, show v⁻¹.elems n = (v.elems n)⁻¹ from rfl, Units.val_inv_eq_inv_val,
        omegaNCU_elems p b n]
    set ζ := toCp p (PadicInt.teichmullerFun p (b : ℤ_[p])) with hζ
    have hζnorm : ‖ζ‖ = 1 := by
      rw [hζ, norm_toCp]; exact PadicInt.isUnit_iff.1 (PadicInt.isUnit_teichmullerFun p b)
    have hζne : ζ ≠ 0 := by rw [← norm_pos_iff, hζnorm]; exact one_pos
    refine (mem_localUnitsOne_iff (p := p)).2 ⟨?_, ?_⟩
    · exact (mem_localUnits_iff p).2
        ⟨w.mem n, by rw [Units.val_inv_eq_inv_val]; exact w.inv_mem n⟩
    · rw [hwval,
        show ζ⁻¹ * (u.elems n : ℂ_[p]) - 1 = ζ⁻¹ * ((u.elems n : ℂ_[p]) - ζ) by
          rw [mul_sub, inv_mul_cancel₀ hζne],
        norm_mul, norm_inv, hζnorm, inv_one, one_mul]
      exact norm_elems_sub_omega_lt_one p u hn
  · rw [hw, ← mul_assoc, mul_inv_cancel, one_mul]

end PadicLFunctions.Coleman
