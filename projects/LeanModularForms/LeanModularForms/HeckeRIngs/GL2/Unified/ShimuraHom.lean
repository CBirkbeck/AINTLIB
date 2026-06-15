/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.HeckeRIngs.GL2.Fricke

/-!
# The Shimura-convention Hecke action `Ψ_χ` as the Fricke conjugate of `Φ_χ`

The companion `heckeRingHomCharSpace` (`Φ_χ`) sends a `Γ₀(N)` double coset to the Hecke
operator of its *adjugate* class (a `V_p`-type operator at bad primes `p ∣ N`).  The
mathematically standard Shimura-convention action `Ψ_χ` is its **Fricke conjugate**:

`Ψ_χ(T) := E.symm ∘ Φ_{χ'}(T) ∘ E`,  where `E := frickeCharEquiv (χ := χ)` is the Fricke
isomorphism `M_k(N, χ) ≃ M_k(N, χ')` and `χ' := chiConj χ = χ ∘ (·)⁻¹`.

Because the Atkin–Lehner anti-involution `ι(δ) = W·adj(δ)·W⁻¹` swaps the right-coset
decomposition (on whose adjugates `Φ` is built) into the left-coset decomposition, this
conjugate is the genuine left-coset operator.  In particular, at a bad prime `p ∣ N`, the
slash representatives `W⁻¹·adj([[1,0],[Nr,p]])·W = [[1,r],[0,p]]` are exactly the `U_p`
representatives.

`Ψ_χ` is a ring homomorphism for free: conjugation by a `LinearEquiv` is an algebra
automorphism of `End`.

## Main definitions

* `conjEndRingHomFricke` — conjugation by `frickeCharEquiv` as a ring hom
  `End (M_k(N, χ')) →+* End (M_k(N, χ))`.
* `heckeRingHomCharSpaceShimura` (`Ψ_χ`) — the Shimura-convention Hecke ring action.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4–3.5.
* Atkin–Lehner, *Hecke operators on `Γ₀(m)`*.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn
open HeckeRing
open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]
variable {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- Conjugation of an endomorphism of `M_k(N, chiConj χ)` by the Fricke isomorphism
`E = frickeCharEquiv (χ := χ)`, yielding an endomorphism of `M_k(N, χ)`:
`T ↦ E.symm ∘ T ∘ E`. -/
noncomputable def conjEndFricke (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : Module.End ℂ (modFormCharSpace k (chiConj χ))) :
    Module.End ℂ (modFormCharSpace k χ) :=
  (frickeCharEquiv k χ).symm.toLinearMap ∘ₗ T ∘ₗ (frickeCharEquiv k χ).toLinearMap

/-- Conjugation by `frickeCharEquiv` is a ring hom
`End (M_k(N, χ')) →+* End (M_k(N, χ))`. -/
noncomputable def conjEndRingHomFricke (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (modFormCharSpace k (chiConj χ)) →+* Module.End ℂ (modFormCharSpace k χ) where
  toFun := conjEndFricke k χ
  map_one' := LinearMap.ext fun x ↦ by
    show (frickeCharEquiv k χ).symm
      ((1 : Module.End ℂ _) ((frickeCharEquiv k χ) x)) = x
    rw [Module.End.one_apply, LinearEquiv.symm_apply_apply]
  map_mul' S T := LinearMap.ext fun x ↦ by
    show (frickeCharEquiv k χ).symm ((S * T) ((frickeCharEquiv k χ) x)) =
      (frickeCharEquiv k χ).symm (S ((frickeCharEquiv k χ) ((frickeCharEquiv k χ).symm
        (T ((frickeCharEquiv k χ) x)))))
    rw [LinearEquiv.apply_symm_apply, Module.End.mul_apply]
  map_zero' := LinearMap.ext fun _ ↦ by simp [conjEndFricke]
  map_add' _ _ := LinearMap.ext fun _ ↦ by
    simp [conjEndFricke, LinearMap.add_apply, map_add]

@[simp] lemma conjEndRingHomFricke_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : Module.End ℂ (modFormCharSpace k (chiConj χ))) :
    conjEndRingHomFricke (N := N) k χ T = conjEndFricke k χ T := rfl

/-- **The Shimura-convention Hecke action `Ψ_χ`** on the Nebentypus character space
`M_k(Γ₁(N), χ)`, as a ring homomorphism `𝕋(Γ₀(N)) →+* End_ℂ (M_k(Γ₁(N), χ))`.

It is the Fricke conjugate of the companion `Φ_{χ'}` (`heckeRingHomCharSpace` at the
inverse-conjugate character `χ' = chiConj χ`):
`Ψ_χ(T) = E.symm ∘ Φ_{χ'}(T) ∘ E`. -/
noncomputable def heckeRingHomCharSpaceShimura (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    𝕋 (Gamma0_pair N) ℤ →+* Module.End ℂ (modFormCharSpace k χ) :=
  (conjEndRingHomFricke (N := N) k χ).comp
    (heckeRingHomCharSpace (k := k) (χ := chiConj χ))

@[simp] lemma heckeRingHomCharSpaceShimura_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : 𝕋 (Gamma0_pair N) ℤ) :
    heckeRingHomCharSpaceShimura (N := N) k χ T =
      conjEndFricke k χ (heckeRingHomCharSpace (k := k) (χ := chiConj χ) T) := rfl

/-- The single-coset Fricke-conjugation identity at the **function level**: for `f` in the
`χ`-Nebentypus space, the Shimura action `Ψ_χ(T_single D 1)` applied to `f`, as a function on
`ℍ`, equals the sum over the right-coset decomposition of `D` of the `χ'`-weighted slash by
the **`W`-conjugated** adjugate representatives `W · tRep_gen D i · W⁻¹` (`= ι(deltaRepGen i)`,
the Atkin–Lehner image).  This is the clean algebraic core: the two Fricke factors `W`
contribute `W·(·)·W` per term, which equals `(W·(·)·W⁻¹) · W²`, and `W² = c·I` cancels the
`c⁻¹` from `E.symm`. -/
theorem heckeRingHomCharSpaceShimura_single_coe (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f : modFormCharSpace k χ) :
    (⇑((heckeRingHomCharSpaceShimura (N := N) k χ (T_single (Gamma0_pair N) ℤ D 1) f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        (↑(delta0NebentypusWeight (N := N) (chiConj χ) D i) : ℂ)⁻¹ •
          (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
            (frickeGL N * tRep_gen (Gamma0_pair N) D i * (frickeGL N)⁻¹ : GL (Fin 2) ℚ)) := by
  set Φf : modFormCharSpace k (chiConj χ) :=
    heckeRingHomCharSpace (k := k) (χ := chiConj χ) (T_single (Gamma0_pair N) ℤ D 1)
      (frickeCharEquiv k χ f)
  have hstep1 : (⇑((heckeRingHomCharSpaceShimura (N := N) k χ
        (T_single (Gamma0_pair N) ℤ D 1) f : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      (frickeScalar N k)⁻¹ •
        ((⇑(Φf : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) ∣[k]
          (frickeGL N : GL (Fin 2) ℚ)) := by
    show (⇑((((frickeCharEquiv k χ).symm) Φf : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
    show (⇑((((frickeScalar N k)⁻¹ • frickeCharRestrict k (chiConj χ)) Φf :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
    rw [LinearMap.smul_apply]
    show ((frickeScalar N k)⁻¹ • ⇑((frickeCharRestrict k (chiConj χ) Φf :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
    rw [frickeCharRestrict_coe, frickeOperator_coe]
  have hEf : (⇑((frickeCharEquiv k χ f : modFormCharSpace k (chiConj χ)) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) ∣[k]
        (frickeGL N : GL (Fin 2) ℚ) := by
    show (⇑((frickeCharRestrict k χ f : modFormCharSpace k (chiConj χ)) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) = _
    rw [frickeCharRestrict_coe, frickeOperator_coe]
  have hstep2 : (⇑(Φf : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        (↑(delta0NebentypusWeight (N := N) (chiConj χ) D i) : ℂ)⁻¹ •
          ((⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
            (frickeGL N : GL (Fin 2) ℚ)) ∣[k]
              tRep_gen (Gamma0_pair N) D i) := by
    have hΦf' : (Φf : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
        ((nebentypusHeckeSum (N := N) (k := k) (χ := chiConj χ)
          (T_single (Gamma0_pair N) ℤ D 1) (frickeCharEquiv k χ f) :
          modFormCharSpace k (chiConj χ)) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl
    rw [hΦf', nebentypusHeckeSum_apply_coe, twistedHeckeSlashExtGen,
      Finsupp.sum_single_index (by simp :
        (0 : ℤ) • twistedHeckeSlashGen (N := N) k (chiConj χ) D
          (⇑(frickeCharEquiv k χ f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) = 0),
      one_zsmul, twistedHeckeSlashGen, hEf]
  rw [hstep1, hstep2, SlashAction.sum_slash, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_slash_pos_det k _ _ _ frickeGL_det_pos, smul_smul,
    ← SlashAction.slash_mul, ← SlashAction.slash_mul,
    show (frickeGL N : GL (Fin 2) ℚ) * (tRep_gen (Gamma0_pair N) D i * frickeGL N) =
        (frickeGL N * tRep_gen (Gamma0_pair N) D i) * frickeGL N by group,
    slash_mul_frickeGL, smul_smul,
    show (frickeGL N : GL (Fin 2) ℚ) * tRep_gen (Gamma0_pair N) D i * (frickeGL N)⁻¹ =
        frickeGL N * tRep_gen (Gamma0_pair N) D i * (frickeGL N)⁻¹ from rfl]
  congr 1
  rw [mul_assoc, mul_comm (↑(delta0NebentypusWeight (N := N) (chiConj χ) D i) : ℂ)⁻¹,
    ← mul_assoc, inv_mul_cancel₀ (frickeScalar_ne_zero (N := N) (k := k)), one_mul]

/- Bad-prime infrastructure: the lower-unipotent representatives.

At a bad prime `p ∣ N` the right-coset representatives of
`D_p = Γ₀(N)·diag(1,p)·Γ₀(N)` are the lower-unipotent matrices
`lunipRep p r = [[1,0],[N·r,p]]`, `r = 0, …, p−1`.  We exhibit them as factorisations
`h₁ · rep(D_p) · h₂` through the abstract representative, build the index bijection
`Fin p ≃ decompQuot`, compute their Nebentypus character (`= 1`), and assemble the
**true** bad-prime matching: the χ-twisted slash sum equals the sum of slashes by the
*adjugates* `adj(lunipRep r)` — which the Fricke conjugation then turns into `U_p`. -/

section BadPrime

variable (p : ℕ)

/-- The lower-unipotent `Γ₀(N)`-element `[[1,0],[N·r,1]]`. -/
noncomputable def lunipH (r : ℕ) : GL (Fin 2) ℚ :=
  mapGL ℚ (⟨!![1, 0; (N : ℤ) * r, 1], by simp [Matrix.det_fin_two]⟩ : SL(2, ℤ))

lemma lunipH_mem (r : ℕ) : lunipH (N := N) r ∈ (Gamma0_pair N).H :=
  Subgroup.mem_map_of_mem _ (by
    rw [CongruenceSubgroup.Gamma0_mem]
    show (((!![1, 0; (N : ℤ) * r, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0
    simp)

lemma lunipRep_eq_lunipH_mul_diag (hp : 0 < p) (r : ℕ) :
    lunipRep (N := N) p hp r =
      lunipH (N := N) r * (diag_1p_delta_Gamma0 N p hp : GL (Fin 2) ℚ) := by
  apply Units.ext
  ext i j
  have hpos : ∀ m : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) m := fun m ↦ by
    fin_cases m <;> simp [hp]
  simp only [Units.val_mul, lunipRep_coe, diag_1p_delta_Gamma0, diagMat_val _ _ hpos,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, lunipH,
    mapGL_coe_matrix, algebraMap_int_eq]
  fin_cases i <;> fin_cases j <;> simp

lemma lunipRep_mem_toSet (hp : Nat.Prime p) (r : ℕ) :
    (lunipRep (N := N) p hp.pos r) ∈ HeckeCoset.toSet (D_p_Gamma0 N p hp.pos) :=
  mem_D_p_Gamma0_of_factor_through_diag N p hp.pos _ (lunipH (N := N) r) 1
    (lunipH_mem r) (one_mem _)
    (by rw [mul_one]; exact lunipRep_eq_lunipH_mul_diag p hp.pos r)

/-- Every bad lower-unipotent representative factors through the abstract coset
representative. -/
lemma lunipRep_factorisation (hp : Nat.Prime p) (r : ℕ) :
    ∃ (h₁ : GL (Fin 2) ℚ) (_ : h₁ ∈ (Gamma0_pair N).H)
      (h₂ : GL (Fin 2) ℚ) (_ : h₂ ∈ (Gamma0_pair N).H),
      lunipRep (N := N) p hp.pos r =
        h₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL (Fin 2) ℚ) * h₂ := by
  have h := lunipRep_mem_toSet (N := N) p hp r
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at h
  obtain ⟨a, ha, c, hc, heq⟩ := h
  exact ⟨a, ha, c, hc, heq⟩

/-- The Nebentypus character of (any `Δ`-packaging of) a lower-unipotent representative
is `1`: its upper-left entry is `1`. -/
lemma lunipRep_deltaChar (hp : Nat.Prime p) (r : ℕ) (χ'' : (ZMod N)ˣ →* ℂˣ)
    (g : (Gamma0_pair N).Δ)
    (hg : (g : GL (Fin 2) ℚ) = lunipRep (N := N) p hp.pos r) :
    delta0NebentypusDeltaChar (N := N) χ'' g = 1 := by
  unfold delta0NebentypusDeltaChar
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [show (1 : ℂˣ) = χ'' 1 from (map_one χ'').symm]
  congr 1
  apply Units.ext
  rw [delta0UpperUnit_val, Units.val_one]
  have hwit : delta0IntegralMatrix (N := N) g = !![1, 0; (N : ℤ) * r, (p : ℤ)] := by
    apply delta0IntegralMatrix_witness_unique
    rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lunipRep, GeneralLinearGroup.mkOfDetNeZero, Matrix.map_apply]
  rw [hwit]
  simp

/-- The index map `Fin p → decompQuot` attached to the lower-unipotent factorisations. -/
noncomputable def lunipPsi (hp : Nat.Prime p) :
    Fin p → decompQuot (Gamma0_pair N) (HeckeCoset.rep (D_p_Gamma0 N p hp.pos)) :=
  fun r ↦ ⟦⟨(lunipRep_factorisation (N := N) p hp r.val).choose,
    (lunipRep_factorisation (N := N) p hp r.val).choose_spec.choose⟩⟧

/-- Unadjugated companion of `adj_quot_eq_imp_inv_mul_mem_H`: two factorisations through
the representative whose `H`-parts agree in `decompQuot` differ by a right `Γ₀(N)`-factor. -/
lemma quot_eq_imp_inv_mul_mem_H' (g : (Gamma0_pair N).Δ)
    (a₁ : GL (Fin 2) ℚ) (ha₁ : a₁ ∈ (Gamma0_pair N).H)
    (c₁ : GL (Fin 2) ℚ) (hc₁ : c₁ ∈ (Gamma0_pair N).H)
    (a₂ : GL (Fin 2) ℚ) (ha₂ : a₂ ∈ (Gamma0_pair N).H)
    (c₂ : GL (Fin 2) ℚ) (hc₂ : c₂ ∈ (Gamma0_pair N).H)
    (g₁ g₂ : GL (Fin 2) ℚ)
    (heq₁ : g₁ = a₁ * (g : GL (Fin 2) ℚ) * c₁)
    (heq₂ : g₂ = a₂ * (g : GL (Fin 2) ℚ) * c₂)
    (hquot : (⟦(⟨a₁, ha₁⟩ : (Gamma0_pair N).H)⟧ :
        decompQuot (Gamma0_pair N) g) = ⟦⟨a₂, ha₂⟩⟧) :
    g₁⁻¹ * g₂ ∈ (Gamma0_pair N).H := by
  rw [heq₁, heq₂]
  have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact hquot)
  rw [Subgroup.mem_subgroupOf] at hrel
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hrel
  simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at hrel
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  have h_prod : (a₁ * (g : GL (Fin 2) ℚ) * c₁)⁻¹ * (a₂ * (g : GL (Fin 2) ℚ) * c₂) =
      c₁⁻¹ * (((g : GL (Fin 2) ℚ))⁻¹ * (a₁⁻¹ * a₂) * (g : GL (Fin 2) ℚ)) * c₂ := by
    group
  rw [h_prod]
  exact (Gamma0_pair N).H.mul_mem
    ((Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.inv_mem hc₁) hrel) hc₂

/-- Distinct lower-unipotent representatives lie in distinct right cosets: the quotient
matrix `[[1,0],[N(r'−r)/p,1]]` lies in `Γ₀(N)` only when `p ∣ r'−r`. -/
lemma lunipPsi_injective (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    Function.Injective (lunipPsi (N := N) p hp) := by
  intro r r' hquot
  by_contra hne
  obtain ⟨ha₁, c₁, hc₁, heq₁⟩ := (lunipRep_factorisation (N := N) p hp r.val).choose_spec
  obtain ⟨ha₂, c₂, hc₂, heq₂⟩ := (lunipRep_factorisation (N := N) p hp r'.val).choose_spec
  have hmem := quot_eq_imp_inv_mul_mem_H' (N := N)
    (⟨HeckeCoset.rep (D_p_Gamma0 N p hp.pos),
      (HeckeCoset.rep (D_p_Gamma0 N p hp.pos)).2⟩)
    _ ha₁ c₁ hc₁ _ ha₂ c₂ hc₂ _ _ heq₁ heq₂ hquot
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hmat : ((lunipRep (N := N) p hp.pos r.val)⁻¹ *
      lunipRep (N := N) p hp.pos r'.val : GL (Fin 2) ℚ) =
      GeneralLinearGroup.mkOfDetNeZero
        !![1, 0; ((N : ℚ) * r' - (N : ℚ) * r) / p, 1] (by
          rw [Matrix.det_fin_two_of]
          simp) := by
    rw [inv_mul_eq_iff_eq_mul]
    apply Units.ext
    ext i j
    have hco : ∀ s : ℕ, (↑(lunipRep (N := N) p hp.pos s) : Matrix (Fin 2) (Fin 2) ℚ) =
        !![1, 0; (N : ℚ) * s, (p : ℚ)] := fun s ↦ lunipRep_coe p hp.pos s
    fin_cases i <;> fin_cases j <;> simp only [Units.val_mul, hco,
        GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply, Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
      (try simp) <;> (try field_simp) <;> (try ring)
  rw [hmat] at hmem
  obtain ⟨γ, hγ, hγeq⟩ := Subgroup.mem_map.mp hmem
  have hentry : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ) =
      ((N : ℚ) * r' - (N : ℚ) * r) / p := by
    have := congr_arg (fun M : GL (Fin 2) ℚ ↦ (M : Matrix (Fin 2) (Fin 2) ℚ) 1 0) hγeq
    simpa [mapGL_coe_matrix, GeneralLinearGroup.mkOfDetNeZero] using this
  have hdvdN : (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hγ
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  obtain ⟨m, hm⟩ := hdvdN
  have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hkey : (p : ℤ) * m = (r' : ℤ) - r := by
    have h1 : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ) * p =
        (N : ℚ) * r' - (N : ℚ) * r := by
      rw [hentry]
      field_simp
    rw [hm] at h1
    push_cast at h1
    have h2 : (N : ℚ) * (m * p) = (N : ℚ) * ((r' : ℚ) - r) := by
      ring_nf
      ring_nf at h1
      linarith
    have h3 : (m : ℚ) * p = (r' : ℚ) - r := mul_left_cancel₀ hNQ h2
    exact_mod_cast (by linarith : (p : ℚ) * m = (r' : ℚ) - r)
  have habs : (p : ℤ) ∣ (r' : ℤ) - r := ⟨m, hkey.symm⟩
  have hzero : ((r' : ℤ) - r) = 0 := by
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs habs ?_
    have h1 := r.isLt
    have h2 := r'.isLt
    simp only [Int.natAbs_natCast]
    omega
  exact hne (Fin.ext (by omega : r.val = r'.val))

lemma lunipPsi_bijective (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    Function.Bijective (lunipPsi (N := N) p hp) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨lunipPsi_injective (N := N) p hp hpN, ?_⟩
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
  exact (decompQuot_D_p_Gamma0_bad_natcard (N := N) p hp hpN).symm

/-- **The true bad-prime matching**: for a `Γ₀(N),χ''`-twisted-invariant function `g`, the
χ''-twisted Hecke slash at the bad class equals the plain sum of slashes by the **adjugated**
lower-unipotent representatives.  (The non-adjugated/`U_p` form is FALSE for the
right-coset convention; the Fricke conjugation below converts
the adjugates into the genuine `U_p` matrices.) -/
theorem twistedHeckeSlashGen_bad (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (χ'' : (ZMod N)ˣ →* ℂˣ) {k : ℤ} {g : ℍ → ℂ} (hg : IsGamma0TwistedInvariant (N := N) k χ'' g) :
    twistedHeckeSlashGen (N := N) k χ'' (D_p_Gamma0 N p hp.pos) g =
      ∑ r ∈ Finset.range p, g ∣[k] GL_adjugate (lunipRep (N := N) p hp.pos r) := by
  rw [twistedHeckeSlashGen, ← Fin.sum_univ_eq_sum_range
    (fun r ↦ g ∣[k] GL_adjugate (lunipRep (N := N) p hp.pos r)) p]
  refine (Fintype.sum_bijective (lunipPsi (N := N) p hp)
    (lunipPsi_bijective (N := N) p hp hpN) _ _ fun r ↦ ?_).symm
  obtain ⟨ha₁, c₁, hc₁, heq₁⟩ := (lunipRep_factorisation (N := N) p hp r.val).choose_spec
  set h₁ := (lunipRep_factorisation (N := N) p hp r.val).choose
  have habs := twisted_weighted_slash_tRep_gen_of_mem (N := N) k χ''
    (D_p_Gamma0 N p hp.pos) h₁ ha₁ c₁ hc₁ g hg
  have htriple_char : delta0NebentypusDeltaChar (N := N) χ''
      (gamma0TripleDelta (N := N) (D_p_Gamma0 N p hp.pos) h₁ ha₁ c₁ hc₁) = 1 := by
    refine lunipRep_deltaChar (N := N) p hp r.val χ'' _ ?_
    show h₁ * (HeckeCoset.rep (D_p_Gamma0 N p hp.pos) : GL (Fin 2) ℚ) * c₁ = _
    exact heq₁.symm
  rw [htriple_char, Units.val_one, inv_one, one_smul, ← heq₁] at habs
  show g ∣[k] GL_adjugate (lunipRep (N := N) p hp.pos r.val) =
    (↑(delta0NebentypusWeight (N := N) χ'' (D_p_Gamma0 N p hp.pos)
      (lunipPsi (N := N) p hp r)) : ℂ)⁻¹ •
      (g ∣[k] tRep_gen (Gamma0_pair N) (D_p_Gamma0 N p hp.pos) (lunipPsi (N := N) p hp r))
  exact habs

end BadPrime

/- Bad-prime payoff `Ψ(D_p) = U_p`.

The matrix algebra is fully verified: at a bad prime `p ∣ N`, the right-coset representatives
of `D_p = Γ₀(N)·diag(1,p)·Γ₀(N)` are the lower-unipotent `δ_r = [[1,0],[N·r,p]]`
(`r = 0, …, p−1`; `lunip_inject` / `decompQuot_D_p_Gamma0_bad_natcard`), each with upper-left
unit `1` (so `χ'`-weight `1`), and the `W`-conjugated adjugate is exactly the `U_p`
representative:
`W · adj(δ_r) · W⁻¹ = W · [[p,0],[−N·r,1]] · W⁻¹ = [[1,r],[0,p]] = T_p_upper(r)`
(machine-checked above as a `GL₂(ℚ)` matrix identity).

Combined with `heckeRingHomCharSpaceShimura_single_coe`, this gives
`Ψ_χ(D_p)(f) = ∑_r (⇑f) ∣ T_p_upper(r) = U_p(f)`.  The remaining gap is the **index
bijection bookkeeping**: identifying `decompQuot`'s abstract index set with `Fin p` via the
explicit reps `lunip_inject` (currently `private` in `CongruenceHecke/Props.lean`), matching
`deltaRepGen` to `[[1,0],[N·r,p]]`, and absorbing the residual `Γ₁(N)` factor (left of the
slash, killed by `f`'s `Γ₁(N)`-invariance).  This mirrors `twisted_matches_T_p` /
`twistedTpPsi` (the good-prime analogue) but on the `W`-conjugated bad reps. -/
theorem heckeRingHomCharSpaceShimura_D_p_bad (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    heckeRingHomCharSpaceShimura (N := N) k χ (heckeRingDp p hp.pos) =
      heckeT_p_all_charRestrict k p hp χ := by
  refine LinearMap.ext fun f ↦ Subtype.ext (DFunLike.coe_injective ?_)
  show (⇑((heckeRingHomCharSpaceShimura (N := N) k χ
      (T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N p hp.pos) 1) f : modFormCharSpace k χ) :
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : ℍ → ℂ) =
    (⇑(heckeT_p_all k p hp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) : ℍ → ℂ)
  rw [heckeRingHomCharSpaceShimura_single_coe, heckeT_p_all_not_coprime_apply k hp hpN,
    heckeT_p_ut]
  set g := ⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] (frickeGL N : GL (Fin 2) ℚ)
    with hg_def
  have hg : IsGamma0TwistedInvariant (N := N) k (chiConj χ) g :=
    coe_mem_twistedInvariant (frickeOperator k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
      (frickeOperator_mem_charSpace (N := N) k χ f.property)
  have hfrickeInvDetPos : 0 < ((frickeGL N)⁻¹ : GL (Fin 2) ℚ).det.val := by
    rw [show ((frickeGL N)⁻¹ : GL (Fin 2) ℚ).det.val =
        ((frickeGL N).det.val)⁻¹ by rw [← Units.val_inv_eq_inv_val, ← map_inv]]
    exact inv_pos.mpr frickeGL_det_pos
  have hterm : ∀ (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep (D_p_Gamma0 N p hp.pos))),
      (↑(delta0NebentypusWeight (chiConj χ) (D_p_Gamma0 N p hp.pos) i) : ℂ)⁻¹ •
        (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
          (frickeGL N * tRep_gen (Gamma0_pair N) (D_p_Gamma0 N p hp.pos) i * (frickeGL N)⁻¹)) =
      ((↑(delta0NebentypusWeight (chiConj χ) (D_p_Gamma0 N p hp.pos) i) : ℂ)⁻¹ •
          g ∣[k] tRep_gen (Gamma0_pair N) (D_p_Gamma0 N p hp.pos) i) ∣[k] (frickeGL N)⁻¹ := by
    intro i
    rw [show ⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
        (frickeGL N * tRep_gen (Gamma0_pair N) (D_p_Gamma0 N p hp.pos) i * (frickeGL N)⁻¹) =
        (g ∣[k] tRep_gen (Gamma0_pair N) (D_p_Gamma0 N p hp.pos) i) ∣[k] (frickeGL N)⁻¹
      by rw [← SlashAction.slash_mul, ← SlashAction.slash_mul]; congr 1; group,
      smul_slash_pos_det k _ _ _ hfrickeInvDetPos]
  rw [Finset.sum_congr rfl (fun i _ ↦ hterm i), ← SlashAction.sum_slash]
  rw [show ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep (D_p_Gamma0 N p hp.pos)),
        (↑(delta0NebentypusWeight (chiConj χ) (D_p_Gamma0 N p hp.pos) i) : ℂ)⁻¹ •
          (g ∣[k] tRep_gen (Gamma0_pair N) (D_p_Gamma0 N p hp.pos) i) =
      twistedHeckeSlashGen (N := N) k (chiConj χ) (D_p_Gamma0 N p hp.pos) g from rfl]
  rw [twistedHeckeSlashGen_bad (N := N) p hp hpN (chiConj χ) hg, SlashAction.sum_slash]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [hg_def, ← SlashAction.slash_mul, ← SlashAction.slash_mul]
  congr 1
  rw [← mul_assoc, frickeGL_mul_adj_lunipRep_mul_frickeGL_inv]

end HeckeRing.GL2.Unified
