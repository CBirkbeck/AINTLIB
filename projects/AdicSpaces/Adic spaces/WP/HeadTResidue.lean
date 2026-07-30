/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.RestrictedFubini
import «Adic spaces».FJP.TateNullstellensatz
import «Adic spaces».WP.Heads

/-!
# Residue finiteness up the `T_N⟨T⟩` tower

([hrw-decomposition] D-prep, stage 1.)  The `k`-th Tate extension of the
even part of the head is a genuine Tate algebra (`evenTEquiv`, via the
isometric `evenSupportEquiv` and the restricted Fubini), so its maximal
residues are `K`-finite by the affinoid Nullstellensatz, transported along
the constants-compatible quotient equivalence.
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver FiniteJet.GraphKoszul

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (w : ℕ → ℕ) (N k : ℕ)

/-- The `k`-th Tate extension of the even part is a Tate algebra. -/
noncomputable def evenTEquiv :
    P ↥(wpEvenSupport K w N) k ≃+* P K (k + (N + 1)) :=
  (WeightedParity.mvRestrictedCongr (evenSupportEquiv K w N)
    (norm_evenSupportEquiv K w N)).trans
    (restrictedFubini (N + 1) k).symm

section Constants

/-- The even constants. -/
noncomputable def evenConst : K →+* ↥(wpEvenSupport K w N) where
  toFun c := ⟨⟨MvPowerSeries.C c, MvPowerSeries.isRestrictedGauss_C _ _⟩,
    fun s hs => by
      show MvPowerSeries.coeff s (MvPowerSeries.C (σ := ℕ) c) = 0
      classical
      rw [MvPowerSeries.coeff_C, if_neg (by
        intro h
        subst h
        exact hs (evenHeadMem_zero w N))]⟩
  map_one' := Subtype.ext (Subtype.ext
    (map_one (MvPowerSeries.C (σ := ℕ) (R := K))))
  map_mul' x y := Subtype.ext (Subtype.ext
    (map_mul (MvPowerSeries.C (σ := ℕ)) x y))
  map_zero' := Subtype.ext (Subtype.ext
    (map_zero (MvPowerSeries.C (σ := ℕ) (R := K))))
  map_add' x y := Subtype.ext (Subtype.ext
    (map_add (MvPowerSeries.C (σ := ℕ)) x y))

/-- Constants of a restricted Tate extension (generic coefficients). -/
noncomputable def constPE {E : Type*} [NormedCommRing E]
    [IsUltrametricDist E] (k : ℕ) : E →+* P E k where
  toFun a := ⟨MvPowerSeries.C a, MvPowerSeries.isRestrictedGauss_C _ _⟩
  map_one' := Subtype.ext (map_one (MvPowerSeries.C (σ := Fin k) (R := E)))
  map_mul' x y := Subtype.ext (map_mul (MvPowerSeries.C (σ := Fin k)) x y)
  map_zero' := Subtype.ext
    (map_zero (MvPowerSeries.C (σ := Fin k) (R := E)))
  map_add' x y := Subtype.ext (map_add (MvPowerSeries.C (σ := Fin k)) x y)

theorem unhalve_zero : unhalve N 0 = 0 := by
  have h := unhalve_add (N := N) 0 0
  rw [add_zero] at h
  refine Finsupp.ext fun n => ?_
  have h2 : unhalve N 0 n = unhalve N 0 n + unhalve N 0 n := by
    conv_lhs => rw [h]
    rw [Finsupp.add_apply]
  rw [Finsupp.zero_apply]
  omega

theorem evenSupportEquiv_evenConst (c : K) :
    evenSupportEquiv K w N (evenConst w N c) = constPE (N + 1) c := by
  refine Subtype.ext (MvPowerSeries.ext fun s => ?_)
  have h1 : MvPowerSeries.coeff s
      ((evenSupportEquiv K w N (evenConst w N c))).1 =
      MvPowerSeries.coeff (unhalve N s) ((evenConst w N c)).1.1 :=
    evenToP_coeff _ _
  rw [h1]
  show MvPowerSeries.coeff (unhalve N s) (MvPowerSeries.C (σ := ℕ) c) =
    MvPowerSeries.coeff s (MvPowerSeries.C (σ := Fin (N + 1)) c)
  classical
  rw [MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  by_cases hs : s = 0
  · subst hs
    rw [if_pos (unhalve_zero N), if_pos rfl]
  · rw [if_neg (fun h => hs (unhalve_injective (N := N)
      (h.trans (unhalve_zero N).symm))), if_neg hs]

theorem mvRestrictedCongr_constPE {R S : Type*} [NormedCommRing R]
    [IsUltrametricDist R] [NormedCommRing S] [IsUltrametricDist S]
    (e : R ≃+* S) (he : ∀ x, ‖e x‖ = ‖x‖) (k : ℕ) (a : R) :
    WeightedParity.mvRestrictedCongr (σ := Fin k) e he
      (constPE k a) = constPE k (e a) := by
  refine Subtype.ext ?_
  show MvPowerSeries.map (e : R →+* S) (MvPowerSeries.C a) =
    MvPowerSeries.C (e a)
  exact MvPowerSeries.map_C _ _

theorem restrictedFubini_symm_constPE_constPE (m k : ℕ) (c : K) :
    (restrictedFubini (K := K) m k).symm (constPE k (constPE m c)) =
      constPE (k + m) c := by
  show (restrictedRenameEquiv (finSumFinEquiv (m := k) (n := m)).symm).symm
    ((restrictedSumEquiv m k).symm (constPE k (constPE m c))) = _
  have h1 : (restrictedSumEquiv (K := K) m k).symm
      (constPE k (constPE m c)) =
      ⟨MvPowerSeries.C c, MvPowerSeries.isRestrictedGauss_C _ _⟩ := by
    refine Subtype.ext ?_
    show (MvPowerSeries.sumAlgEquiv (Fin k) (Fin m) K).symm
      (MvPowerSeries.map (pValHom m) (MvPowerSeries.C (constPE m c))) =
      MvPowerSeries.C c
    rw [MvPowerSeries.map_C]
    have h2 : (pValHom (K := K) m) (constPE m c) = MvPowerSeries.C c := rfl
    rw [h2]
    refine (AlgEquiv.symm_apply_eq _).mpr ?_
    show MvPowerSeries.C (MvPowerSeries.C c) =
      MvPowerSeries.sumToIter (Fin k) (Fin m) K (MvPowerSeries.C c)
    exact (MvPowerSeries.sumToIter_C c).symm
  rw [h1]
  refine Subtype.ext ?_
  show MvPowerSeries.rename
    (⇑(finSumFinEquiv (m := k) (n := m)).symm.symm)
    (MvPowerSeries.C c) = MvPowerSeries.C c
  exact MvPowerSeries.rename_C _ c

theorem evenTEquiv_evenConst (c : K) :
    evenTEquiv w N k (constPE k (evenConst w N c)) =
      constPE (k + (N + 1)) c := by
  show (restrictedFubini (N + 1) k).symm
    (WeightedParity.mvRestrictedCongr (evenSupportEquiv K w N)
      (norm_evenSupportEquiv K w N) (constPE k (evenConst w N c))) = _
  rw [mvRestrictedCongr_constPE, evenSupportEquiv_evenConst,
    restrictedFubini_symm_constPE_constPE]

end Constants

section ResidueTransport

open scoped Valued

/-- **Maximal residues of the even Tate extension are `K`-finite** (transport
of the affinoid Nullstellensatz along `evenTEquiv`). -/
theorem module_finite_residue_evenT (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔪ₑ : Ideal (P ↥(wpEvenSupport K w N) k)) [h𝔪 : 𝔪ₑ.IsMaximal] :
    letI : Algebra K (P ↥(wpEvenSupport K w N) k ⧸ 𝔪ₑ) :=
      ((Ideal.Quotient.mk 𝔪ₑ).comp
        ((constPE k).comp (evenConst w N))).toAlgebra
    Module.Finite K (P ↥(wpEvenSupport K w N) k ⧸ 𝔪ₑ) := by
  letI : Algebra K (P ↥(wpEvenSupport K w N) k ⧸ 𝔪ₑ) :=
    ((Ideal.Quotient.mk 𝔪ₑ).comp
      ((constPE k).comp (evenConst w N))).toAlgebra
  classical
  -- push the ideal to the big Tate algebra
  set 𝔪' : Ideal (P K (k + (N + 1))) :=
    𝔪ₑ.map (((evenTEquiv w N k) :
      P ↥(wpEvenSupport K w N) k ≃+* P K (k + (N + 1))) :
      P ↥(wpEvenSupport K w N) k →+* P K (k + (N + 1))) with h𝔪'def
  haveI h𝔪'max : 𝔪'.IsMaximal := by
    rw [h𝔪'def, Ideal.map_comap_of_equiv]
    exact Ideal.comap_isMaximal_of_surjective _
      ((evenTEquiv w N k).symm.surjective)
  -- the Nullstellensatz on the big side
  letI : Algebra K (P K (k + (N + 1)) ⧸ 𝔪') :=
    (FiniteJet.GraphKoszul.constantsToResidue
      (m := k + (N + 1)) 𝔪').toAlgebra
  haveI hbig : Module.Finite K (P K (k + (N + 1)) ⧸ 𝔪') :=
    FiniteJet.GraphKoszul.module_finite_residue
      (m := k + (N + 1)) ϖ 𝔪' hK₀
  -- the quotient equivalence
  have hle : 𝔪ₑ ≤ Ideal.comap (((evenTEquiv w N k) :
      P ↥(wpEvenSupport K w N) k ≃+* P K (k + (N + 1))) :
      P ↥(wpEvenSupport K w N) k →+* P K (k + (N + 1))) 𝔪' :=
    Ideal.le_comap_map
  set e : (P ↥(wpEvenSupport K w N) k ⧸ 𝔪ₑ) →+*
      (P K (k + (N + 1)) ⧸ 𝔪') :=
    Ideal.quotientMap 𝔪' (((evenTEquiv w N k) :
      P ↥(wpEvenSupport K w N) k ≃+* P K (k + (N + 1))) :
      P ↥(wpEvenSupport K w N) k →+* P K (k + (N + 1))) hle with hedef
  have hinj : Function.Injective e := by
    rw [hedef]
    refine Ideal.quotientMap_injective' ?_
    rw [h𝔪'def]
    have hcm : Ideal.comap (((evenTEquiv w N k) :
        P ↥(wpEvenSupport K w N) k ≃+* P K (k + (N + 1))) :
        P ↥(wpEvenSupport K w N) k →+* P K (k + (N + 1)))
        (Ideal.map (((evenTEquiv w N k) :
          P ↥(wpEvenSupport K w N) k ≃+* P K (k + (N + 1))) :
          P ↥(wpEvenSupport K w N) k →+* P K (k + (N + 1))) 𝔪ₑ) = 𝔪ₑ :=
      Ideal.comap_map_of_bijective _ (evenTEquiv w N k).bijective
    rw [hcm]
  -- e is K-linear for the constants structures
  have hcomm : ∀ c : K, e (algebraMap K
      (P ↥(wpEvenSupport K w N) k ⧸ 𝔪ₑ) c) =
      algebraMap K (P K (k + (N + 1)) ⧸ 𝔪') c := by
    intro c
    show e (Ideal.Quotient.mk 𝔪ₑ (constPE k (evenConst w N c))) =
      Ideal.Quotient.mk 𝔪'
        (FiniteJet.GraphKoszul.polyToP (MvPolynomial.C c))
    rw [hedef, Ideal.quotientMap_mk]
    rw [show ((evenTEquiv w N k :
        P ↥(wpEvenSupport K w N) k ≃+* P K (k + (N + 1))) :
        P ↥(wpEvenSupport K w N) k →+* P K (k + (N + 1)))
        (constPE k (evenConst w N c)) =
      constPE (k + (N + 1)) c from evenTEquiv_evenConst w N k c]
    congr 1
    refine Subtype.ext ?_
    show MvPowerSeries.C c =
      ((MvPolynomial.C c : MvPolynomial (Fin (k + (N + 1))) K) :
        MvPowerSeries (Fin (k + (N + 1))) K)
    exact (MvPolynomial.coe_C c).symm
  -- transport the finiteness along the K-linear injection
  have hlin : ∀ (c : K) (x : P ↥(wpEvenSupport K w N) k ⧸ 𝔪ₑ),
      e (c • x) = c • e x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcomm]
  exact Module.Finite.of_injective
    ({ toFun := ⇑e,
       map_add' := fun a b => map_add e a b,
       map_smul' := fun c x => by
         rw [RingHom.id_apply]
         exact hlin c x } :
      (P ↥(wpEvenSupport K w N) k ⧸ 𝔪ₑ) →ₗ[K]
        (P K (k + (N + 1)) ⧸ 𝔪')) hinj

end ResidueTransport

end WeightedParity
