/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.Modularforms.DimensionFormulas
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.NumberTheory.MulChar.Duality

/-!
# Character decomposition of `ModularForm (Γ₁(N)) k`

For each character `χ : (ZMod N)ˣ →* ℂˣ`, the Nebentypus character space

  `modFormCharSpace k χ = ⨅ d : (ZMod N)ˣ, eigenspace (diamondOpHom k d) (χ d)`

and its cusp-form analogue `cuspFormCharSpace k χ` are already defined in
`Gamma1Pair.lean`. This file proves the internal direct sum decomposition

  `ModularForm (Γ₁(N)) k = ⨁_{χ : (ZMod N)ˣ →* ℂˣ} modFormCharSpace k χ`

together with its cusp-form analogues and the refinement to diamond-invariant
submodules.

## Main results

* `ModularForm_Gamma1_iSup_charSpace`: `⨆ χ, modFormCharSpace k χ = ⊤`.
* `ModularForm_Gamma1_iSupIndep_charSpace`, `CuspForm_Gamma1_iSupIndep_charSpace`:
  the families are supremum-independent.
* `ModularForm_Gamma1_charSpace_directSum`: the `DirectSum.IsInternal` statement.
* `modFormCharSpace_iSup_inf_of_diamondOpHom_invariant`,
  `cuspFormCharSpace_iSup_inf_of_diamondOpCuspHom_invariant`: any diamond-invariant
  submodule is the supremum of its intersections with the character spaces, with
  finsupp-indexed corollaries `exists_finsupp_charSpace_of_diamondOp(Cusp)Hom_invariant`.
* `ModularForm_Gamma1_endo_ext`: two endomorphisms agreeing on every character space
  are equal — the gluing principle for extending Hecke-operator identities proven
  per character space to the whole space.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Polynomial

open scoped MatrixGroups DirectSum

namespace HeckeRing.GL2

noncomputable section

section Abstract

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

/-- If `v ≠ 0` is a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` with eigenvalues `χ g`, then the eigenvalue at the
identity is `1`. -/
lemma charDecomp_char_one_of_jointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) : χ 1 = 1 := by
  have h1 := hv_mem 1
  rw [Module.End.mem_eigenspace_iff, map_one, Module.End.one_apply] at h1
  exact (smul_left_inj hv).mp (by rw [← h1, one_smul])

/-- If `v ≠ 0` is a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` with eigenvalues `χ g`, then the eigenvalues are
multiplicative: `χ (g₁ * g₂) = χ g₁ * χ g₂`. -/
lemma charDecomp_char_mul_of_jointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g₁ g₂ : G) :
    χ (g₁ * g₂) = χ g₁ * χ g₂ := by
  have h := hv_mem (g₁ * g₂)
  rw [Module.End.mem_eigenspace_iff, map_mul] at h
  refine (smul_left_inj hv).mp ?_
  rw [← h, Module.End.mul_apply, Module.End.mem_eigenspace_iff.mp (hv_mem g₂), map_smul,
    Module.End.mem_eigenspace_iff.mp (hv_mem g₁), smul_smul, mul_comm (χ g₂) (χ g₁)]

/-- If `g` has finite order and `v ≠ 0` is a joint eigenvector with eigenvalues
`χ`, then `χ g ≠ 0`: the eigenvalue of a finite-order element is a root of
unity (hence a unit). -/
lemma charDecomp_char_ne_zero_of_jointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) {g : G} (hg : IsOfFinOrder g) :
    χ g ≠ 0 := by
  obtain ⟨n, hnpos, hn⟩ := hg.exists_pow_eq_one
  intro hzero
  have hχ_pow : χ (g ^ n) = χ g ^ n :=
    map_pow (⟨⟨χ, charDecomp_char_one_of_jointEigenvector ρ χ v hv hv_mem⟩,
      charDecomp_char_mul_of_jointEigenvector ρ χ v hv hv_mem⟩ : G →* K) g n
  rw [hn, charDecomp_char_one_of_jointEigenvector ρ χ v hv hv_mem, hzero,
    zero_pow hnpos.ne'] at hχ_pow
  exact one_ne_zero hχ_pow

/-- Given a joint eigenvector `v ≠ 0` for a monoid-hom representation
`ρ : G →* Module.End K V` of a *finite* group `G`, the eigenvalue function
`χ : G → K` factors through a unique monoid homomorphism `G →* Kˣ`. -/
def charDecomp_charHomOfEigenvector [Finite G] (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) : G →* Kˣ where
  toFun g := Units.mk0 (χ g)
    (charDecomp_char_ne_zero_of_jointEigenvector ρ χ v hv hv_mem (isOfFinOrder_of_finite g))
  map_one' := Units.ext (charDecomp_char_one_of_jointEigenvector ρ χ v hv hv_mem)
  map_mul' g₁ g₂ := Units.ext (charDecomp_char_mul_of_jointEigenvector ρ χ v hv hv_mem g₁ g₂)

@[simp]
lemma charDecomp_charHomOfEigenvector_val [Finite G] (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g : G) :
    ((charDecomp_charHomOfEigenvector ρ χ v hv hv_mem g) : K) = χ g := rfl

private lemma exists_charHom_of_iInf_eigenspace_ne_bot [Finite G] {ρ : G →* Module.End K V}
    {χ : G → K} (hχ : ⨅ g, (ρ g).eigenspace (χ g) ≠ ⊥) :
    ∃ χ₀ : G →* Kˣ, (fun g ↦ ((χ₀ g) : K)) = χ := by
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hχ
  exact ⟨charDecomp_charHomOfEigenvector ρ χ v hv_ne
    fun g ↦ (Submodule.mem_iInf _).mp hv_mem g, rfl⟩

/-- A finite-order endomorphism of a vector space over a characteristic-zero field is
semisimple. -/
lemma charDecomp_isSemisimple_of_isOfFinOrder [CharZero K] {f : Module.End K V}
    (hf : IsOfFinOrder f) : f.IsSemisimple := by
  obtain ⟨n, hnpos, hn⟩ := hf.exists_pow_eq_one
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (X_pow_sub_one_separable_iff.mpr <| Nat.cast_ne_zero.mpr hnpos.ne').squarefree
    (by simp [map_sub, aeval_X_pow, hn])

private lemma iSupIndep_iInf_eigenspace_of_isSemisimple {ι : Type*} (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hss : ∀ i, (f i).IsSemisimple) :
    iSupIndep fun χ : ι → K ↦ ⨅ i, (f i).eigenspace (χ i) := by
  have heq (i : ι) (μ : K) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have h_mapsTo (i j : ι) (φ : K) : Set.MapsTo (f i) ((f j).maxGenEigenspace φ : Set V)
      ((f j).maxGenEigenspace φ : Set V) := by
    refine Module.End.mapsTo_maxGenEigenspace_of_comm ?_ φ
    rcases eq_or_ne j i with rfl | hij
    · exact Commute.refl _
    · exact hcomm hij
  simpa only [heq] using Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f h_mapsTo

private lemma iSup_iInf_eigenspace_eq_top_of_isSemisimple [IsAlgClosed K] [FiniteDimensional K V]
    {ι : Type*} (f : ι → Module.End K V) (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hss : ∀ i, (f i).IsSemisimple) : (⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i)) = ⊤ := by
  have heq (i : ι) (μ : K) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  simpa only [heq] using
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      hcomm fun i ↦ by simpa only [heq] using (hss i).iSup_eigenspace_eq_top

private lemma iSup_inf_iInf_eigenspace_eq_self_of_invariant {ι : Type*} [FiniteDimensional K V]
    (f : ι → Module.End K V) (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hss : ∀ i, (f i).IsSemisimple) (htop : ∀ i, ⨆ μ : K, (f i).eigenspace μ = ⊤)
    (p : Submodule K V) (hp : ∀ i, ∀ x ∈ p, f i x ∈ p) :
    (⨆ χ : ι → K, p ⊓ ⨅ i, (f i).eigenspace (χ i)) = p := by
  have hmax (i : ι) (μ : K) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  simp_rw [← hmax,
    fun χ : ι → K ↦ Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo
      (f := f) (μ := χ) p (fun i ↦ hp i),
    ← Submodule.map_iSup]
  suffices h_restrict_top :
      (⨆ χ : ι → K, ⨅ i,
        Module.End.maxGenEigenspace ((f i).restrict (hp i)) (χ i)) = ⊤ by
    rw [h_restrict_top, Submodule.map_top, Submodule.range_subtype]
  apply Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
  · intro i j hij
    refine LinearMap.ext fun ⟨x, _⟩ ↦ Subtype.ext ?_
    simpa only [Module.End.mul_apply, LinearMap.coe_restrict_apply] using
      LinearMap.congr_fun (hcomm hij).eq x
  · refine fun i ↦ Module.End.genEigenspace_restrict_eq_top (hp i) ?_
    simpa only [hmax] using htop i

end Abstract

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- Each diamond operator has finite order. -/
lemma diamondOpHom_isOfFinOrder (d : (ZMod N)ˣ) : IsOfFinOrder (diamondOpHom k d) :=
  (diamondOpHom k).isOfFinOrder (isOfFinOrder_of_finite d)

/-- Each diamond operator is a semisimple endomorphism. -/
lemma diamondOp_isSemisimple (d : (ZMod N)ˣ) : (diamondOpHom k d).IsSemisimple :=
  charDecomp_isSemisimple_of_isOfFinOrder (diamondOpHom_isOfFinOrder d)

/-- The diamond operators pairwise commute. -/
lemma diamondOpHom_pairwise_commute :
    Pairwise fun d₁ d₂ : (ZMod N)ˣ ↦ Commute (diamondOpHom k d₁) (diamondOpHom k d₂) :=
  fun _ _ _ ↦ (Commute.all _ _).map (diamondOpHom k)

/-- Finite-dimensionality of the space of modular forms for `Γ₁(N)`. -/
instance modularForm_Gamma1_finiteDimensional :
    FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  dim_gen_cong_levels k (Gamma1 N) Subgroup.FiniteIndex.index_ne_zero

/-- Finite-dimensionality of the space of modular forms for `Γ₀(N)`. -/
instance modularForm_Gamma0_finiteDimensional :
    FiniteDimensional ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  dim_gen_cong_levels k (Gamma0 N) Subgroup.FiniteIndex.index_ne_zero

/-- For each diamond operator, the supremum of its eigenspaces is the whole
space. -/
lemma diamondOp_iSup_eigenspace_eq_top (d : (ZMod N)ˣ) : ⨆ μ : ℂ, (diamondOpHom k d).eigenspace μ =
    (⊤ : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) :=
  (diamondOp_isSemisimple d).iSup_eigenspace_eq_top

/-- The joint eigenspace indexed by a function `χ : (ZMod N)ˣ → ℂ`. When `χ` is
not the underlying function of a character `(ZMod N)ˣ →* ℂˣ`, this space is
`⊥`; otherwise it coincides with `modFormCharSpace k χ₀` for that character. -/
def jointDiamondEigenspace (k : ℤ) (χ : (ZMod N)ˣ → ℂ) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, (diamondOpHom k d).eigenspace (χ d)

/-- `jointDiamondEigenspace` at the underlying function of a character agrees
with `modFormCharSpace`. -/
lemma jointDiamondEigenspace_eq_modFormCharSpace (χ₀ : (ZMod N)ˣ →* ℂˣ) :
    jointDiamondEigenspace k (fun d ↦ (χ₀ d : ℂ)) = modFormCharSpace k χ₀ := rfl

/-- If `jointDiamondEigenspace k χ ≠ ⊥`, then `χ` comes from a character, i.e.,
equals `(d ↦ (χ₀ d : ℂ))` for some `χ₀ : (ZMod N)ˣ →* ℂˣ`. -/
lemma exists_charHom_of_jointDiamondEigenspace_ne_bot {χ : (ZMod N)ˣ → ℂ}
    (hχ : jointDiamondEigenspace k χ ≠ ⊥) : ∃ χ₀ : (ZMod N)ˣ →* ℂˣ, (fun d ↦ ((χ₀ d) : ℂ)) = χ :=
  exists_charHom_of_iInf_eigenspace_ne_bot (ρ := diamondOpHom k) hχ

/-- **The character subspaces `modFormCharSpace k χ` span the whole space**:
modular forms for `Γ₁(N)` decompose into the span of Nebentypus character
spaces, one for each character `(ZMod N)ˣ →* ℂˣ`. -/
theorem ModularForm_Gamma1_iSup_charSpace (k : ℤ) : (⨆ χ : (ZMod N)ˣ →* ℂˣ, modFormCharSpace k χ) =
    (⊤ : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  have h_top_fun : (⨆ χ : (ZMod N)ˣ → ℂ, jointDiamondEigenspace k χ) = ⊤ :=
    iSup_iInf_eigenspace_eq_top_of_isSemisimple (diamondOpHom k) diamondOpHom_pairwise_commute
      diamondOp_isSemisimple
  refine le_antisymm le_top (h_top_fun ▸ iSup_le fun χ ↦ ?_)
  by_cases hχ : jointDiamondEigenspace k χ = ⊥
  · simp [hχ]
  · obtain ⟨χ₀, rfl⟩ := exists_charHom_of_jointDiamondEigenspace_ne_bot hχ
    rw [jointDiamondEigenspace_eq_modFormCharSpace]
    exact le_iSup _ χ₀

/-- **The character subspaces form an independent family.** -/
theorem ModularForm_Gamma1_iSupIndep_charSpace (k : ℤ) :
    iSupIndep (fun χ : (ZMod N)ˣ →* ℂˣ ↦ modFormCharSpace k χ) := by
  have h_indep_fun : iSupIndep (fun χ : (ZMod N)ˣ → ℂ ↦ jointDiamondEigenspace k χ) :=
    iSupIndep_iInf_eigenspace_of_isSemisimple (diamondOpHom k) diamondOpHom_pairwise_commute
      diamondOp_isSemisimple
  exact h_indep_fun.comp fun _ _ h ↦ MonoidHom.ext fun d ↦ Units.ext (congr_fun h d)

/-- **Internal direct sum decomposition**: `ModularForm (Γ₁(N)) k` decomposes
as the direct sum of the Nebentypus character spaces `modFormCharSpace k χ`. -/
theorem ModularForm_Gamma1_charSpace_directSum (k : ℤ) [DecidableEq ((ZMod N)ˣ →* ℂˣ)] :
    DirectSum.IsInternal (fun χ : (ZMod N)ˣ →* ℂˣ ↦ modFormCharSpace k χ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (ModularForm_Gamma1_iSupIndep_charSpace k) (ModularForm_Gamma1_iSup_charSpace k)

/-- Each character subspace `modFormCharSpace k χ` is finite-dimensional over
`ℂ`, as a submodule of the finite-dimensional ambient
`ModularForm ((Gamma1 N).map (mapGL ℝ)) k`. -/
instance modFormCharSpace_finiteDimensional (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    FiniteDimensional ℂ (modFormCharSpace k χ) := inferInstance

/-- The character group `(ZMod N)ˣ →* ℂˣ` is finite. -/
instance finite_charHom : Finite ((ZMod N)ˣ →* ℂˣ) :=
  .of_equiv (MulChar (ZMod N) ℂ) MulChar.equivToUnitHom

/-- `Fintype` version of `finite_charHom`, needed to state sums over the
character group at the statement level (`∑ χ : …`). -/
instance fintype_charHom : Fintype ((ZMod N)ˣ →* ℂˣ) :=
  Fintype.ofFinite _

private def cuspFormToModularFormLin_local : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm := f.toSlashInvariantForm
      holo' := f.holo'
      bdd_at_cusps' := fun hc g hg ↦
        (f.zero_at_cusps' hc g hg).boundedAtFilter }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero N] in
private lemma cuspFormToModularFormLin_local_injective :
    Function.Injective (cuspFormToModularFormLin_local (N := N) (k := k)) :=
  fun _ _ hfg ↦ DFunLike.ext' (congr_arg (⇑) hfg)

/-- Finite-dimensionality of `CuspForm Γ₁(N) k`. -/
instance cuspForm_Gamma1_finiteDimensional :
    FiniteDimensional ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  FiniteDimensional.of_injective (cuspFormToModularFormLin_local (N := N) (k := k))
    cuspFormToModularFormLin_local_injective

/-- Each cusp-form diamond operator has finite order. -/
lemma diamondOpCuspHom_isOfFinOrder (d : (ZMod N)ˣ) : IsOfFinOrder (diamondOpCuspHom k d) :=
  (diamondOpCuspHom k).isOfFinOrder (isOfFinOrder_of_finite d)

/-- Each cusp-form diamond operator is semisimple. -/
lemma diamondOpCusp_isSemisimple (d : (ZMod N)ˣ) : (diamondOpCuspHom k d).IsSemisimple :=
  charDecomp_isSemisimple_of_isOfFinOrder (diamondOpCuspHom_isOfFinOrder d)

/-- The cusp-form diamond operators pairwise commute. -/
lemma diamondOpCuspHom_pairwise_commute :
    Pairwise fun d₁ d₂ : (ZMod N)ˣ ↦ Commute (diamondOpCuspHom k d₁) (diamondOpCuspHom k d₂) :=
  fun _ _ _ ↦ (Commute.all _ _).map (diamondOpCuspHom k)

/-- For each cusp-form diamond operator, the supremum of its eigenspaces is
the whole space. -/
lemma diamondOpCusp_iSup_eigenspace_eq_top (d : (ZMod N)ˣ) :
    ⨆ μ : ℂ, (diamondOpCuspHom k d).eigenspace μ =
    (⊤ : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) :=
  (diamondOpCusp_isSemisimple d).iSup_eigenspace_eq_top

/-- The joint cusp-form eigenspace indexed by an arbitrary function
`χ : (ZMod N)ˣ → ℂ`.  For characters this coincides with
`cuspFormCharSpace`; for non-characters it is `⊥`. -/
def jointDiamondCuspEigenspace (k : ℤ) (χ : (ZMod N)ˣ → ℂ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, (diamondOpCuspHom k d).eigenspace (χ d)

/-- `jointDiamondCuspEigenspace` at the underlying function of a character
agrees with `cuspFormCharSpace`. -/
lemma jointDiamondCuspEigenspace_eq_cuspFormCharSpace (χ₀ : (ZMod N)ˣ →* ℂˣ) :
    jointDiamondCuspEigenspace k (fun d ↦ (χ₀ d : ℂ)) = cuspFormCharSpace k χ₀ := rfl

/-- If `jointDiamondCuspEigenspace k χ ≠ ⊥`, then `χ` comes from a character. -/
lemma exists_charHom_of_jointDiamondCuspEigenspace_ne_bot {χ : (ZMod N)ˣ → ℂ}
    (hχ : jointDiamondCuspEigenspace k χ ≠ ⊥) :
    ∃ χ₀ : (ZMod N)ˣ →* ℂˣ, (fun d ↦ ((χ₀ d) : ℂ)) = χ :=
  exists_charHom_of_iInf_eigenspace_ne_bot (ρ := diamondOpCuspHom k) hχ

/-- **The cusp-form character subspaces form an independent family.** -/
theorem CuspForm_Gamma1_iSupIndep_charSpace (k : ℤ) :
    iSupIndep (fun χ : (ZMod N)ˣ →* ℂˣ ↦ cuspFormCharSpace k χ) := by
  have h_indep_fun : iSupIndep (fun χ : (ZMod N)ˣ → ℂ ↦ jointDiamondCuspEigenspace k χ) :=
    iSupIndep_iInf_eigenspace_of_isSemisimple (diamondOpCuspHom k)
      diamondOpCuspHom_pairwise_commute diamondOpCusp_isSemisimple
  exact h_indep_fun.comp fun _ _ h ↦ MonoidHom.ext fun d ↦ Units.ext (congr_fun h d)

/-- Each cusp-form character subspace `cuspFormCharSpace k χ` is
finite-dimensional over `ℂ`, as a submodule of the finite-dimensional
`CuspForm ((Gamma1 N).map (mapGL ℝ)) k`. -/
instance cuspFormCharSpace_finiteDimensional (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    FiniteDimensional ℂ (cuspFormCharSpace k χ) := inferInstance

section InvariantSubmoduleCharDecomp

/-- **Character decomposition of a diamond-invariant submodule of
`ModularForm (Γ₁(N)) k`.**  If `p ⊆ M_k(Γ₁(N))` is stable under every
diamond operator `⟨d⟩` for `d ∈ (ZMod N)ˣ`, then `p` equals the supremum
of its intersections with the Nebentypus character subspaces
`modFormCharSpace k χ`.  Specialising `p = ⊤` recovers
`ModularForm_Gamma1_iSup_charSpace`. -/
theorem modFormCharSpace_iSup_inf_of_diamondOpHom_invariant
    (k : ℤ) (p : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpHom k d f ∈ p) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, p ⊓ modFormCharSpace k χ) = p := by
  have h_fun_top : (⨆ χ : (ZMod N)ˣ → ℂ, p ⊓ jointDiamondEigenspace k χ) = p :=
    iSup_inf_iInf_eigenspace_eq_self_of_invariant (diamondOpHom k) diamondOpHom_pairwise_commute
      diamondOp_isSemisimple diamondOp_iSup_eigenspace_eq_top p hp
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) ?_
  conv_lhs => rw [← h_fun_top]
  refine iSup_le fun χ ↦ ?_
  by_cases hχ : p ⊓ jointDiamondEigenspace k χ = ⊥
  · simp [hχ]
  · obtain ⟨χ₀, rfl⟩ := exists_charHom_of_jointDiamondEigenspace_ne_bot
      (fun h_bot ↦ hχ (by rw [h_bot, inf_bot_eq]))
    rw [jointDiamondEigenspace_eq_modFormCharSpace]
    exact le_iSup (fun ψ : (ZMod N)ˣ →* ℂˣ ↦ p ⊓ modFormCharSpace k ψ) χ₀

/-- **Character decomposition of a diamond-invariant submodule of
`CuspForm (Γ₁(N)) k`.**  The cusp-form analogue of
`modFormCharSpace_iSup_inf_of_diamondOpHom_invariant`. -/
theorem cuspFormCharSpace_iSup_inf_of_diamondOpCuspHom_invariant
    (k : ℤ) (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpCuspHom k d f ∈ p) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, p ⊓ cuspFormCharSpace k χ) = p := by
  have h_fun_top : (⨆ χ : (ZMod N)ˣ → ℂ, p ⊓ jointDiamondCuspEigenspace k χ) = p :=
    iSup_inf_iInf_eigenspace_eq_self_of_invariant (diamondOpCuspHom k)
      diamondOpCuspHom_pairwise_commute diamondOpCusp_isSemisimple
      diamondOpCusp_iSup_eigenspace_eq_top p hp
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) ?_
  conv_lhs => rw [← h_fun_top]
  refine iSup_le fun χ ↦ ?_
  by_cases hχ : p ⊓ jointDiamondCuspEigenspace k χ = ⊥
  · simp [hχ]
  · obtain ⟨χ₀, rfl⟩ := exists_charHom_of_jointDiamondCuspEigenspace_ne_bot
      (fun h_bot ↦ hχ (by rw [h_bot, inf_bot_eq]))
    rw [jointDiamondCuspEigenspace_eq_cuspFormCharSpace]
    exact le_iSup (fun ψ : (ZMod N)ˣ →* ℂˣ ↦ p ⊓ cuspFormCharSpace k ψ) χ₀

/-- **Finsupp-indexed character decomposition of a modular form in a
diamond-invariant submodule.**  Consumer-facing corollary of
`modFormCharSpace_iSup_inf_of_diamondOpHom_invariant`: any element of a
diamond-invariant submodule `p ⊆ M_k(Γ₁(N))` is a finitely-supported sum
of Nebentypus-character components, each landing simultaneously in `p`
and in its character subspace. -/
theorem exists_finsupp_charSpace_of_diamondOpHom_invariant
    (k : ℤ) (p : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpHom k d f ∈ p)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ p) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ ModularForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ p ⊓ modFormCharSpace k χ) ∧ (g.sum fun _ y ↦ y) = f :=
  (Submodule.mem_iSup_iff_exists_finsupp _ _).mp <|
    (modFormCharSpace_iSup_inf_of_diamondOpHom_invariant k p hp).symm ▸ hf

/-- **Finsupp-indexed character decomposition of a cusp form in a
diamond-invariant submodule.**  Cusp-form analogue of
`exists_finsupp_charSpace_of_diamondOpHom_invariant`. -/
theorem exists_finsupp_charSpace_of_diamondOpCuspHom_invariant
    (k : ℤ) (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpCuspHom k d f ∈ p)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ p) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ p ⊓ cuspFormCharSpace k χ) ∧ (g.sum fun _ y ↦ y) = f :=
  (Submodule.mem_iSup_iff_exists_finsupp _ _).mp <|
    (cuspFormCharSpace_iSup_inf_of_diamondOpCuspHom_invariant k p hp).symm ▸ hf

end InvariantSubmoduleCharDecomp

section EndoExt

variable {N : ℕ} [NeZero N]

/-- **Extensionality along the character decomposition**: two `ℂ`-linear endomorphisms of
`ModularForm (Γ₁(N)) k` that agree on every Nebentypus subspace `modFormCharSpace k χ`
are equal.  This is the gluing principle by which identities of Hecke operators proven
per character space (e.g. transported from the commutative ring `𝕋(Γ₀(N))` along
`heckeRingHomCharSpace`) extend to the whole space of modular forms. -/
theorem ModularForm_Gamma1_endo_ext {k : ℤ}
    {S T : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (h : ∀ (χ : (ZMod N)ˣ →* ℂˣ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      f ∈ modFormCharSpace k χ → S f = T f) : S = T := by
  refine LinearMap.ext fun f ↦ ?_
  have hf : f ∈ ⨆ χ : (ZMod N)ˣ →* ℂˣ, modFormCharSpace k χ :=
    ModularForm_Gamma1_iSup_charSpace (N := N) k ▸ Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := fun g ↦ S g = T g) hf h (by simp)
    fun x y hx hy ↦ by simp [hx, hy]

end EndoExt

end

end HeckeRing.GL2
