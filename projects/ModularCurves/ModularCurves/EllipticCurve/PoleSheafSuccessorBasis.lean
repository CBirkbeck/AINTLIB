/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Basis.Prod
import ModularCurves.EllipticCurve.PoleSheafSuccessorSections

/-!
# Compatible bases of successive pole-section modules

A normalized lift of the rank-one successive quotient extends any basis of the
lower pole-section module to a basis of the next pole-section module.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace ModularCurves

private def prodShear
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : M) : (M × R) ≃ₗ[R] (M × R) where
  toFun q := (q.1 + q.2 • p, q.2)
  invFun q := (q.1 - q.2 • p, q.2)
  left_inv q := by
    ext
    · simp
    · rfl
  right_inv q := by
    ext
    · simp
    · rfl
  map_add' q q' := by
    ext
    · simp only [Prod.fst_add, Prod.snd_add, add_smul]
      abel
    · rfl
  map_smul' a q := by
    ext
    · change a • q.1 + (a * q.2) • p = a • (q.1 + q.2 • p)
      rw [smul_add, smul_smul]
    · rfl

private noncomputable def appendBasisOfSplit
    {R P Q : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {n : ℕ} (b : Module.Basis (Fin n) R P) (d : Q ≃ₗ[R] P × R) (x : Q) :
    Module.Basis (Fin (n + 1)) R Q :=
  (((b.prod (Module.Basis.singleton (Fin 1) R)).map (prodShear (d x).1)).map d.symm).reindex
    finSumFinEquiv

private theorem appendBasisOfSplit_castAdd
    {R P Q : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {n : ℕ} (b : Module.Basis (Fin n) R P) (d : Q ≃ₗ[R] P × R) (x : Q)
    (i : Fin n) :
    appendBasisOfSplit b d x (Fin.castAdd 1 i) = d.symm (b i, 0) := by
  rw [appendBasisOfSplit, Module.Basis.reindex_apply,
    finSumFinEquiv_symm_apply_castAdd, Module.Basis.map_apply, Module.Basis.map_apply,
    Module.Basis.prod_apply]
  simp [prodShear]

private theorem appendBasisOfSplit_last
    {R P Q : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {n : ℕ} (b : Module.Basis (Fin n) R P) (d : Q ≃ₗ[R] P × R) (x : Q)
    (hx : (d x).2 = 1) :
    appendBasisOfSplit b d x (Fin.last n) = x := by
  rw [appendBasisOfSplit, Module.Basis.reindex_apply, finSumFinEquiv_symm_last,
    Module.Basis.map_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
  simp only [Sum.elim_inr, LinearMap.coe_inr, Function.comp_apply,
    Module.Basis.singleton_apply]
  change d.symm (0 + (1 : R) • (d x).1, 1) = x
  rw [zero_add, one_smul, ← hx]
  exact d.symm_apply_apply x

/-- A section with successor coordinate one extends a basis of the lower pole
module to a basis of the successor pole module. -/
theorem sectionPoleSheafPower_succ_baseSectionsBasisOfCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz n).sheaf 1))
    (b : Module.Basis (Fin n) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n)))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1)))
    (hx : (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
        hsm z hz U hU r hspan hnzd n).hom
      (Scheme.Modules.baseSectionsMap π
        (cokernel.π (sectionPoleSheafSuccHom π z hz n)) x) = 1) :
    ∃ b' : Module.Basis (Fin (n + 1)) Γ(S, (⊤ : S.Opens))
        (Scheme.Modules.baseSections π
          (sectionPoleSheafPower π z hz (n + 1))),
      (∀ i : Fin n,
        b' (Fin.castAdd 1 i) =
          Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz n) (b i)) ∧
        b' (Fin.last n) = x := by
  let d := sectionPoleSheafPower_succ_baseSectionsSplitEquivOfCartierGenerator
    hsm z hz U hU r hspan hnzd n hH
  have hdx : (d x).2 = 1 := by
    rw [sectionPoleSheafPower_succ_baseSectionsSplitEquiv_apply_snd]
    exact hx
  refine ⟨appendBasisOfSplit b d x, ?_, appendBasisOfSplit_last b d x hdx⟩
  intro i
  rw [appendBasisOfSplit_castAdd,
    sectionPoleSheafPower_succ_baseSectionsSplitEquiv_symm_apply_inl]

/-- In a compatible successor basis, the last basis coordinate is the canonical
coordinate on the rank-one successor quotient. -/
theorem sectionPoleSheafPower_succ_baseSectionsBasis_repr_last_of_CartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (b : Module.Basis (Fin n) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n)))
    (b' : Module.Basis (Fin (n + 1)) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz (n + 1))))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1)))
    (hb : ∀ i : Fin n,
      b' (Fin.castAdd 1 i) =
        Scheme.Modules.baseSectionsMap π
          (sectionPoleSheafSuccHom π z hz n) (b i))
    (hbx : b' (Fin.last n) = x)
    (hx : (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
        hsm z hz U hU r hspan hnzd n).hom
      (Scheme.Modules.baseSectionsMap π
        (cokernel.π (sectionPoleSheafSuccHom π z hz n)) x) = 1)
    (q : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1))) :
    b'.repr q (Fin.last n) =
      (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
        hsm z hz U hU r hspan hnzd n).hom
        (Scheme.Modules.baseSectionsMap π
          (cokernel.π (sectionPoleSheafSuccHom π z hz n)) q) := by
  let c : Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz (n + 1)) →ₗ[Γ(S, (⊤ : S.Opens))]
      Γ(S, (⊤ : S.Opens)) :=
    (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
        hsm z hz U hU r hspan hnzd n).toLinearEquiv.toLinearMap.comp
      (Scheme.Modules.baseSectionsMap π
        (cokernel.π (sectionPoleSheafSuccHom π z hz n))).hom
  have hc_old (i : Fin n) : c (b' (Fin.castAdd 1 i)) = 0 := by
    rw [hb i]
    change (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
        hsm z hz U hU r hspan hnzd n).hom
      (Scheme.Modules.baseSectionsMap π
        (cokernel.π (sectionPoleSheafSuccHom π z hz n))
        (Scheme.Modules.baseSectionsMap π
          (sectionPoleSheafSuccHom π z hz n) (b i))) = 0
    rw [(sectionPoleSheafPower_baseSectionsSucc_exact hsm z hz n).apply_apply_eq_zero]
    exact map_zero _
  have hcoord : b'.coord (Fin.last n) = c := by
    apply b'.ext
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl, hbx]
      exact hx.symm
    · change b'.coord (Fin.last n) (b' (Fin.castAdd 1 i)) =
        c (b' (Fin.castAdd 1 i))
      have hne : Fin.castAdd 1 i ≠ Fin.last n := Fin.castSucc_ne_last i
      rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg hne, hc_old]
  rw [← Module.Basis.coord_apply]
  exact LinearMap.congr_fun hcoord q

/-- Normalized pole-order-two and pole-order-three sections successively extend
a basis of the first pole module to compatible bases of the next two modules. -/
theorem sectionPoleSheafPower_two_three_baseSectionsBasesOfCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hH1 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (hH2 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 2).sheaf 1))
    (b1 : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 1)))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
        hsm z hz U hU r hspan hnzd 1).hom
      (Scheme.Modules.baseSectionsMap π
        (cokernel.π (sectionPoleSheafSuccHom π z hz 1)) x) = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
        hsm z hz U hU r hspan hnzd 2).hom
      (Scheme.Modules.baseSectionsMap π
        (cokernel.π (sectionPoleSheafSuccHom π z hz 2)) y) = 1) :
    ∃ b2 : Module.Basis (Fin 2) Γ(S, (⊤ : S.Opens))
        (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 2)),
      (∀ i : Fin 1,
        b2 (Fin.castAdd 1 i) =
          Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 1) (b1 i)) ∧
        b2 (Fin.last 1) = x ∧
          ∃ b3 : Module.Basis (Fin 3) Γ(S, (⊤ : S.Opens))
              (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 3)),
            (∀ i : Fin 2,
              b3 (Fin.castAdd 1 i) =
                Scheme.Modules.baseSectionsMap π
                  (sectionPoleSheafSuccHom π z hz 2) (b2 i)) ∧
              b3 (Fin.last 2) = y := by
  obtain ⟨b2, hb2, hb2x⟩ :=
    sectionPoleSheafPower_succ_baseSectionsBasisOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 hH1 b1 x hx
  obtain ⟨b3, hb3, hb3y⟩ :=
    sectionPoleSheafPower_succ_baseSectionsBasisOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 hH2 b2 y hy
  exact ⟨b2, hb2, hb2x, b3, hb3, hb3y⟩

end ModularCurves
