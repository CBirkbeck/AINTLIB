/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.Basic
import LeanModularForms.HeckeRIngs.GLn.SL2Surjection
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Hecke Pair for Γ₁(N)

Defines the submonoid `Δ₁(N)` and the Hecke pair `(Γ₁(N), Δ₁(N))` for the congruence
subgroup `Γ₁(N)`, together with the diamond operators `⟨d⟩` on modular and cusp forms
for `Γ₁(N)` and the associated Nebentypus character spaces.

## Main definitions

* `Delta1_submonoid` — `Δ₁(N)`: integer 2×2 matrices with `a ≡ 1 (mod N)`,
  `c ≡ 0 (mod N)`, and positive determinant.
* `Gamma1_pair` — the Hecke pair `(Γ₁(N), Δ₁(N))`.
* `diamondOpHom`/`diamondOpCuspHom` — the diamond operators `⟨d⟩` for `d : (ZMod N)ˣ`,
  as monoid homomorphisms into the endomorphisms of `M_k(Γ₁(N))` resp. `S_k(Γ₁(N))`.
* `modFormCharSpace`/`cuspFormCharSpace` — the Nebentypus character spaces
  `M_k(Γ₁(N), χ)` and `S_k(Γ₁(N), χ)`, cut out as diamond eigenspaces.

## Main results

* `Gamma1_le_Delta1` — `Γ₁(N) ≤ Δ₁(N)` as submonoids.
* `Delta1_le_commensurator` — `Δ₁(N) ≤ commensurator(Γ₁(N))`.
* `Gamma0_normalizes_Gamma1` — conjugation by `Γ₀(N)` preserves `Γ₁(N)`.
* `modFormCharSpace_iff_nebentypus`/`cuspFormCharSpace_iff_nebentypus` — membership in
  the character space is the classical Nebentypus relation `f ∣[k] g = χ(d(g)) • f`
  for all `g ∈ Γ₀(N)`.

## References

* Miyake, *Modular Forms*, §4.5
* Diamond–Shurman, *A First Course in Modular Forms*, §5.1
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups ModularForm

namespace HeckeRing.GL2

/-- `Δ₁(N)`: integer 2×2 matrices with `a ≡ 1 (mod N)`, `c ≡ 0 (mod N)`,
and positive determinant. This pairs with `Γ₁(N)` to form a Hecke pair. -/
noncomputable def Delta1_submonoid (N : ℕ) : Submonoid (GL (Fin 2) ℚ) where
  carrier := {g | HasIntEntries 2 g ∧ 0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ, (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
      (N : ℤ) ∣ A 1 0 ∧ (A 0 0 : ZMod N) = 1}
  one_mem' := ⟨hasIntEntries_one 2, by simp, 1, by simp, by simp, by simp⟩
  mul_mem' := by
    intro a b ⟨ha, hda, A, hA, hAN, hAone⟩ ⟨hb, hdb, B, hB, hBN, hBone⟩
    refine ⟨ha.mul _ hb, by simpa [det_mul] using mul_pos hda hdb, A * B, ?_, ?_, ?_⟩
    · ext i j
      simp [hA, hB, mul_apply, map_apply]
    · simp only [mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hAN _) (dvd_mul_of_dvd_right hBN _)
    · simp [mul_apply, Fin.sum_univ_two, hAone, hBone,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hBN]

/-- `Γ₁(N) ≤ Δ₁(N)`: the congruence subgroup embeds into the submonoid. -/
lemma Gamma1_le_Delta1 (N : ℕ) [NeZero N] :
    ((Gamma1 N).map (mapGL ℚ)).toSubmonoid ≤ Delta1_submonoid N := by
  intro g hg
  obtain ⟨σ, hσ_mem, rfl⟩ := hg
  obtain ⟨ha, -, hc⟩ := (Gamma1_mem _ _).mp hσ_mem
  refine ⟨SLnZ_subgroup_hasIntEntries 2 ⟨σ, rfl⟩, ?_, (σ : Matrix (Fin 2) (Fin 2) ℤ), rfl,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc, ha⟩
  rw [mapGL_coe_matrix, (SpecialLinearGroup.map (algebraMap ℤ ℚ) σ).prop]
  exact one_pos

private lemma Delta1_le_posDetInt (N : ℕ) : Delta1_submonoid N ≤ posDetInt_submonoid 2 :=
  fun _ ⟨hint, hdet, _⟩ ↦ ⟨hint, hdet⟩

private lemma Gamma1_map_commensurable_SLnZ (N : ℕ) [NeZero N] :
    Subgroup.Commensurable ((Gamma1 N).map (mapGL ℚ))
      (Subgroup.map (mapGL ℚ : SpecialLinearGroup (Fin 2) ℤ →* GL (Fin 2) ℚ) ⊤) := by
  constructor
  · rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  · rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_left]
    exact one_ne_zero

/-- `Δ₁(N) ≤ commensurator(Γ₁(N))`. The proof chains:
`Δ₁(N) ≤ posDetInt ≤ commensurator(SL₂(ℤ)) = commensurator(Γ₁(N))`,
where the last equality holds because `Γ₁(N)` has finite index in `SL₂(ℤ)`. -/
lemma Delta1_le_commensurator (N : ℕ) [NeZero N] :
    Delta1_submonoid N ≤ (commensurator ((Gamma1 N).map (mapGL ℚ))).toSubmonoid := by
  rw [Subgroup.Commensurable.eq (Gamma1_map_commensurable_SLnZ N), ← MonoidHom.range_eq_map]
  exact (Delta1_le_posDetInt N).trans (posDetInt_le_commensurator 2)

/-- **The Hecke pair `(Γ₁(N), Δ₁(N))`** for level N.
This is the foundation for Hecke operators on `M_k(Γ₁(N))`. -/
noncomputable def Gamma1_pair (N : ℕ) [NeZero N] : HeckeRing.HeckePair (GL (Fin 2) ℚ) where
  H := (Gamma1 N).map (mapGL ℚ)
  Δ := Delta1_submonoid N
  h₀ := Gamma1_le_Delta1 N
  h₁ := Delta1_le_commensurator N

/-- The slash-action conjugation `σ` is the identity for matrices coming from
`SL₂(ℤ)`: their determinant is `1 > 0`, so the `σ` branch picks `ContinuousAlgEquiv.refl ℝ ℂ`. -/
@[simp]
lemma σ_mapGL_real_eq_refl (s : SL(2, ℤ)) :
    UpperHalfPlane.σ (mapGL ℝ s) = ContinuousAlgEquiv.refl ℝ ℂ := by
  simp [UpperHalfPlane.σ, SpecialLinearGroup.mapGL]

/-- Conjugation by a `Gamma0(N)` element preserves `Gamma1(N)`.
This is the foundation for the diamond operator `⟨d⟩` on modular forms. -/
theorem Gamma0_normalizes_Gamma1 (g : ↥(Gamma0 N)) (h : SL(2, ℤ)) (hh : h ∈ Gamma1 N) :
    (g : SL(2, ℤ)) * h * (g : SL(2, ℤ))⁻¹ ∈ Gamma1 N :=
  (Gamma1_mem _ _).mpr <| (Gamma1_to_Gamma0_mem _).mp <|
    (Gamma0Map N).normal_ker.conj_mem ⟨h, Gamma1_in_Gamma0 N hh⟩
      ((Gamma1_to_Gamma0_mem _).mpr ((Gamma1_mem _ _).mp hh)) g

/-- `Gamma1(N).map(mapGL ℝ)` is invariant under conjugation by `Gamma0(N)` elements
in `GL₂(ℝ)`. -/
theorem Gamma1_map_conjAct_eq (g : ↥(Gamma0 N)) :
    ConjAct.toConjAct (mapGL ℝ (g : SL(2, ℤ)))⁻¹ •
    (Gamma1 N).map (mapGL ℝ) = (Gamma1 N).map (mapGL ℝ) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, hσy⟩
    have hmem : (g : SL(2, ℤ))⁻¹ * σ * (g : SL(2, ℤ)) ∈ Gamma1 N := by
      simpa [inv_inv] using Gamma0_normalizes_Gamma1
        ⟨(g : SL(2, ℤ))⁻¹, (Gamma0 N).inv_mem g.property⟩ σ hσ
    exact ⟨_, hmem, by
      simp only [map_mul, map_inv, hσy]
      group⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨(g : SL(2, ℤ)) * σ * (g : SL(2, ℤ))⁻¹,
      Gamma0_normalizes_Gamma1 g σ hσ, by simp [map_mul, map_inv]⟩

/-- Forward variant of `Gamma1_map_conjAct_eq`: `Gamma1(N).map(mapGL ℝ)` is invariant
under conjugation by `mapGL ℝ g` (rather than its inverse). -/
theorem Gamma1_map_conjAct_eq_forward (g : ↥(Gamma0 N)) :
    ConjAct.toConjAct (mapGL ℝ (g : SL(2, ℤ))) •
    (Gamma1 N).map (mapGL ℝ) = (Gamma1 N).map (mapGL ℝ) := by
  simpa [map_inv, ConjAct.toConjAct_inv, inv_inv, inv_smul_eq_iff] using
    Gamma1_map_conjAct_eq ⟨(g : SL(2, ℤ))⁻¹, (Gamma0 N).inv_mem g.property⟩

/-- For a function `f` invariant under `Γ₁(N).map(mapGL ℝ)`, the slash action
`f ↦ f ∣[k] (mapGL ℝ g)` for `g ∈ Γ₀(N)` produces another `Γ₁(N).map(mapGL ℝ)`-invariant
function. -/
lemma slash_mapGL_invariant_of_Gamma1_invariant {k : ℤ} (g : ↥(Gamma0 N))
    {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℝ), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    (f ∣[k] mapGL ℝ (g : SL(2, ℤ))) ∣[k] γ = f ∣[k] mapGL ℝ (g : SL(2, ℤ)) := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  rw [← SlashAction.slash_mul, ← map_mul,
    show (g : SL(2, ℤ)) * σ = ((g : SL(2, ℤ)) * σ * (g : SL(2, ℤ))⁻¹) * (g : SL(2, ℤ)) by group,
    map_mul, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map.mpr ⟨_, Gamma0_normalizes_Gamma1 g σ hσ, rfl⟩)]

/-- For `g ∈ Γ₀(N)` and `γ ∈ GL₂(ℝ)` with `γ • ∞ = c`, a cusp `c` for `Γ₁(N).map(mapGL ℝ)`
transports along the conjugation by `mapGL ℝ g` to a cusp at `(mapGL ℝ g · γ) • ∞`. -/
lemma isCusp_mul_mapGL_smul_infty (g : ↥(Gamma0 N))
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ)))
    {γ : GL (Fin 2) ℝ} (hγ : γ • (OnePoint.infty : OnePoint ℝ) = c) :
    IsCusp ((mapGL ℝ (g : SL(2, ℤ)) * γ) • (OnePoint.infty : OnePoint ℝ))
      ((Gamma1 N).map (mapGL ℝ)) := by
  rw [mul_smul, hγ]
  exact Gamma1_map_conjAct_eq_forward g ▸ hc.smul (mapGL ℝ (g : SL(2, ℤ)))

/-- The diamond operator on modular forms for `Gamma1(N)`: for `g ∈ Gamma0(N)`,
the slash action `f ↦ f ∣[k] g` preserves `ModularForm ((Gamma1 N).map (mapGL ℝ)) k`
by the normality of `Gamma1` in `Gamma0`. -/
noncomputable def diamondOpAux (k : ℤ) (g : ↥(Gamma0 N)) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
      { toFun := ⇑f ∣[k] (mapGL ℝ (g : SL(2, ℤ)))
        slash_action_eq' _ hγ :=
          slash_mapGL_invariant_of_Gamma1_invariant g
            (fun _ hδ ↦ SlashInvariantFormClass.slash_action_eq f _ hδ) hγ }
      holo' := (ModularFormClass.holo f).slash k _
      bdd_at_cusps' {c} hc _ hγ := by
        rw [← SlashAction.slash_mul, ← OnePoint.isBoundedAt_infty_iff,
          ← OnePoint.IsBoundedAt.smul_iff]
        exact ModularFormClass.bdd_at_cusps f (isCusp_mul_mapGL_smul_infty g hc hγ) }
  map_add' f₁ f₂ := by
    ext z
    exact congr_fun (SlashAction.add_slash k (mapGL ℝ (g : SL(2, ℤ))) ⇑f₁ ⇑f₂) z
  map_smul' c f := by
    ext z
    change ((c • ⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z = c • _
    simp [ModularForm.smul_slash]

/-- The `Gamma0Map` lifts to a group homomorphism to `(ZMod N)ˣ`: the bottom-right
entry is a unit mod N with inverse the top-left entry (from `det = 1` and `N ∣ c`). -/
noncomputable def Gamma0MapUnits : ↥(Gamma0 N) →* (ZMod N)ˣ where
  toFun g := by
    set A := (g : SL(2, ℤ))
    have hc : (A 1 0 : ZMod N) = 0 := Gamma0_mem.mp g.property
    have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using A.prop
    have hunit : (A 0 0 : ZMod N) * (A 1 1 : ZMod N) = 1 := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero]
        using congr_arg (Int.cast : ℤ → ZMod N) hdet
    exact Units.mk (Gamma0Map N g) (A 0 0 : ZMod N) ((mul_comm _ _).trans hunit) hunit
  map_one' := Units.ext (map_one (Gamma0Map N))
  map_mul' g₁ g₂ := Units.ext (map_mul (Gamma0Map N) g₁ g₂)

@[simp]
lemma Gamma0MapUnits_val (g : ↥(Gamma0 N)) : (Gamma0MapUnits g : ZMod N) = Gamma0Map N g := rfl

/-- If two `Γ₀(N)` elements have equal image under `Gamma0Map`, their ratio
`g₁ · g₂⁻¹` lies in `Γ₁(N)` (as an `SL₂(ℤ)` element). -/
lemma mul_inv_mem_Gamma1_of_Gamma0Map_eq (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    ((g₁ : SL(2, ℤ)) * (g₂ : SL(2, ℤ))⁻¹) ∈ Gamma1 N := by
  have heq_u : Gamma0MapUnits g₁ = Gamma0MapUnits g₂ := Units.ext heq
  have hker : Gamma0MapUnits (g₁ * g₂⁻¹) = 1 := by simp [map_mul, map_inv, heq_u]
  exact (Gamma1_mem _ _).mpr <| (Gamma1_to_Gamma0_mem _).mp <| congr_arg Units.val hker

/-- Slash-transport for `Γ₁(N)`-invariant functions: if `f` is invariant under
`(Γ₁(N)).map(mapGL ℝ)` and `Gamma0Map N g₁ = Gamma0Map N g₂`, then `f ∣[k] g₁ = f ∣[k] g₂`. -/
lemma slash_eq_of_Gamma0Map_eq {k : ℤ} {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℝ), f ∣[k] γ = f)
    (g₁ g₂ : ↥(Gamma0 N)) (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    f ∣[k] mapGL ℝ (g₁ : SL(2, ℤ)) = f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ)) := by
  rw [show (g₁ : SL(2, ℤ)) = ((g₁ : SL(2, ℤ)) * (g₂ : SL(2, ℤ))⁻¹) * (g₂ : SL(2, ℤ)) by group,
    map_mul, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map.mpr ⟨_, mul_inv_mem_Gamma1_of_Gamma0Map_eq g₁ g₂ heq, rfl⟩)]

/-- The diamond operator depends only on the `Gamma0Map` value: if two `Gamma0(N)`
elements have the same image, their diamond operators agree. -/
theorem diamondOpAux_eq_of_Gamma0Map_eq (k : ℤ) (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) : diamondOpAux k g₁ = diamondOpAux k g₂ := by
  ext f z
  exact congr_fun (slash_eq_of_Gamma0Map_eq
    (fun _ hγ ↦ SlashInvariantFormClass.slash_action_eq f _ hγ) g₁ g₂ heq) z

/-- `Gamma0MapUnits` is surjective: every unit `d ∈ (ZMod N)ˣ` is realized as the
bottom-right entry of some `g ∈ Gamma0(N)`. -/
theorem Gamma0MapUnits_surjective [NeZero N] :
    Function.Surjective (Gamma0MapUnits (N := N)) := fun d ↦ by
  obtain ⟨g, hg⟩ := SL2Reduction.SL2_reduction_surjective N
    ⟨!![↑d⁻¹, 0; 0, ↑d], by simp [Matrix.det_fin_two]⟩
  have hg11 := congr_fun (congr_fun (congr_arg Subtype.val hg) 1)
  exact ⟨⟨g, Gamma0_mem.mpr (by simpa using hg11 0)⟩, Units.ext <| by simpa [Gamma0Map] using hg11 1⟩

/-- The diamond operator `⟨d⟩` on modular forms for `Gamma1(N)`, indexed by
`d : (ZMod N)ˣ`. -/
noncomputable def diamondOp [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  diamondOpAux k (Gamma0MapUnits_surjective d).choose

/-- `diamondOp` equals `diamondOpAux` on any representative with the right image. -/
theorem diamondOp_eq_diamondOpAux [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : Gamma0MapUnits g = d) : diamondOp k d = diamondOpAux k g :=
  diamondOpAux_eq_of_Gamma0Map_eq k _ g
    (by simp [← Gamma0MapUnits_val, (Gamma0MapUnits_surjective d).choose_spec, hg])

/-- The diamond operator at `1` is the identity. -/
@[simp]
theorem diamondOp_one [NeZero N] (k : ℤ) : diamondOp (N := N) k 1 = LinearMap.id := by
  rw [diamondOp_eq_diamondOpAux k 1 1 (map_one _)]
  ext f z
  change (⇑f ∣[k] mapGL ℝ (1 : SL(2, ℤ))) z = f z
  simp only [map_one, SlashAction.slash_one]

/-- Diamond operators compose: `⟨d₁ * d₂⟩ = ⟨d₁⟩ ∘ ⟨d₂⟩`. -/
theorem diamondOp_mul [NeZero N] (k : ℤ) (d₁ d₂ : (ZMod N)ˣ) :
    diamondOp k (d₁ * d₂) = (diamondOp k d₁).comp (diamondOp k d₂) := by
  obtain ⟨g₁, hg₁⟩ := Gamma0MapUnits_surjective (N := N) d₁
  obtain ⟨g₂, hg₂⟩ := Gamma0MapUnits_surjective (N := N) d₂
  rw [diamondOp_eq_diamondOpAux k (d₁ * d₂) (g₂ * g₁) (by simp [map_mul, hg₁, hg₂, mul_comm]),
    diamondOp_eq_diamondOpAux k d₁ g₁ hg₁, diamondOp_eq_diamondOpAux k d₂ g₂ hg₂]
  ext f z
  change (⇑f ∣[k] mapGL ℝ ((g₂ : SL(2, ℤ)) * (g₁ : SL(2, ℤ)))) z =
    ((⇑f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ))) ∣[k] mapGL ℝ (g₁ : SL(2, ℤ))) z
  rw [map_mul, SlashAction.slash_mul]

/-- The diamond operator as a monoid homomorphism `(ZMod N)ˣ →* Module.End ℂ (...)`. -/
noncomputable def diamondOpHom [NeZero N] (k : ℤ) :
    (ZMod N)ˣ →* Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := diamondOp k
  map_one' := diamondOp_one k
  map_mul' := diamondOp_mul k

lemma diamondOpHom_apply [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) :
    diamondOpHom k d = diamondOp k d := rfl

private noncomputable def diamondOpCuspAux (k : ℤ) (g : ↥(Gamma0 N)) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
      { toFun := ⇑f ∣[k] (mapGL ℝ (g : SL(2, ℤ)))
        slash_action_eq' _ hγ :=
          slash_mapGL_invariant_of_Gamma1_invariant g
            (fun _ hδ ↦ SlashInvariantFormClass.slash_action_eq f _ hδ) hγ }
      holo' := (CuspFormClass.holo f).slash k _
      zero_at_cusps' {c} hc _ hγ := by
        rw [← SlashAction.slash_mul, ← OnePoint.isZeroAt_infty_iff,
          ← OnePoint.IsZeroAt.smul_iff]
        exact CuspFormClass.zero_at_cusps f (isCusp_mul_mapGL_smul_infty g hc hγ) }
  map_add' f₁ f₂ := by
    ext z
    exact congr_fun (SlashAction.add_slash k (mapGL ℝ (g : SL(2, ℤ))) ⇑f₁ ⇑f₂) z
  map_smul' c f := by
    ext z
    change ((c • ⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z = c • _
    simp [ModularForm.smul_slash]

/-- Well-definedness for the cusp-form diamond operator. -/
theorem diamondOpCuspAux_eq_of_Gamma0Map_eq (k : ℤ) (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    diamondOpCuspAux k g₁ = diamondOpCuspAux k g₂ := by
  ext f z
  exact congr_fun (slash_eq_of_Gamma0Map_eq
    (fun _ hγ ↦ SlashInvariantFormClass.slash_action_eq f _ hγ) g₁ g₂ heq) z

/-- The cusp-form diamond operator indexed by `d : (ZMod N)ˣ`. -/
noncomputable def diamondOpCusp [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  diamondOpCuspAux k (Gamma0MapUnits_surjective d).choose

/-- `diamondOpCusp` equals `diamondOpCuspAux` on any representative. -/
theorem diamondOpCusp_eq (k : ℤ) (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : Gamma0MapUnits g = d) [NeZero N] :
    diamondOpCusp k d = diamondOpCuspAux k g :=
  diamondOpCuspAux_eq_of_Gamma0Map_eq k _ g
    (by simp [← Gamma0MapUnits_val, (Gamma0MapUnits_surjective d).choose_spec, hg])

@[simp]
theorem diamondOpCusp_one [NeZero N] (k : ℤ) : diamondOpCusp (N := N) k 1 = LinearMap.id := by
  rw [diamondOpCusp_eq k 1 1 (map_one _)]
  ext f z
  change (⇑f ∣[k] mapGL ℝ (1 : SL(2, ℤ))) z = f z
  simp only [map_one, SlashAction.slash_one]

theorem diamondOpCusp_mul [NeZero N] (k : ℤ) (d₁ d₂ : (ZMod N)ˣ) :
    diamondOpCusp k (d₁ * d₂) = (diamondOpCusp k d₁).comp (diamondOpCusp k d₂) := by
  obtain ⟨g₁, hg₁⟩ := Gamma0MapUnits_surjective (N := N) d₁
  obtain ⟨g₂, hg₂⟩ := Gamma0MapUnits_surjective (N := N) d₂
  rw [diamondOpCusp_eq k (d₁ * d₂) (g₂ * g₁) (by simp [map_mul, hg₁, hg₂, mul_comm]),
    diamondOpCusp_eq k d₁ g₁ hg₁, diamondOpCusp_eq k d₂ g₂ hg₂]
  ext f z
  change (⇑f ∣[k] mapGL ℝ ((g₂ : SL(2, ℤ)) * (g₁ : SL(2, ℤ)))) z =
    ((⇑f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ))) ∣[k] mapGL ℝ (g₁ : SL(2, ℤ))) z
  rw [map_mul, SlashAction.slash_mul]

/-- The cusp-form diamond operator as a monoid homomorphism. -/
noncomputable def diamondOpCuspHom [NeZero N] (k : ℤ) :
    (ZMod N)ˣ →* Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := diamondOpCusp k
  map_one' := diamondOpCusp_one k
  map_mul' := diamondOpCusp_mul k

lemma diamondOpCuspHom_apply [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) :
    diamondOpCuspHom k d = diamondOpCusp k d := rfl

/-- The Nebentypus character space `S_k(Γ₁(N), χ)`: cusp forms on which every
diamond operator `⟨d⟩` acts by the scalar `χ(d)`. -/
noncomputable def cuspFormCharSpace [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, Module.End.eigenspace (diamondOpCuspHom k d) (↑(χ d))

/-- Membership in `S_k(Γ₁(N), χ)`: `f` is in the `χ`-eigenspace iff
`⟨d⟩ f = χ(d) • f` for every `d ∈ (ZMod N)ˣ`. -/
theorem mem_cuspFormCharSpace_iff [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ cuspFormCharSpace k χ ↔
    ∀ d : (ZMod N)ˣ, diamondOpCuspHom k d f = (↑(χ d) : ℂ) • f := by
  simp only [cuspFormCharSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- Diamond operators act by `χ(d)` on elements of `S_k(Γ₁(N), χ)`. -/
theorem diamondOpCusp_apply_charSpace [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (d : (ZMod N)ˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    diamondOpCuspHom k d f = (↑(χ d) : ℂ) • f :=
  (mem_cuspFormCharSpace_iff k χ f).mp hf d

/-- The modular-form Nebentypus character space `M_k(Γ₁(N), χ)`. -/
noncomputable def modFormCharSpace [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, Module.End.eigenspace (diamondOpHom k d) (↑(χ d))

/-- Membership in `M_k(Γ₁(N), χ)`: `f` is in the `χ`-eigenspace iff `⟨d⟩ f = χ(d) • f`
for every `d ∈ (ZMod N)ˣ`. -/
theorem mem_modFormCharSpace_iff [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ modFormCharSpace k χ ↔
    ∀ d : (ZMod N)ˣ, diamondOpHom k d f = (↑(χ d) : ℂ) • f := by
  simp only [modFormCharSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- **Bridge**: for a `Gamma1`-invariant modular form `f`, membership in the
diamond-eigenspace `modFormCharSpace k χ₀` is equivalent to the classical Nebentypus
relation `f ∣[k] g = χ₀(d(g)) • f` for all `g ∈ Γ₀(N)`. -/
theorem modFormCharSpace_iff_nebentypus [NeZero N] (k : ℤ) (χ₀ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ modFormCharSpace k χ₀ ↔
    ∀ g : ↥(Gamma0 N), (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ₀ (Gamma0MapUnits g)) : ℂ) • ⇑f := by
  rw [mem_modFormCharSpace_iff]
  refine ⟨fun h g ↦ ?_, fun h d ↦ ?_⟩
  · have hd := h (Gamma0MapUnits g)
    rw [diamondOpHom_apply, diamondOp_eq_diamondOpAux k _ g rfl] at hd
    exact congr_arg (⇑· : ModularForm _ k → _) hd
  · obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
    rw [diamondOpHom_apply, diamondOp_eq_diamondOpAux k d g hg, ← hg]
    exact ModularForm.ext (congr_fun (h g))

/-- **Bridge (cusp forms)**: for a `Gamma1`-invariant cusp form `f`, membership in the
diamond-eigenspace `cuspFormCharSpace k χ₀` is equivalent to the classical Nebentypus
relation `f ∣[k] g = χ₀(d(g)) • f` for all `g ∈ Γ₀(N)`. -/
theorem cuspFormCharSpace_iff_nebentypus [NeZero N] (k : ℤ) (χ₀ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ cuspFormCharSpace k χ₀ ↔
    ∀ g : ↥(Gamma0 N), (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ₀ (Gamma0MapUnits g)) : ℂ) • ⇑f := by
  rw [mem_cuspFormCharSpace_iff]
  refine ⟨fun h g ↦ ?_, fun h d ↦ ?_⟩
  · have hd := h (Gamma0MapUnits g)
    rw [diamondOpCuspHom_apply, diamondOpCusp_eq k _ g rfl] at hd
    exact congr_arg (⇑· : CuspForm _ k → _) hd
  · obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
    rw [diamondOpCuspHom_apply, diamondOpCusp_eq k d g hg, ← hg]
    exact CuspForm.ext (congr_fun (h g))

end HeckeRing.GL2
