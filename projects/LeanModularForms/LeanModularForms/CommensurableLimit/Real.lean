/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.CommensurableLimit.CommensuratorAction
import Mathlib.RepresentationTheory.Invariants

/-!
# The `ℝ`-vector-space direct limit over a whole commensurability class, with the full commensurator
acting

This is the genuinely general companion to `CommensurableLimit/DirectLimit.lean` and
`CommensurableLimit/CommensuratorAction.lean`. Those build the `ℂ`-vector-space direct limit over the
**determinant-one** part of a commensurability class, with the **positive-determinant** part of the
commensurator acting — both restrictions forced by the fact that `ModularForm Γ k` is a `Module ℂ`
only when `Γ.HasDetOne`, and the slash action is `ℂ`-linear only in positive determinant.

Over `ℝ` neither restriction is needed:

* `ModularForm Γ k` is a `Module ℝ` for **every** subgroup `Γ` (mathlib's unconditional
  `instance : Module ℝ (ModularForm Γ k)`), so the index is the **whole** commensurability class —
  the predicate `P = fun _ ↦ True`.
* The slash action is `ℝ`-linear for **every** `g ∈ GL₂(ℝ)`: `(r • f) ∣[k] g = σ g (↑r) • (f ∣[k] g)`
  and `UpperHalfPlane.σ g` fixes `ℝ` (`UpperHalfPlane.σ_ofReal`), so the acting group is the **full**
  commensurator `Commensurable.commensurator Γ₀`, with no positivity hypotheses.

The index type `ModularForm.CommIndex` and the conjugation action `ModularForm.CommIndex.conj` are
shared with the `ℂ` construction (`CommensurabilityClass.lean` / `CommensuratorAction.lean`); only
the scalar field, the predicate, and the acting group differ here.

## Main definitions

* `ModularForm.restrictSubgroupℝ` — restriction along `Γ′ ≤ Γ` as an `ℝ`-linear map (no `HasDetOne`).
* `ModularFormCommensurableReal Γ₀ k` — the `ℝ`-vector-space direct limit over the whole class.
* `ModularFormCommensurableReal.ofLevelℝ` / `liftℝ` — the canonical maps in / the universal property.
* `ModularForm.translateℝ` — slash by an arbitrary `g` as an `ℝ`-linear map.
* `ModularFormCommensurableReal.smulMapℝ` — the action of `g ∈ Commensurable.commensurator Γ₀`.
* `ModularFormCommensurableReal.commRepℝ` — the weight-`k` `ℝ`-representation of the full
  commensurator on the limit.
* `ModularFormCommensurableReal.ofLevelℝInvariantsEquiv` — `ModularForm Γ.carrier k` is `ℝ`-linearly
  isomorphic to the level invariants.

## Main results

* `ModularFormCommensurableReal.range_ofLevelℝ_eq_invariants` — the level-`Γ` invariants of the
  commensurator action are exactly the image of `ModularForm Γ.carrier k` under `ofLevelℝ`.
-/

open scoped MatrixGroups Pointwise

open Subgroup

namespace ModularForm

variable {k : ℤ}

/-- Restriction of a modular form along a subgroup inclusion `Γ′ ≤ Γ`, as an `ℝ`-linear map.

The `ℝ`-scalar analogue of `ModularForm.restrictSubgroupₗ`. Because `ModularForm Γ k` is a `Module ℝ`
unconditionally, **no** `HasDetOne` hypothesis is needed. The underlying function is unchanged, so
additivity and `ℝ`-homogeneity are definitional. -/
def restrictSubgroupℝ {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) :
    ModularForm Γ k →ₗ[ℝ] ModularForm Γ' k where
  toFun f :=
    { toFun := f.toFun
      slash_action_eq' := fun γ hγ ↦ f.slash_action_eq' γ (h hγ)
      holo' := f.holo'
      bdd_at_cusps' := fun hc ↦ f.bdd_at_cusps' (hc.mono h) }
  map_add' f g := by ext z; rfl
  map_smul' c f := by ext z; rfl

@[simp]
lemma coe_restrictSubgroupℝ {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    ⇑(restrictSubgroupℝ h f) = ⇑f := rfl

lemma restrictSubgroupℝ_injective {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) :
    Function.Injective (restrictSubgroupℝ (k := k) h) := by
  intro f g hfg
  ext z
  simpa using DFunLike.congr_fun hfg z

/-- The slash action is `ℝ`-linear for **every** `g ∈ GL₂(ℝ)`: scaling by a real `c` commutes with
`∣[k] g`, because `UpperHalfPlane.σ g` fixes the reals (`σ_ofReal`). This is the `ℝ`-scalar
replacement for the positive-determinant lemma `sigma_eq_refl_of_pos_det`. -/
private lemma real_smul_slash (c : ℝ) (g : GL (Fin 2) ℝ) (φ : UpperHalfPlane → ℂ) :
    (c • φ) ∣[k] g = c • (φ ∣[k] g) := by
  ext τ
  simp only [slash_apply, Pi.smul_apply, Complex.real_smul, map_mul, UpperHalfPlane.σ_ofReal]
  ring

/-- Translation by `g` (slash by `g`) as an `ℝ`-linear map `ModularForm Γ k → ModularForm (g⁻¹Γg) k`,
for an **arbitrary** `g ∈ GL₂(ℝ)`. The slash action is `ℝ`-linear for every `g` (the `σ`-twist fixes
the reals), so — unlike the `ℂ`-linear `ModularForm.translateₗ` — there is no positivity hypothesis
and no `HasDetOne`. The underlying function is `⇑f ∣[k] g`. -/
noncomputable def translateℝ (g : GL (Fin 2) ℝ) {Γ : Subgroup (GL (Fin 2) ℝ)} :
    ModularForm Γ k →ₗ[ℝ] ModularForm (ConjAct.toConjAct g⁻¹ • Γ) k where
  toFun f := ModularForm.translate f g
  map_add' f₁ f₂ := by
    ext z
    simp only [ModularForm.coe_translate, ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply]
  map_smul' c f := by
    ext z
    change (⇑(c • f) ∣[k] g) z = c • ((⇑f ∣[k] g) z)
    rw [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f from rfl, real_smul_slash]
    rfl

@[simp] lemma coe_translateℝ (g : GL (Fin 2) ℝ) {Γ : Subgroup (GL (Fin 2) ℝ)} (f : ModularForm Γ k) :
    ⇑(translateℝ g f) = ⇑f ∣[k] g := rfl

end ModularForm

open ModularForm

/-- The whole commensurability class is always nonempty as an index: the base `Γ₀` itself is an index
(`P = fun _ ↦ True` imposes nothing). -/
instance (Γ₀ : Subgroup (GL (Fin 2) ℝ)) : Nonempty (CommIndex Γ₀ (fun _ ↦ True)) :=
  ⟨CommIndex.base trivial⟩

/-- The transition maps of the whole-class directed system: for `i ≤ j` (i.e. `j.carrier ≤
i.carrier`), restriction `ModularForm i.carrier k → ModularForm j.carrier k`, `ℝ`-linear. -/
noncomputable def commTransitionℝ (Γ₀ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :
    ∀ i j : CommIndex Γ₀ (fun _ ↦ True), i ≤ j →
      (ModularForm i.carrier k →ₗ[ℝ] ModularForm j.carrier k) :=
  fun _ _ h ↦ ModularForm.restrictSubgroupℝ h

/-- The restriction maps form a directed system (each is the identity on underlying functions). -/
instance commDirectedSystemℝ (Γ₀ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :
    DirectedSystem (fun i : CommIndex Γ₀ (fun _ ↦ True) ↦ ModularForm i.carrier k)
      (fun i j h ↦ (commTransitionℝ Γ₀ k i j h :
        ModularForm i.carrier k → ModularForm j.carrier k)) where
  map_self := by intros; ext z; rfl
  map_map := by intros; ext z; rfl

/-- **Modular forms of weight `k` over the whole commensurability class of `Γ₀`, as an
`ℝ`-vector space**, defined as the direct limit of `ModularForm Γ k` over *all* subgroups `Γ`
commensurable with `Γ₀` (no determinant condition), ordered by reverse inclusion with restriction as
the transition maps. -/
noncomputable def ModularFormCommensurableReal (Γ₀ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) : Type :=
  Module.DirectLimit (fun i : CommIndex Γ₀ (fun _ ↦ True) ↦ ModularForm i.carrier k)
    (commTransitionℝ Γ₀ k)

namespace ModularFormCommensurableReal

open ModularForm

noncomputable instance (Γ₀ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :
    AddCommGroup (ModularFormCommensurableReal Γ₀ k) :=
  inferInstanceAs (AddCommGroup
    (Module.DirectLimit (fun i : CommIndex Γ₀ (fun _ ↦ True) ↦ ModularForm i.carrier k)
      (commTransitionℝ Γ₀ k)))

noncomputable instance (Γ₀ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :
    Module ℝ (ModularFormCommensurableReal Γ₀ k) :=
  inferInstanceAs (Module ℝ
    (Module.DirectLimit (fun i : CommIndex Γ₀ (fun _ ↦ True) ↦ ModularForm i.carrier k)
      (commTransitionℝ Γ₀ k)))

variable (Γ₀ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)

/-- The canonical `ℝ`-linear map of the level-`i` modular forms into the direct limit. -/
noncomputable def ofLevelℝ (i : CommIndex Γ₀ (fun _ ↦ True)) :
    ModularForm i.carrier k →ₗ[ℝ] ModularFormCommensurableReal Γ₀ k :=
  Module.DirectLimit.of ℝ (CommIndex Γ₀ (fun _ ↦ True)) (fun i ↦ ModularForm i.carrier k)
    (commTransitionℝ Γ₀ k) i

/-- `ofLevelℝ` is compatible with restriction: restricting to a finer level then including agrees with
including directly. -/
@[simp]
lemma ofLevelℝ_restrict {i j : CommIndex Γ₀ (fun _ ↦ True)} (h : i ≤ j)
    (f : ModularForm i.carrier k) :
    ofLevelℝ Γ₀ k j (restrictSubgroupℝ h f) = ofLevelℝ Γ₀ k i f :=
  Module.DirectLimit.of_f

/-- Each level embeds into the direct limit: `ofLevelℝ` is injective. -/
lemma ofLevelℝ_injective (i : CommIndex Γ₀ (fun _ ↦ True)) :
    Function.Injective (ofLevelℝ Γ₀ k i) := by
  intro x y hxy
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy
  exact restrictSubgroupℝ_injective hij hj

/-- **Universal property**: a family of `ℝ`-linear maps `gᵢ : ModularForm i.carrier k → P` compatible
with restriction factors (uniquely) through the direct limit. -/
noncomputable def liftℝ {P : Type*} [AddCommGroup P] [Module ℝ P]
    (g : ∀ i : CommIndex Γ₀ (fun _ ↦ True), ModularForm i.carrier k →ₗ[ℝ] P)
    (Hg : ∀ (i j : CommIndex Γ₀ (fun _ ↦ True)) (h : i ≤ j) (x : ModularForm i.carrier k),
      g j (restrictSubgroupℝ h x) = g i x) :
    ModularFormCommensurableReal Γ₀ k →ₗ[ℝ] P :=
  Module.DirectLimit.lift ℝ (CommIndex Γ₀ (fun _ ↦ True)) (fun i ↦ ModularForm i.carrier k)
    (commTransitionℝ Γ₀ k) g Hg

@[simp]
lemma liftℝ_ofLevel {P : Type*} [AddCommGroup P] [Module ℝ P]
    (g : ∀ i : CommIndex Γ₀ (fun _ ↦ True), ModularForm i.carrier k →ₗ[ℝ] P)
    (Hg : ∀ (i j : CommIndex Γ₀ (fun _ ↦ True)) (h : i ≤ j) (x : ModularForm i.carrier k),
      g j (restrictSubgroupℝ h x) = g i x)
    (i : CommIndex Γ₀ (fun _ ↦ True)) (x : ModularForm i.carrier k) :
    liftℝ Γ₀ k g Hg (ofLevelℝ Γ₀ k i x) = g i x :=
  Module.DirectLimit.lift_of _ _ _

/-- Induction principle for the limit phrased with `ofLevelℝ` rather than the raw
`Module.DirectLimit.of` (to which it is definitionally equal). -/
@[elab_as_elim]
lemma ofLevelℝ_induction {C : ModularFormCommensurableReal Γ₀ k → Prop}
    (z : ModularFormCommensurableReal Γ₀ k)
    (ih : ∀ (i : CommIndex Γ₀ (fun _ ↦ True)) (f : ModularForm i.carrier k),
      C (ofLevelℝ Γ₀ k i f)) : C z :=
  Module.DirectLimit.induction_on z ih

/-- Every element of the limit comes from some level. -/
lemma existsℝ_ofLevel (z : ModularFormCommensurableReal Γ₀ k) :
    ∃ (i : CommIndex Γ₀ (fun _ ↦ True)) (f : ModularForm i.carrier k), ofLevelℝ Γ₀ k i f = z :=
  Module.DirectLimit.exists_of z

/-- The action of `g ∈ Commensurable.commensurator Γ₀` (the **full** commensurator) on the direct
limit: on the level-`i` piece it translates by `g⁻¹` (an `ℝ`-linear map for any `g`) into the
conjugate level `g i g⁻¹`. -/
noncomputable def smulMapℝ (g : ↥(Commensurable.commensurator Γ₀)) :
    ModularFormCommensurableReal Γ₀ k →ₗ[ℝ] ModularFormCommensurableReal Γ₀ k :=
  liftℝ Γ₀ k
    (fun i ↦ (ofLevelℝ Γ₀ k (CommIndex.conj g.1 g.2 i)).comp (translateℝ g.1⁻¹))
    (fun i j h x ↦ by
      have hconj : CommIndex.conj g.1 g.2 i ≤ CommIndex.conj g.1 g.2 j := by
        rw [CommIndex.le_def, CommIndex.conj_carrier, CommIndex.conj_carrier]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (CommIndex.le_def.mp h)
      have hcomm : translateℝ g.1⁻¹ (restrictSubgroupℝ h x)
          = restrictSubgroupℝ hconj (translateℝ g.1⁻¹ x) := by
        ext z; rfl
      simp only [LinearMap.comp_apply]
      exact (congrArg (ofLevelℝ Γ₀ k (CommIndex.conj g.1 g.2 j)) hcomm).trans
        (ofLevelℝ_restrict Γ₀ k hconj (translateℝ g.1⁻¹ x)))

lemma smulMapℝ_ofLevel (g : ↥(Commensurable.commensurator Γ₀)) (i : CommIndex Γ₀ (fun _ ↦ True))
    (f : ModularForm i.carrier k) :
    smulMapℝ Γ₀ k g (ofLevelℝ Γ₀ k i f)
      = ofLevelℝ Γ₀ k (CommIndex.conj g.1 g.2 i) (translateℝ g.1⁻¹ f) :=
  liftℝ_ofLevel Γ₀ k _ _ i f

/-- The `ℝ`-linear inclusion of a single level into functions `ℍ → ℂ`. -/
def coeℝ {Γ : Subgroup (GL (Fin 2) ℝ)} :
    ModularForm Γ k →ₗ[ℝ] (UpperHalfPlane → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma coeℝ_apply {Γ : Subgroup (GL (Fin 2) ℝ)} (f : ModularForm Γ k) : coeℝ k f = ⇑f := rfl

/-- The underlying-function map out of the limit: a form over the class restricts to an honest
function `ℍ → ℂ`. It is `ℝ`-linear and injective, and intertwines `smulMapℝ g` with `· ∣[k] g⁻¹`. -/
noncomputable def toFunℝ : ModularFormCommensurableReal Γ₀ k →ₗ[ℝ] (UpperHalfPlane → ℂ) :=
  liftℝ Γ₀ k (fun _ ↦ coeℝ k)
    (fun i j h x ↦ by simp only [coeℝ_apply, coe_restrictSubgroupℝ])

@[simp] lemma toFunℝ_ofLevel (i : CommIndex Γ₀ (fun _ ↦ True)) (f : ModularForm i.carrier k) :
    toFunℝ Γ₀ k (ofLevelℝ Γ₀ k i f) = ⇑f := by
  unfold toFunℝ
  simp only [liftℝ_ofLevel, coeℝ_apply]

lemma toFunℝ_injective : Function.Injective (toFunℝ Γ₀ k) := by
  unfold toFunℝ liftℝ
  apply Module.DirectLimit.lift_injective
  intro i a b hab
  exact DFunLike.coe_injective hab

lemma toFunℝ_smulMap (g : ↥(Commensurable.commensurator Γ₀))
    (x : ModularFormCommensurableReal Γ₀ k) :
    toFunℝ Γ₀ k (smulMapℝ Γ₀ k g x) = toFunℝ Γ₀ k x ∣[k] g.1⁻¹ := by
  induction x using ofLevelℝ_induction with
  | ih i f => rw [smulMapℝ_ofLevel, toFunℝ_ofLevel, toFunℝ_ofLevel]; rfl

lemma smulMapℝ_one : smulMapℝ Γ₀ k (1 : ↥(Commensurable.commensurator Γ₀)) = LinearMap.id := by
  ext x
  apply toFunℝ_injective
  simp only [toFunℝ_smulMap, LinearMap.id_coe, id_eq, OneMemClass.coe_one, inv_one,
    SlashAction.slash_one]

lemma smulMapℝ_mul (g h : ↥(Commensurable.commensurator Γ₀)) :
    smulMapℝ Γ₀ k (g * h) = smulMapℝ Γ₀ k g ∘ₗ smulMapℝ Γ₀ k h := by
  ext x
  apply toFunℝ_injective
  simp only [toFunℝ_smulMap, LinearMap.comp_apply, Subgroup.coe_mul, mul_inv_rev,
    SlashAction.slash_mul]

/-- The weight-`k` action of the **full** commensurator `Commensurable.commensurator Γ₀` on
`ModularFormCommensurableReal Γ₀ k` as an `ℝ`-linear representation: `g` acts by the slash action of
`g⁻¹` (well-defined and `ℝ`-linear for any `g`), permuting the levels by conjugation. -/
noncomputable def commRepℝ : Representation ℝ (↥(Commensurable.commensurator Γ₀))
    (ModularFormCommensurableReal Γ₀ k) where
  toFun := smulMapℝ Γ₀ k
  map_one' := smulMapℝ_one Γ₀ k
  map_mul' := smulMapℝ_mul Γ₀ k

@[simp] lemma commRepℝ_apply (g : ↥(Commensurable.commensurator Γ₀)) :
    commRepℝ Γ₀ k g = smulMapℝ Γ₀ k g := rfl

/-- The inclusion of a level (any subgroup commensurable with `Γ₀`) into the full commensurator. -/
noncomputable def levelInclℝ (Γ : CommIndex Γ₀ (fun _ ↦ True)) :
    Γ.carrier →* ↥(Commensurable.commensurator Γ₀) :=
  Subgroup.inclusion (Subgroup.commensurable_le_commensurator Γ.commensurable)

@[simp] lemma coe_levelInclℝ (Γ : CommIndex Γ₀ (fun _ ↦ True)) (γ : Γ.carrier) :
    ((levelInclℝ Γ₀ Γ γ : ↥(Commensurable.commensurator Γ₀)) : GL (Fin 2) ℝ) =
      (γ : GL (Fin 2) ℝ) := rfl

/-- **The level invariants of the (full) commensurator action are the modular forms of that level.**

For a level `Γ` in the commensurability class, the image of `ModularForm Γ.carrier k` under
`ofLevelℝ` is exactly the submodule of `ModularFormCommensurableReal Γ₀ k` fixed by the action of all
of `Γ.carrier` (restricted from the `commRepℝ` action of the full commensurator). -/
theorem range_ofLevelℝ_eq_invariants (Γ : CommIndex Γ₀ (fun _ ↦ True)) :
    LinearMap.range (ofLevelℝ Γ₀ k Γ)
      = Representation.invariants ((commRepℝ Γ₀ k).comp (levelInclℝ Γ₀ Γ)) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [Representation.mem_invariants]
    intro γ
    change smulMapℝ Γ₀ k (levelInclℝ Γ₀ Γ γ) (ofLevelℝ Γ₀ k Γ f) = ofLevelℝ Γ₀ k Γ f
    apply toFunℝ_injective
    rw [toFunℝ_smulMap, toFunℝ_ofLevel, coe_levelInclℝ]
    exact SlashInvariantForm.slash_action_eqn f _ (Γ.carrier.inv_mem γ.2)
  · intro x hx
    rw [Representation.mem_invariants] at hx
    obtain ⟨Λ, f, rfl⟩ := existsℝ_ofLevel Γ₀ k x
    set Λ' : CommIndex Γ₀ (fun _ ↦ True) :=
      ⟨Λ.carrier ⊓ Γ.carrier, Subgroup.commensurable_inf Λ.commensurable Γ.commensurable, trivial⟩
    have hΛΛ' : Λ ≤ Λ' := CommIndex.le_def.mpr inf_le_left
    have hΓΛ' : Γ ≤ Λ' := CommIndex.le_def.mpr inf_le_right
    have hcomm : Subgroup.Commensurable Λ.carrier Γ.carrier :=
      Λ.commensurable.trans Γ.commensurable.symm
    have key : ∀ g : Γ.carrier, (⇑f : UpperHalfPlane → ℂ) ∣[k] (g : GL (Fin 2) ℝ)⁻¹ = ⇑f := by
      intro g
      have h2 := congrArg (toFunℝ Γ₀ k) (hx g)
      rwa [MonoidHom.comp_apply, commRepℝ_apply, toFunℝ_smulMap, toFunℝ_ofLevel,
        coe_levelInclℝ] at h2
    let F : ModularForm Γ.carrier k :=
      { toFun := ⇑f
        slash_action_eq' := fun δ hδ ↦ by
          simpa only [inv_inv] using key ⟨δ⁻¹, Γ.carrier.inv_mem hδ⟩
        holo' := f.holo'
        bdd_at_cusps' := fun {c} hc ↦
          f.bdd_at_cusps' ((Subgroup.Commensurable.isCusp_iff hcomm).mpr hc) }
    refine ⟨F, ?_⟩
    have e1 : restrictSubgroupℝ hΓΛ' F = restrictSubgroupℝ hΛΛ' f := by ext z; rfl
    rw [← ofLevelℝ_restrict Γ₀ k hΓΛ' F, e1]
    exact ofLevelℝ_restrict Γ₀ k hΛΛ' f

/-- **Corollary.** `ModularForm Γ.carrier k` is `ℝ`-linearly isomorphic to the `Γ.carrier`-invariants
of the limit, via `ofLevelℝ`. -/
noncomputable def ofLevelℝInvariantsEquiv (Γ : CommIndex Γ₀ (fun _ ↦ True)) :
    ModularForm Γ.carrier k ≃ₗ[ℝ]
      Representation.invariants ((commRepℝ Γ₀ k).comp (levelInclℝ Γ₀ Γ)) :=
  (LinearEquiv.ofInjective (ofLevelℝ Γ₀ k Γ) (ofLevelℝ_injective Γ₀ k Γ)).trans
    (LinearEquiv.ofEq _ _ (range_ofLevelℝ_eq_invariants Γ₀ k Γ))

end ModularFormCommensurableReal
