/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMBilinear
import ModularCurves.WeilPairing.KMIndependence
import ModularCurves.Picard.PicComparison

/-!
# Existence of a normalised Katz–Mazur dataset (AP-E1-DS)

`torsionSplittingEval` consumes a *dataset* for the `N`-torsion section `Q`: an invertible
module `M` with `toSkeleton M = κ(Q)`, a trivialising cover `W`, trivialisations `e`, and the
normalisation `hnorm` — the transition cocycle takes the value `1` along the zero section.
This file constructs one for every torsion `Q`:

* `exists_module_kappa` (AP-E1-DS1) — a representative module, invertible, from the skeleton.
* `exists_over_trivialization_of_isInvertible` (AP-E1-DS2) — an `.over`-form trivialising
  cover, through `restrictIsoOfPullbackIso` and `overTrivializationOfRestrictIso`.
* `nonempty_pullback_zero_iso_unit_of_kappa` (AP-E1-DS3) — the rigidification `0^*M ≅ 𝒪_T`,
  from `kappa_mem_ker`. This is what makes a *normalised* trivialisation possible at all.
* the two-family cover construction (AP-E1-DS4–DS6): near the zero image, correct each chart
  by the `π`-pullback of its comparison unit with the rigidification; off the zero image —
  an open set, because the zero section is a closed immersion — the normalisation condition
  is vacuous.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

section Scale

variable {X : Scheme.{u}}

/-- Sections of the structure sheaf commute (the same local instance
`Picard/InvertibleSheafCocycle.lean` declares for the scalar-endomorphism ring
equivalence). -/
local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- Composition of scalar endomorphisms of the over-site unit is multiplication of the
scalars. -/
private theorem overUnitScalarEnd_comp (U : X.Opens) (a b : Γ(X, U)) :
    SheafOfModules.overUnitScalarEnd X.ringCatSheaf U a ≫
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U b =
    SheafOfModules.overUnitScalarEnd X.ringCatSheaf U (a * b) :=
  ((End.mul_def _ _).symm.trans
    ((SheafOfModules.overUnitScalarEndRingHom X.ringCatSheaf U).map_mul b a).symm).trans
    (congrArg (SheafOfModules.overUnitScalarEnd X.ringCatSheaf U) (mul_comm b a))

/-- The scalar endomorphism of `1` is the identity. -/
private theorem overUnitScalarEnd_one (U : X.Opens) :
    SheafOfModules.overUnitScalarEnd X.ringCatSheaf U (1 : Γ(X, U)) =
      𝟙 (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  ((SheafOfModules.overUnitScalarEndRingHom X.ringCatSheaf U).map_one).trans End.one_def

/-- **(AP-E1-DS5)** Multiplication by a unit section, as an automorphism of the over-site
unit module. Rescaling a trivialisation composes with this. -/
noncomputable def overUnitScalarIso (U : X.Opens) (c : Γ(X, U)ˣ) :
    _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U) where
  hom := SheafOfModules.overUnitScalarEnd X.ringCatSheaf U (c : Γ(X, U))
  inv := SheafOfModules.overUnitScalarEnd X.ringCatSheaf U ((c⁻¹ : Γ(X, U)ˣ) : Γ(X, U))
  hom_inv_id := by
    rw [overUnitScalarEnd_comp, Units.mul_inv, overUnitScalarEnd_one]
  inv_hom_id := by
    rw [overUnitScalarEnd_comp, Units.inv_mul, overUnitScalarEnd_one]

/-- Restricting a rescaled trivialisation is rescaling the restriction by the restricted
unit. -/
theorem restrictOverTrivialization_trans_scalarIso {M : X.Modules} {U V : X.Opens}
    (hVU : V ≤ U)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) (c : Γ(X, U)ˣ) :
    SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U
        (e ≪≫ overUnitScalarIso U c) (Over.mk (homOfLE hVU)) =
      SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
          (Over.mk (homOfLE hVU)) ≪≫
        overUnitScalarIso V (Scheme.resUnit hVU c) := by
  apply Iso.ext
  have h := restrictOverTrivialization_hom_eq_comp_scalar M hVU e
    (e ≪≫ overUnitScalarIso U c) (c : Γ(X, U)) (by rw [Iso.trans_hom]; rfl)
  exact h

/-- **(AP-E1-DS5, the cocycle effect)** Rescaling two trivialisations rescales their
transition unit by the ratio of the scalars:
`ttu(a·σ(c_a), b·σ(c_b)) = ttu(a,b) · c_a⁻¹ · c_b`. -/
theorem trivializationTransitionUnit_trans_scalarIso {M : X.Modules} (U : X.Opens)
    (a b : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (ca cb : Γ(X, U)ˣ) :
    trivializationTransitionUnit U (a ≪≫ overUnitScalarIso U ca)
        (b ≪≫ overUnitScalarIso U cb) =
      trivializationTransitionUnit U a b * ca⁻¹ * cb := by
  apply Units.ext
  letI : ∀ W, IsMulCommutative (X.ringCatSheaf.obj.obj W) := fun W ↦ by
    change IsMulCommutative (X.presheaf.obj W)
    exact IsMulCommutative.of_comm fun x y ↦ mul_comm x y
  apply (SheafOfModules.overUnitScalarEndRingEquiv X.ringCatSheaf U).injective
  have hL : (SheafOfModules.overUnitScalarEndRingEquiv X.ringCatSheaf U)
      (trivializationTransitionUnit U (a ≪≫ overUnitScalarIso U ca)
        (b ≪≫ overUnitScalarIso U cb) : Γ(X, U)) =
      (a ≪≫ overUnitScalarIso U ca).inv ≫ (b ≪≫ overUnitScalarIso U cb).hom :=
    overUnitScalarEnd_transitionUnit U _ _
  have hR : (SheafOfModules.overUnitScalarEndRingEquiv X.ringCatSheaf U)
      (trivializationTransitionUnit U a b : Γ(X, U)) = a.inv ≫ b.hom :=
    overUnitScalarEnd_transitionUnit U a b
  rw [hL]
  have hcomp : (a ≪≫ overUnitScalarIso U ca).inv ≫ (b ≪≫ overUnitScalarIso U cb).hom =
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
        ((((ca⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) *
          (trivializationTransitionUnit U a b : Γ(X, U))) * (cb : Γ(X, U))) := by
    rw [Iso.trans_inv, Iso.trans_hom]
    have hmid : a.inv ≫ b.hom = SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
        (trivializationTransitionUnit U a b : Γ(X, U)) := hR.symm
    show (overUnitScalarIso U ca).inv ≫ a.inv ≫ b.hom ≫ (overUnitScalarIso U cb).hom = _
    rw [show a.inv ≫ b.hom ≫ (overUnitScalarIso U cb).hom =
        (a.inv ≫ b.hom) ≫ (overUnitScalarIso U cb).hom from by simp only [Category.assoc],
      hmid]
    show SheafOfModules.overUnitScalarEnd X.ringCatSheaf U ((ca⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) ≫
        SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
          (trivializationTransitionUnit U a b : Γ(X, U)) ≫
        SheafOfModules.overUnitScalarEnd X.ringCatSheaf U ((cb : Γ(X, U)ˣ) : Γ(X, U)) = _
    rw [overUnitScalarEnd_comp, overUnitScalarEnd_comp, mul_assoc]
  rw [hcomp]
  show SheafOfModules.overUnitScalarEnd X.ringCatSheaf U _ =
    SheafOfModules.overUnitScalarEnd X.ringCatSheaf U _
  refine congrArg _ ?_
  simp only [Units.val_mul]
  ring

end Scale

section Dataset

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)

/-- **(AP-E1-DS1)** Every `κ(Q)` is represented by an invertible module: take the skeleton
representative; it is invertible because its class is a unit of the skeleton monoid. -/
theorem exists_module_kappa (Q : (E.baseChange t).Point (𝟙 T)) :
    ∃ M : (pullback E.π t).Modules,
      (letI := Scheme.Modules.monoidalCategory (pullback E.π t);
        (kappa E hsm t Q).val = toSkeleton M) ∧ IsInvertible M := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  refine ⟨(fromSkeleton (pullback E.π t).Modules).obj (kappa E hsm t Q).val, ?_, ?_⟩
  · exact (toSkeleton_fromSkeleton_obj _).symm
  · refine isInvertible_of_isUnit_toSkeleton ?_
    rw [toSkeleton_fromSkeleton_obj]
    exact (kappa E hsm t Q).isUnit

/-- **(AP-E1-DS2)** A cover-locally trivial module admits trivialisations in the `.over`
form `transitionUnitOfCover` consumes, over the same cover. -/
theorem exists_over_trivialization_of_isInvertible {X : Scheme.{u}} {M : X.Modules}
    (hM : IsInvertible M) :
    ∃ (ι : Type u) (W : ι → X.Opens) (_ : iSup W = ⊤),
      ∀ i, Nonempty (M.over (W i) ≅
        _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i))) := by
  obtain ⟨ι, U, hU, htriv⟩ := hM
  refine ⟨ι, U, hU, fun i => ?_⟩
  obtain ⟨e⟩ := htriv i
  exact ⟨overTrivializationOfRestrictIso M (U i) (restrictIsoOfPullbackIso M (U i) e)⟩

/-- **(AP-E1-DS3)** The rigidification: a module representing `κ(Q)` pulls back trivially
along the zero section, because `κ` lands in the relative Picard group (`kappa_mem_ker`). -/
theorem nonempty_pullback_zero_iso_unit_of_kappa (Q : (E.baseChange t).Point (𝟙 T))
    (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M) :
    Nonempty ((Scheme.Modules.pullback (baseChangeZero E.π E.zero E.zero_π t)).obj M ≅
      unitObj T) := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  letI := Scheme.Modules.monoidalCategory T
  have hM' : (kappa E hsm t Q).val = toSkeleton M := hM
  have hval := congrArg Units.val (kappa_mem_ker E hsm t Q)
  rw [Scheme.Pic.map_val] at hval
  refine toSkeleton_eq_toSkeleton_iff.mp ?_
  have h1 : toSkeleton ((Scheme.Modules.pullback (baseChangeZero E.π E.zero E.zero_π t)).obj M) =
      (Scheme.Modules.pullback (baseChangeZero E.π E.zero E.zero_π t)).mapSkeleton.obj
        (toSkeleton M) :=
    (Functor.mapSkeleton_obj_toSkeleton _ M).symm
  rw [h1, ← hM', hval]
  exact (Units.val_one).trans toSkeleton_unitObj.symm

/-- The two `d`-atoms of the zero-trace cancellation: `(a·b⁻¹)·a⁻¹·b = 1`. -/
private theorem mul_inv_mul_inv_cancel {G : Type*} [CommGroup G] (a b : G) :
    a * b⁻¹ * a⁻¹ * b = 1 := by
  rw [show a * b⁻¹ * a⁻¹ * b = (a * a⁻¹) * (b⁻¹ * b) from by ac_rfl,
    mul_inv_cancel, inv_mul_cancel, one_mul]

/-- Evaluation along the identity is the identity. -/
private theorem sectionEval_id {Y : Scheme.{u}} (U : Y.Opens) (u : Γ(Y, U)ˣ) :
    sectionEval (𝟙 Y) U u = u :=
  Units.ext rfl

/-- Sections over an open contained in `⊥` form a trivial ring. -/
private theorem sections_subsingleton_of_le_bot {Y : Scheme.{u}} {V : Y.Opens}
    (hV : V ≤ ⊥) : Subsingleton Γ(Y, V) := by
  obtain rfl : V = ⊥ := le_bot_iff.mp hV
  infer_instance

/-- **(AP-E1-DS6)** For every section `Q` of the base-changed curve there is a complete
normalised Katz–Mazur dataset: an invertible module representing `κ(Q)`, a trivialising
cover, and trivialisations whose transition cocycle is `1` along the zero section.

Construction: pick any trivialised representative (`DS1`, `DS2`). The zero-pulled cocycle is
a coboundary `d_i · d_j⁻¹` — this is AP-D5's engine at `f := ` the zero section, with
`kappa_mem_ker` as the Picard input (`DS3`/`DS4`). Then re-cover by two families: near the
zero image use `Z i := W i ⊓ π⁻¹(0⁻¹ W i)` and rescale the chart by `π^#(d_i)` (`DS5`), which
makes the zero-trace of the cocycle `(d_i d_j⁻¹) · d_i⁻¹ · d_j = 1`; off the zero image — an
open set, because the zero section is a closed immersion (a section of the separated
`pullback.snd`) — use `O i := W i ⊓ (im 0)ᶜ`, where the zero-trace is empty and the
condition is vacuous (`Subsingleton Γ(T, ⊥)`). -/
theorem exists_normalized_dataset (Q : (E.baseChange t).Point (𝟙 T)) :
    ∃ (M : (pullback E.π t).Modules)
      (_ : letI := Scheme.Modules.monoidalCategory (pullback E.π t);
        (kappa E hsm t Q).val = toSkeleton M)
      (ι : Type u) (W : ι → (pullback E.π t).Opens) (_ : iSup W = ⊤)
      (e : ∀ i, M.over (W i) ≅
        _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i))),
      ∀ i j, transitionUnitOfCover M W e i j ∈
        sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j) := by
  classical
  set z : T ⟶ pullback E.π t := baseChangeZero E.π E.zero E.zero_π t with hz
  obtain ⟨M, hM, hInv⟩ := exists_module_kappa E hsm t Q
  obtain ⟨ι, W₀, hW₀, htriv⟩ := exists_over_trivialization_of_isInvertible hInv
  have e₀ : ∀ i, M.over (W₀ i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W₀ i)) :=
    fun i => (htriv i).some
  obtain ⟨d, hd⟩ := exists_transitionUnit_eq_mul_inv_of_picMap_eq_one z
    (kappa E hsm t Q) M hM (kappa_mem_ker E hsm t Q) W₀ e₀
  -- the zero image is closed
  haveI hsep : IsSeparated (pullback.snd E.π t) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π t ‹_›
  haveI hzci : IsClosedImmersion z := by
    refine MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated)
      z (pullback.snd E.π t) hsep ?_
    rw [hz, baseChangeZero_snd]
    infer_instance
  set Zc : (pullback E.π t).Opens :=
    ⟨(Set.range z.base)ᶜ, (z.isClosedEmbedding.isClosed_range).isOpen_compl⟩ with hZc
  have hzZc : z ⁻¹ᵁ Zc ≤ ⊥ := by
    intro x hx
    exact absurd (Set.mem_range_self x) hx
  -- the two-family cover
  set W : ι ⊕ ι → (pullback E.π t).Opens := Sum.elim
    (fun i => W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))
    (fun i => W₀ i ⊓ Zc) with hWdef
  have hW : iSup W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hmem : x ∈ Set.range z.base
    · obtain ⟨y, rfl⟩ := hmem
      have hy : z.base y ∈ (⊤ : (pullback E.π t).Opens) := trivial
      rw [← hW₀, TopologicalSpace.Opens.mem_iSup] at hy
      obtain ⟨i, hi⟩ := hy
      refine ⟨Sum.inl i, hi, ?_⟩
      show (pullback.snd E.π t).base (z.base y) ∈ (z ⁻¹ᵁ W₀ i)
      have hzy : (pullback.snd E.π t).base (z.base y) = y := by
        have := congrArg (fun m : T ⟶ T => m.base y) (baseChangeZero_snd E.π E.zero
          E.zero_π t)
        simpa using this
      rw [hzy]
      exact hi
    · have hx : x ∈ (⊤ : (pullback E.π t).Opens) := trivial
      rw [← hW₀, TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨i, hi⟩ := hx
      exact ⟨Sum.inr i, hi, hmem⟩
  -- the trivialisation family: rescaled near the zero image, plain off it
  set cZ : ∀ i : ι, Γ(pullback E.π t, W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))ˣ :=
    fun i => unitPullback (pullback.snd E.π t) (z ⁻¹ᵁ W₀ i)
      (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) inf_le_right (d i) with hcZ
  set e : ∀ a : ι ⊕ ι, M.over (W a) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W a)) :=
    fun a => match a with
      | .inl i => SheafOfModules.restrictOverTrivialization
          (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
          (Over.mk (homOfLE (inf_le_left :
            W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i) ≤ W₀ i))) ≪≫
        overUnitScalarIso _ (cZ i)
      | .inr i => SheafOfModules.restrictOverTrivialization
          (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
          (Over.mk (homOfLE (inf_le_left : W₀ i ⊓ Zc ≤ W₀ i))) with hedef
  refine ⟨M, hM, ι ⊕ ι, W, hW, e, ?_⟩
  intro a b
  rw [mem_sectionUnits_iff]
  -- any overlap touching the off-zero family has empty zero-trace
  have hvac : ∀ (V : (pullback E.π t).Opens), V ≤ Zc →
      ∀ (u : Γ(pullback E.π t, V)ˣ), sectionEval z V u = 1 := by
    intro V hV u
    haveI := sections_subsingleton_of_le_bot
      ((z.preimage_mono hV).trans hzZc)
    exact Units.ext (Subsingleton.elim _ _)
  cases a with
  | inr i =>
      exact hvac _ (le_trans inf_le_left inf_le_right) _
  | inl i =>
      cases b with
      | inr j =>
          exact hvac _ (le_trans inf_le_right inf_le_right) _
      | inl j =>
          -- the genuine case: both charts rescaled near the zero image
          have hzπ : z ≫ pullback.snd E.π t = 𝟙 T := by
            rw [hz]; exact baseChangeZero_snd E.π E.zero E.zero_π t
          have hVle : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
              (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤ W₀ i ⊓ W₀ j :=
            inf_le_inf inf_le_left inf_le_left
          -- the unscaled cocycle over the refined overlap reads the original one
          have hAB : trivializationTransitionUnit
              ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i) ≤ W₀ i))))
                (Over.mk (homOfLE (inf_le_left :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)))))
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ j) (e₀ j)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j) ≤ W₀ j))))
                (Over.mk (homOfLE (inf_le_right :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))))) =
              Scheme.resUnit hVle (transitionUnitOfCover M W₀ e₀ i j) :=
            (congrArg₂ (trivializationTransitionUnit _)
              (restrictOverTrivialization_comp_eq M (e₀ i)
                (inf_le_left) (inf_le_left) hVle (inf_le_left : W₀ i ⊓ W₀ j ≤ W₀ i))
              (restrictOverTrivialization_comp_eq M (e₀ j)
                (inf_le_right) (inf_le_left) hVle
                (inf_le_right : W₀ i ⊓ W₀ j ≤ W₀ j))).trans
            (trivializationTransitionUnit_restrict (M := M) hVle
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
                (Over.mk (homOfLE (inf_le_left : W₀ i ⊓ W₀ j ≤ W₀ i))))
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M (W₀ j) (e₀ j)
                (Over.mk (homOfLE (inf_le_right : W₀ i ⊓ W₀ j ≤ W₀ j)))))
          -- split the scalar corrections off
          have hco : trivializationTransitionUnit
              ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M
                (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i))
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i) ≤ W₀ i))) ≪≫
                  overUnitScalarIso (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) (cZ i))
                (Over.mk (homOfLE inf_le_left)))
              (SheafOfModules.restrictOverTrivialization
                (pullback E.π t).ringCatSheaf M
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ j) (e₀ j)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j) ≤ W₀ j))) ≪≫
                  overUnitScalarIso (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) (cZ j))
                (Over.mk (homOfLE inf_le_right))) =
              Scheme.resUnit hVle (transitionUnitOfCover M W₀ e₀ i j) *
                (Scheme.resUnit (inf_le_left :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) (cZ i))⁻¹ *
                Scheme.resUnit (inf_le_right :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) (cZ j) :=
            (congrArg₂ (trivializationTransitionUnit _)
              (restrictOverTrivialization_trans_scalarIso inf_le_left
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ i) (e₀ i)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i) ≤ W₀ i)))) (cZ i))
              (restrictOverTrivialization_trans_scalarIso inf_le_right
                (SheafOfModules.restrictOverTrivialization
                  (pullback E.π t).ringCatSheaf M (W₀ j) (e₀ j)
                  (Over.mk (homOfLE (inf_le_left :
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j) ≤ W₀ j)))) (cZ j))).trans
            ((trivializationTransitionUnit_trans_scalarIso _ _ _ _ _).trans
              (congrArg (fun x => x *
                (Scheme.resUnit (inf_le_left :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) (cZ i))⁻¹ *
                Scheme.resUnit (inf_le_right :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) (cZ j)) hAB))
          -- evaluate along the zero section and cancel the `d`-atoms
          have hEB : ∀ (k : ι) (hk : (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
              (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                W₀ k ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ k))
              (p' : z ⁻¹ᵁ ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j))) ≤
                (𝟙 T) ⁻¹ᵁ (z ⁻¹ᵁ W₀ k)),
              sectionEval z ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))
                (Scheme.resUnit hk (cZ k)) =
              Scheme.resUnit p' (d k) := by
            intro k hk p'
            refine ((congrArg (sectionEval z _)
              (resUnit_unitPullback (pullback.snd E.π t) inf_le_right hk (d k))).trans
              (sectionEval_unitPullback (pullback.snd E.π t) z
                (hk.trans inf_le_right) (d k))).trans ?_
            refine (resUnit_sectionEval_congr hzπ (z ⁻¹ᵁ W₀ k) (d k)
              (z.preimage_mono (hk.trans inf_le_right)) p').trans ?_
            exact congrArg (Scheme.resUnit p') (sectionEval_id (z ⁻¹ᵁ W₀ k) (d k))
          have hkey : sectionEval z
              ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))
              (Scheme.resUnit hVle (transitionUnitOfCover M W₀ e₀ i j) *
                (Scheme.resUnit (inf_le_left :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) (cZ i))⁻¹ *
                Scheme.resUnit (inf_le_right :
                  (W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
                    (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) ≤
                    W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)) (cZ j)) = 1 := by
            rw [map_mul, map_mul, map_inv]
            rw [show sectionEval z _ (Scheme.resUnit hVle
                (transitionUnitOfCover M W₀ e₀ i j)) =
              Scheme.resUnit (z.preimage_mono hVle)
                (Scheme.resUnit (z.preimage_mono (inf_le_left : W₀ i ⊓ W₀ j ≤ W₀ i))
                    (d i) *
                  (Scheme.resUnit (z.preimage_mono (inf_le_right : W₀ i ⊓ W₀ j ≤ W₀ j))
                    (d j))⁻¹) from
              (sectionEval_resUnit z hVle _).trans
                (congrArg (Scheme.resUnit (z.preimage_mono hVle)) (hd i j))]
            rw [hEB i inf_le_left
                ((z.preimage_mono (inf_le_left)).trans (z.preimage_mono (inf_le_left))),
              hEB j inf_le_right
                ((z.preimage_mono (inf_le_right)).trans (z.preimage_mono (inf_le_left))),
              map_mul, map_inv, Scheme.resUnit_resUnit, Scheme.resUnit_resUnit]
            exact mul_inv_mul_inv_cancel _ _
          exact (congrArg (sectionEval z
            ((W₀ i ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ i)) ⊓
              (W₀ j ⊓ (pullback.snd E.π t) ⁻¹ᵁ (z ⁻¹ᵁ W₀ j)))) hco).trans hkey

end Dataset

end ModularCurves
