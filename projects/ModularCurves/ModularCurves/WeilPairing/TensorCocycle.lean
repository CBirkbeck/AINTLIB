/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PullbackTensorSection
import ModularCurves.Picard.PicComparison
import ModularCurves.WeilPairing.KMPatching

/-!
# The transition cocycle is monoidal (the AP-D7 brick)

`Picard/InvertibleSheafCocycle.lean` proves that `trivializationTransitionUnit` is reflexive,
symmetric and transitive, and compatible with restriction and pullback, but says nothing about
`⊗`. This file supplies the missing multiplicativity, in the form actually needed by
`WeilPairing/KMBilinear.lean`: **the transition cocycle of a tensor power is the power of the
transition cocycle**, hence a Picard class killed by `N` has `f_{i,j}^N` a coboundary.

## The device: frame sections rather than a monoidal comparison

Transporting a trivialization through a monoidal comparison
`(M ⊗ M').over U ≅ M.over U ⊗ M'.over U` would leave a coherence obligation — that the transport
commutes with `restrictOverTrivialization` — which is exactly what the cocycle identity on
`W i ⊓ W j` needs. That obligation is avoided here by working with the *generating section* of a
trivialization instead of the trivialization itself:

* `IsFrame M U σ` — `σ : Γ(M, U)` is the coefficient-`1` section of some trivialization of `M`
  over `U`. Restriction-stability (`IsFrame.restrict`) is naturality of the coefficient, and the
  cocycle appears as the ratio of two frames (`frame_eq_transitionUnit_smul`).
* `tensorSection` (`EllipticCurve/PoleSheaf.lean`) is *already* natural
  (`tensorSection_restrict`) and bilinear (`tensorSection_smul_left/right`), and
  `overTrivializationOfRestrictIso_tensorSection_coefficient`
  (`EllipticCurve/PullbackTensorSection.lean`) says the coefficient of a pure tensor is the
  product of the coefficients. So `IsFrame.tensor` needs no new coherence at all.

## Main results

* `IsFrame` and its API: `IsFrame.restrict`, `frame_eq_transitionUnit_smul`, `IsFrame.tensor`.
* `exists_frame_pow` — the tensor power `M^{⊗k}` carries frames over the `W i` whose ratios are
  `f_{i,j}^k`, together with the Picard class `[M]^k`.
* `exists_pow_transitionUnitOfCover_split_of_toSkeleton_pow_eq_one` — **the brick**: if
  `[M]^N = 1` in the skeleton then `f_{i,j}^N` is a coboundary on the `W i`. No covering
  hypothesis is needed.

The units in the conclusion are *not* obtainable from the coboundary relation alone (the zero
family satisfies it): they come from `IsFrame`, i.e. from the frames being generators.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme.Modules ModularCurves.SheafOfModules

namespace ModularCurves

local instance instIsMulCommutativeRingCatSheafObj (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- The monoidal structure on `X.Modules`, activated locally exactly as
`EllipticCurve/PoleSheaf.lean` activates it (same `def`, so the two files' `⊗` agree). -/
noncomputable local instance instMonoidalCategoryModules (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {X : Scheme.{u}}

/-! ## Frame sections -/

/-- The coefficient of a module section in an over-site trivialization. -/
noncomputable def frameCoeff (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (m : Γ(M, U)) : Γ(X, U) :=
  e.hom.val.app (.op (Over.mk (𝟙 U))) m

theorem evalSection_eq_frameCoeff (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (m : Γ(M, U)) :
    evalSection X.ringCatSheaf M U e.hom m = frameCoeff M U e m := by
  refine (evalSection_eq X.ringCatSheaf M U e.hom m).trans ?_
  congr 1
  rw [op_id, M.val.map_id]
  rfl

theorem frameCoeff_eq_evalSection (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (m : Γ(M, U)) :
    frameCoeff M U e m = evalSection X.ringCatSheaf M U e.hom m :=
  (evalSection_eq_frameCoeff M U e m).symm

/-- A section is a **frame** of `M` over `U` when it is the coefficient-`1` section of some
trivialization; equivalently, when it generates `M` over every open inside `U`. -/
def IsFrame (M : X.Modules) (U : X.Opens) (σ : Γ(M, U)) : Prop :=
  ∃ e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U), frameCoeff M U e σ = 1

/-- Every trivialization has a frame: the section of coefficient `1`. -/
theorem isFrame_overTrivializationSection (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    IsFrame M U (overTrivializationSection M U e 1) :=
  ⟨e, overTrivializationSection_coefficient M U e 1⟩

/-- In a trivialization whose frame is `σ`, every section is its coefficient times `σ`. -/
theorem eq_frameCoeff_smul {M : X.Modules} {U : X.Opens}
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) {σ : Γ(M, U)}
    (hσ : frameCoeff M U e σ = 1) (m : Γ(M, U)) :
    m = frameCoeff M U e m • σ := by
  refine (bijective_evalSection_iso X.ringCatSheaf M U e).injective ?_
  rw [evalSection_smul_right, evalSection_eq_frameCoeff, evalSection_eq_frameCoeff, hσ,
    smul_eq_mul, mul_one]

/-- **The cocycle, read on frames.** Two frames of `M` over `U` differ by the transition unit of
the two trivializations that produced them. -/
theorem frame_eq_transitionUnit_smul {M : X.Modules} {U : X.Opens}
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) {σ τ : Γ(M, U)}
    (hσ : frameCoeff M U e σ = 1) (hτ : frameCoeff M U g τ = 1) :
    σ = (trivializationTransitionUnit U e g : Γ(X, U)) • τ := by
  have hcoeff : frameCoeff M U g σ = (trivializationTransitionUnit U e g : Γ(X, U)) := by
    rw [frameCoeff_eq_evalSection, evalSection_factor X.ringCatSheaf M U e g.hom σ,
      ← frameCoeff_eq_evalSection, hσ, mul_one, ← overUnitScalarEnd_transitionUnit U e g,
      ← dualUnitSectionsEquiv_symm_apply X.ringCatSheaf U, Equiv.apply_symm_apply]
  exact (eq_frameCoeff_smul g hτ σ).trans (congrArg (· • τ) hcoeff)

/-- The coefficient of a restricted section in the restricted trivialization is the restriction
of the coefficient. -/
theorem frameCoeff_restrict (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (m : Γ(M, U)) :
    frameCoeff M V (restrictOverTrivialization X.ringCatSheaf M U e (Over.mk (homOfLE h)))
        (M.val.map (homOfLE h).op m) =
      (X.presheaf.map (homOfLE h).op).hom (frameCoeff M U e m) := by
  rw [frameCoeff_eq_evalSection, frameCoeff_eq_evalSection]
  exact evalSection_naturality X.ringCatSheaf M (homOfLE h).op e.hom m

/-- Frames restrict to frames. -/
theorem IsFrame.restrict {M : X.Modules} {U V : X.Opens} {σ : Γ(M, U)}
    (hσ : IsFrame M U σ) (h : V ≤ U) : IsFrame M V (M.val.map (homOfLE h).op σ) := by
  obtain ⟨e, he⟩ := hσ
  exact ⟨restrictOverTrivialization X.ringCatSheaf M U e (Over.mk (homOfLE h)),
    (frameCoeff_restrict M h e σ).trans ((congrArg (X.presheaf.map (homOfLE h).op).hom he).trans
      (map_one _))⟩

/-! ## The tensor brick -/

/-- Every over-site trivialization comes from a restriction trivialization: the inverse of
`overTrivializationOfRestrictIso`, which is a bijection on isomorphisms because
`(overEquiv U).functor` is fully faithful. -/
noncomputable def restrictIsoOfOverIso (M : X.Modules) (U : X.Opens)
    (f : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme :=
  ((overFunctorEquiv U).app M).symm ≪≫ (overEquiv U).functor.mapIso f ≪≫
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf)

@[simp]
theorem overTrivializationOfRestrictIso_restrictIsoOfOverIso (M : X.Modules) (U : X.Opens)
    (f : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Scheme.Modules.overTrivializationOfRestrictIso M U (restrictIsoOfOverIso M U f) = f := by
  apply Iso.ext
  refine (overEquiv U).fullyFaithfulFunctor.map_injective ?_
  show (overEquiv U).functor.map ((overEquiv U).fullyFaithfulFunctor.preimageIso _).hom = _
  rw [Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
  simp [restrictIsoOfOverIso]

/-- **`trivializationTransitionUnit` is monoidal, in frame form.** The pure tensor of two frames
is a frame of the tensor product. This is the one clause `WeilPairing/KMBilinear.lean` was
missing; combined with `frame_eq_transitionUnit_smul` it says that the transition cocycle of a
tensor product is the product of the transition cocycles.

No coherence obligation arises: `tensorSection` is natural for restriction by construction, and
the coefficient of a pure tensor in the tensor-product frame is the product of the coefficients
(`overTrivializationOfRestrictIso_tensorSection_coefficient`). -/
theorem IsFrame.tensor {M N : X.Modules} {U : X.Opens} {σ : Γ(M, U)} {τ : Γ(N, U)}
    (hσ : IsFrame M U σ) (hτ : IsFrame N U τ) :
    IsFrame (M ⊗ N) U (tensorSection M N U σ τ) := by
  obtain ⟨eM, heM⟩ := hσ
  obtain ⟨eN, heN⟩ := hτ
  refine ⟨Scheme.Modules.overTrivializationOfRestrictIso (M ⊗ N) U
    (restrictMonoidalTensorIso U.ι M N ≪≫
      (restrictIsoOfOverIso M U eM ⊗ᵢ restrictIsoOfOverIso N U eN) ≪≫
      unitObjTensorIso U.toScheme), ?_⟩
  have h := overTrivializationOfRestrictIso_tensorSection_coefficient M N U
    (restrictIsoOfOverIso M U eM) (restrictIsoOfOverIso N U eN) σ τ
  simp only [overTrivializationOfRestrictIso_restrictIsoOfOverIso] at h
  exact h.trans ((congrArg₂ (· * ·) heM heN).trans (mul_one (1 : Γ(X, U))))

/-! ## Tensor powers: the cocycle to the `k`-th power -/

/-- **The transition cocycle of a tensor power is the power of the transition cocycle.** For
every `k` the tensor power `M^{⊗k}` carries frames over the `W i` — a Picard class `[M]^k` —
whose ratios on the overlaps are `f_{i,j}^k`.

The frames are the pure tensor powers of the frames of the `e i`; `IsFrame.tensor` keeps them
frames, `tensorSection_restrict` makes them restrict correctly, and
`tensorSection_smul_left/right` turn the cocycle relation of the factors into its `k`-th power.
Neither a covering hypothesis on `W` nor any normalisation is used. -/
theorem exists_frame_pow (M : X.Modules) {ι : Type*} (W : ι → X.Opens)
    (e : ∀ i, M.over (W i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (W i))) (k : ℕ) :
    ∃ (A : X.Modules) (σ : ∀ i, Γ(A, W i)),
      toSkeleton A = toSkeleton M ^ k ∧ (∀ i, IsFrame A (W i) (σ i)) ∧
        ∀ i j, A.val.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (σ i) =
          ((transitionUnitOfCover M W e i j : Γ(X, W i ⊓ W j)) ^ k) •
            A.val.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (σ j) := by
  induction k with
  | zero =>
    refine ⟨Scheme.Modules.unitObj X, fun i => (1 : Γ(X, W i)), ?_,
      fun i => ⟨Iso.refl _, rfl⟩, fun i j => ?_⟩
    · rw [pow_zero]
      exact Scheme.Modules.toSkeleton_unitObj
    · rw [pow_zero, one_smul]
      exact (map_one (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom).trans
        (map_one (X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom).symm
  | succ k ih =>
    obtain ⟨A, σ, hsk, hfr, hrel⟩ := ih
    refine ⟨A ⊗ M, fun i => tensorSection A M (W i) (σ i)
      (overTrivializationSection M (W i) (e i) 1), ?_, ?_, fun i j => ?_⟩
    · rw [Skeleton.toSkeleton_tensorObj, hsk, pow_succ]
    · exact fun i => (hfr i).tensor (isFrame_overTrivializationSection M (W i) (e i))
    · have hL : W i ⊓ W j ≤ W i := inf_le_left
      have hR : W i ⊓ W j ≤ W j := inf_le_right
      have hμ : M.val.map (homOfLE hL).op (overTrivializationSection M (W i) (e i) 1) =
          (transitionUnitOfCover M W e i j : Γ(X, W i ⊓ W j)) •
            M.val.map (homOfLE hR).op (overTrivializationSection M (W j) (e j) 1) :=
        frame_eq_transitionUnit_smul _ _
          ((frameCoeff_restrict M hL (e i) _).trans
            ((congrArg (X.presheaf.map (homOfLE hL).op).hom
              (overTrivializationSection_coefficient M (W i) (e i) 1)).trans (map_one _)))
          ((frameCoeff_restrict M hR (e j) _).trans
            ((congrArg (X.presheaf.map (homOfLE hR).op).hom
              (overTrivializationSection_coefficient M (W j) (e j) 1)).trans (map_one _)))
      rw [tensorSection_restrict A M hL, tensorSection_restrict A M hR, hrel i j, hμ,
        tensorSection_smul_left, tensorSection_smul_right, smul_smul, ← pow_succ]

/-- **The tensor of two trivialised covers carries frames with the product cocycle** — the
`M ⊗ M'` form of `exists_frame_pow`'s inductive step, needed for bilinearity of the pairing
in the second variable (AP-E3). -/
theorem exists_frame_mul (M M' : X.Modules) {ι : Type*} (W : ι → X.Opens)
    (e : ∀ i, M.over (W i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (W i)))
    (e' : ∀ i, M'.over (W i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (W i))) :
    ∃ σ : ∀ i, Γ(M ⊗ M', W i),
      (∀ i, IsFrame (M ⊗ M') (W i) (σ i)) ∧
        ∀ i j, (M ⊗ M').val.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (σ i) =
          ((transitionUnitOfCover M W e i j : Γ(X, W i ⊓ W j)) *
              (transitionUnitOfCover M' W e' i j : Γ(X, W i ⊓ W j))) •
            (M ⊗ M').val.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (σ j) := by
  refine ⟨fun i => tensorSection M M' (W i) (overTrivializationSection M (W i) (e i) 1)
    (overTrivializationSection M' (W i) (e' i) 1),
    fun i => (isFrame_overTrivializationSection M (W i) (e i)).tensor
      (isFrame_overTrivializationSection M' (W i) (e' i)), fun i j => ?_⟩
  have hL : W i ⊓ W j ≤ W i := inf_le_left
  have hR : W i ⊓ W j ≤ W j := inf_le_right
  have hμ : M.val.map (homOfLE hL).op (overTrivializationSection M (W i) (e i) 1) =
      (transitionUnitOfCover M W e i j : Γ(X, W i ⊓ W j)) •
        M.val.map (homOfLE hR).op (overTrivializationSection M (W j) (e j) 1) :=
    frame_eq_transitionUnit_smul _ _
      ((frameCoeff_restrict M hL (e i) _).trans
        ((congrArg (X.presheaf.map (homOfLE hL).op).hom
          (overTrivializationSection_coefficient M (W i) (e i) 1)).trans (map_one _)))
      ((frameCoeff_restrict M hR (e j) _).trans
        ((congrArg (X.presheaf.map (homOfLE hR).op).hom
          (overTrivializationSection_coefficient M (W j) (e j) 1)).trans (map_one _)))
  have hμ' : M'.val.map (homOfLE hL).op (overTrivializationSection M' (W i) (e' i) 1) =
      (transitionUnitOfCover M' W e' i j : Γ(X, W i ⊓ W j)) •
        M'.val.map (homOfLE hR).op (overTrivializationSection M' (W j) (e' j) 1) :=
    frame_eq_transitionUnit_smul _ _
      ((frameCoeff_restrict M' hL (e' i) _).trans
        ((congrArg (X.presheaf.map (homOfLE hL).op).hom
          (overTrivializationSection_coefficient M' (W i) (e' i) 1)).trans (map_one _)))
      ((frameCoeff_restrict M' hR (e' j) _).trans
        ((congrArg (X.presheaf.map (homOfLE hR).op).hom
          (overTrivializationSection_coefficient M' (W j) (e' j) 1)).trans (map_one _)))
  rw [tensorSection_restrict M M' hL, tensorSection_restrict M M' hR, hμ, hμ',
    tensorSection_smul_left, tensorSection_smul_right, smul_smul]

/-- **Frames with a prescribed ratio cocycle give a trivialising family with that
cocycle** — the converse of `isFrame_overTrivializationSection`, and the glue that turns
`exists_frame_mul` into the tensor *dataset* AP-E3 needs. The cancellation on the frame is
by reading coefficients in the chosen trivialisation. -/
theorem exists_over_trivialization_of_frames (A : X.Modules) {ι : Type*}
    (W : ι → X.Opens) (σ : ∀ i, Γ(A, W i)) (hfr : ∀ i, IsFrame A (W i) (σ i))
    (r : ∀ i j, Γ(X, W i ⊓ W j)ˣ)
    (hrel : ∀ i j, A.val.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (σ i) =
      (r i j : Γ(X, W i ⊓ W j)) •
        A.val.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (σ j)) :
    ∃ e'' : ∀ i, A.over (W i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (W i)),
      ∀ i j, transitionUnitOfCover A W e'' i j = r i j := by
  refine ⟨fun i => (hfr i).choose, fun i j => ?_⟩
  have hL : W i ⊓ W j ≤ W i := inf_le_left
  have hR : W i ⊓ W j ≤ W j := inf_le_right
  have hσi : frameCoeff A (W i ⊓ W j)
      (restrictOverTrivialization X.ringCatSheaf A (W i) (hfr i).choose
        (Over.mk (homOfLE hL))) (A.val.map (homOfLE hL).op (σ i)) = 1 :=
    (frameCoeff_restrict A hL (hfr i).choose _).trans
      ((congrArg (X.presheaf.map (homOfLE hL).op).hom (hfr i).choose_spec).trans
        (map_one _))
  have hσj : frameCoeff A (W i ⊓ W j)
      (restrictOverTrivialization X.ringCatSheaf A (W j) (hfr j).choose
        (Over.mk (homOfLE hR))) (A.val.map (homOfLE hR).op (σ j)) = 1 :=
    (frameCoeff_restrict A hR (hfr j).choose _).trans
      ((congrArg (X.presheaf.map (homOfLE hR).op).hom (hfr j).choose_spec).trans
        (map_one _))
  have hdict : A.val.map (homOfLE hL).op (σ i) =
      (transitionUnitOfCover A W (fun i => (hfr i).choose) i j : Γ(X, W i ⊓ W j)) •
        A.val.map (homOfLE hR).op (σ j) :=
    frame_eq_transitionUnit_smul _ _ hσi hσj
  -- cancel on the frame by reading coefficients in the `j`-restricted trivialisation
  refine Units.ext ?_
  have hread : ∀ (a : Γ(X, W i ⊓ W j)),
      frameCoeff A (W i ⊓ W j)
        (restrictOverTrivialization X.ringCatSheaf A (W j) (hfr j).choose
          (Over.mk (homOfLE hR)))
        (a • A.val.map (homOfLE hR).op (σ j)) = a := by
    intro a
    rw [frameCoeff_eq_evalSection, evalSection_smul_right, ← frameCoeff_eq_evalSection,
      hσj, smul_eq_mul, mul_one]
  calc (transitionUnitOfCover A W (fun i => (hfr i).choose) i j : Γ(X, W i ⊓ W j))
      = frameCoeff A (W i ⊓ W j)
          (restrictOverTrivialization X.ringCatSheaf A (W j) (hfr j).choose
            (Over.mk (homOfLE hR)))
          ((transitionUnitOfCover A W (fun i => (hfr i).choose) i j :
            Γ(X, W i ⊓ W j)) • A.val.map (homOfLE hR).op (σ j)) := (hread _).symm
    _ = frameCoeff A (W i ⊓ W j)
          (restrictOverTrivialization X.ringCatSheaf A (W j) (hfr j).choose
            (Over.mk (homOfLE hR))) (A.val.map (homOfLE hL).op (σ i)) :=
        congrArg _ hdict.symm
    _ = frameCoeff A (W i ⊓ W j)
          (restrictOverTrivialization X.ringCatSheaf A (W j) (hfr j).choose
            (Over.mk (homOfLE hR)))
          ((r i j : Γ(X, W i ⊓ W j)) • A.val.map (homOfLE hR).op (σ j)) :=
        congrArg _ (hrel i j)
    _ = (r i j : Γ(X, W i ⊓ W j)) := hread _

/-! ## The brick: a cocycle whose class is killed by `N` has `f^N` a coboundary -/

/-- The coefficient of a section in a *global* trivialization of `A`. -/
noncomputable def globCoeff {A : X.Modules} (ε : A ≅ Scheme.Modules.unitObj X) (U : X.Opens)
    (m : Γ(A, U)) : Γ(X, U) :=
  ε.hom.val.app (.op U) m

theorem globCoeff_res {A : X.Modules} (ε : A ≅ Scheme.Modules.unitObj X) {U V : X.Opens}
    (h : V ≤ U) (m : Γ(A, U)) :
    Scheme.resLE h (globCoeff ε U m) = globCoeff ε V (A.val.map (homOfLE h).op m) :=
  (PresheafOfModules.naturality_apply ε.hom.val (homOfLE h).op m).symm

theorem globCoeff_smul {A : X.Modules} (ε : A ≅ Scheme.Modules.unitObj X) (U : X.Opens)
    (c : Γ(X, U)) (m : Γ(A, U)) : globCoeff ε U (c • m) = c * globCoeff ε U m :=
  (ε.hom.val.app (.op U)).hom.map_smul c m

theorem globCoeff_surjective {A : X.Modules} (ε : A ≅ Scheme.Modules.unitObj X) (U : X.Opens) :
    Function.Surjective (globCoeff ε U) := by
  intro y
  refine ⟨ε.inv.val.app (.op U) y, ?_⟩
  exact ConcreteCategory.congr_hom
    (congrArg (fun q : Scheme.Modules.unitObj X ⟶ Scheme.Modules.unitObj X =>
      q.val.app (.op U)) ε.inv_hom_id) y

/-- **A frame has an invertible coefficient in any global trivialization.** This — not the
coboundary relation — is where the units of the brick come from. -/
theorem isUnit_globCoeff_of_isFrame {A : X.Modules} (ε : A ≅ Scheme.Modules.unitObj X)
    {U : X.Opens} {σ : Γ(A, U)} (hσ : IsFrame A U σ) : IsUnit (globCoeff ε U σ) := by
  obtain ⟨f, hf⟩ := hσ
  obtain ⟨m, hm⟩ := globCoeff_surjective ε U 1
  rw [eq_frameCoeff_smul f hf m, globCoeff_smul] at hm
  exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans hm)

/-- **The AP-D7 brick.** If the Picard class of `M` is killed by `N`, then the `N`-th power of
the transition cocycle of any family of trivializations is a coboundary:

  `f_{i,j}^N = g_i · g_j⁻¹`   on `W i ⊓ W j`.

No covering hypothesis on `W` and no normalisation along a section are needed.

The `g_i` are the coefficients, in a global trivialization `ε` of `M^{⊗N}`, of the tensor-power
frames of `exists_frame_pow`. That they are **units** is not a consequence of the coboundary
relation — the zero family satisfies that — but of the frames being generators: multiplication
by a frame is bijective on sections, so its `ε`-coefficient generates the unit ideal. -/
theorem exists_pow_transitionUnitOfCover_split_of_toSkeleton_pow_eq_one
    (M : X.Modules) {ι : Type*} (W : ι → X.Opens)
    (e : ∀ i, M.over (W i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (W i))) (N : ℕ)
    (hM : toSkeleton M ^ N = 1) :
    ∃ g : ∀ i, Γ(X, W i)ˣ, ∀ i j,
      transitionUnitOfCover M W e i j ^ N =
        Scheme.resUnit (inf_le_left : W i ⊓ W j ≤ W i) (g i) *
          (Scheme.resUnit (inf_le_right : W i ⊓ W j ≤ W j) (g j))⁻¹ := by
  obtain ⟨A, σ, hsk, hfr, hrel⟩ := exists_frame_pow M W e N
  obtain ⟨ε⟩ : Nonempty (A ≅ Scheme.Modules.unitObj X) :=
    toSkeleton_eq_toSkeleton_iff.mp (hsk.trans (hM.trans Scheme.Modules.toSkeleton_unitObj.symm))
  have hunit : ∀ i, IsUnit (globCoeff ε (W i) (σ i)) :=
    fun i => isUnit_globCoeff_of_isFrame ε (hfr i)
  refine ⟨fun i => (hunit i).unit, fun i j => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Scheme.resUnit_val, Scheme.resUnit_val,
    IsUnit.unit_spec, IsUnit.unit_spec, globCoeff_res, globCoeff_res, hrel i j, globCoeff_smul]

end ModularCurves
