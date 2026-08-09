/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMDataset
import ModularCurves.EllipticCurve.TorsionUnramifiedFibre

/-!
# The canonical Katz–Mazur pairing and the universal torsion points (AP-E1)

With existence of a normalised dataset (`WeilPairing/KMDataset.lean`) and independence of the
value from the dataset (`WeilPairing/KMIndependence.lean`) in hand, KM's `h(P)` becomes a
genuine function of the pair of torsion sections:

* `weilPairingKM E hsm t N P hP Q hQ : Γ(T, 𝒪_T^×)` — `torsionSplittingEval` at a chosen
  dataset; `weilPairingKM_eq_torsionSplittingEval` re-reads it through **any** dataset, which
  is the working form for every law.
* `weilPairingKM_pow_eq_one` — the `μ_N` landing, and `weilPairingKM_add_left` — additivity in
  `P`, both immediate from the AP-D7 theorems at a chosen dataset.
* `univTorsionFst`/`univTorsionSnd` — the tautological pair of `N`-torsion points over the
  universal base `E[N] ×_S E[N]`, which the Yoneda step (`WeilPairing/Basic.lean`,
  `weilPairing`) evaluates the pairing at.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

section Canonical

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)

/-- **(AP-E1, the canonical value)** The Katz–Mazur Weil pairing of two `N`-torsion sections,
as a unit of the base: `torsionSplittingEval` at a dataset chosen by
`exists_normalized_dataset`. By `torsionSplittingEval_congr_dataset` the choice is invisible:
see `weilPairingKM_eq_torsionSplittingEval`. -/
noncomputable def weilPairingKM (N : ℕ)
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N) : Γ(T, ⊤)ˣ :=
  let h := exists_normalized_dataset E hsm t Q
  torsionSplittingEval E hsm t N Q hQ h.choose h.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
    P hP

/-- **The spec of `weilPairingKM`**: it computes as `torsionSplittingEval` of *every*
normalised dataset for `Q`. This is the bridge every law walks across. -/
theorem weilPairingKM_eq_torsionSplittingEval (N : ℕ)
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)
    (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j)) :
    weilPairingKM E hsm t N P hP Q hQ =
      torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP :=
  torsionSplittingEval_congr_dataset E hsm t N Q hQ
    (exists_normalized_dataset E hsm t Q).choose M
    (exists_normalized_dataset E hsm t Q).choose_spec.choose hM
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose W hW
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose e
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec hnorm P hP

/-- **(KM p. 89)** The canonical pairing lands in `μ_N`. -/
theorem weilPairingKM_pow_eq_one (N : ℕ)
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N) :
    weilPairingKM E hsm t N P hP Q hQ ^ N = 1 :=
  torsionSplittingEval_pow_eq_one E hsm t N Q hQ
    (exists_normalized_dataset E hsm t Q).choose (exists_normalized_dataset E hsm t Q).choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
    P hP

/-- **(KM p. 89)** The canonical pairing is additive in the first variable. -/
theorem weilPairingKM_add_left (N : ℕ)
    (P P' : (E.baseChange t).Point (𝟙 T))
    (hP : P ∈ torsionPoints E t N) (hP' : P' ∈ torsionPoints E t N)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N) :
    weilPairingKM E hsm t N (P + P') (add_mem hP hP') Q hQ =
      weilPairingKM E hsm t N P hP Q hQ * weilPairingKM E hsm t N P' hP' Q hQ :=
  torsionSplittingEval_add E hsm t N Q hQ
    (exists_normalized_dataset E hsm t Q).choose (exists_normalized_dataset E hsm t Q).choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
    P P' hP hP'

/-- **(KM p. 89)** The canonical pairing is trivial at `P = 0`. -/
theorem weilPairingKM_zero_left (N : ℕ)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N) :
    weilPairingKM E hsm t N 0 (zero_mem _) Q hQ = 1 :=
  torsionSplittingEval_zero E hsm t N Q hQ
    (exists_normalized_dataset E hsm t Q).choose (exists_normalized_dataset E hsm t Q).choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

end Canonical

section Universal

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ)

/-- The structure morphism of the torsion scheme factors the structure morphism of the
curve: `torsionι ≫ π = torsionπ`. -/
theorem torsionι_π : E.torsionι N ≫ E.π = E.torsionπ N := by
  have hcond : E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero :=
    pullback.condition
  have h2 := congrArg (fun m => m ≫ E.π) hcond
  simpa [E.mulByHom_π, E.zero_π] using h2

/-- The universal base of pairs of `N`-torsion points, with its structure morphism
`pullback.fst ≫ torsionπ`. The first tautological point: the first projection, read as an
`N`-torsion section of the base-changed curve. -/
noncomputable def univTorsionFst :
    (E.baseChange (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)).Point
      (𝟙 (pullback (E.torsionπ N) (E.torsionπ N))) :=
  ⟨pullback.lift (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N)
      (𝟙 (pullback (E.torsionπ N) (E.torsionπ N)))
      (by rw [Category.assoc, torsionι_π, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

/-- The second tautological point: the second projection. Its structure identity uses the
universal base's `pullback.condition`. -/
noncomputable def univTorsionSnd :
    (E.baseChange (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)).Point
      (𝟙 (pullback (E.torsionπ N) (E.torsionπ N))) :=
  ⟨pullback.lift (pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N)
      (𝟙 (pullback (E.torsionπ N) (E.torsionπ N)))
      (by rw [Category.assoc, torsionι_π, Category.id_comp, pullback.condition]),
    pullback.lift_snd _ _ _⟩

/-- Any section of the base-changed curve whose first leg is killed by `[N]` on `E` is an
`N`-torsion point. This is the membership route for both tautological points. -/
theorem mem_torsionPoints_of_comp_mulByHom {T : Scheme.{u}} {t : T ⟶ S}
    (P : (E.baseChange t).Point (𝟙 T))
    (h : (P.1 : T ⟶ pullback E.π t) ≫ pullback.fst E.π t ≫ E.mulByHom (N : ℤ) =
      ((𝟙 T ≫ t) ≫ E.zero)) :
    P ∈ torsionPoints E t N := by
  rw [mem_torsionPoints]
  have hy : ((N : ℤ) • (EllipticCurve.Point.baseChangeEquiv E t (𝟙 T)) P : E.Point (𝟙 T ≫ t)) = 0 := by
    refine (E.smul_eq_zero_iff_comp_mulByHom (𝟙 T ≫ t) N _).mpr ?_
    rw [EllipticCurve.Point.baseChangeEquiv_apply_coe]
    rw [Category.assoc] at h
    exact h
  have := congrArg (EllipticCurve.Point.baseChangeEquiv E t (𝟙 T)).symm
    ((map_zsmul (EllipticCurve.Point.baseChangeEquiv E t (𝟙 T)) (N : ℤ) P).trans hy)
  rwa [AddEquiv.symm_apply_apply, map_zero] at this

/-- The first tautological point is `N`-torsion: its first leg is `fst ≫ torsionι`, and the
torsion scheme's defining square kills it. -/
theorem univTorsionFst_mem :
    univTorsionFst E N ∈
      torsionPoints E (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) N := by
  refine mem_torsionPoints_of_comp_mulByHom E N _ ?_
  show pullback.lift _ _ _ ≫ pullback.fst E.π _ ≫ E.mulByHom (N : ℤ) = _
  rw [pullback.lift_fst_assoc, Category.assoc,
    show E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero from
      pullback.condition,
    Category.id_comp, ← Category.assoc]

/-- The second tautological point is `N`-torsion. -/
theorem univTorsionSnd_mem :
    univTorsionSnd E N ∈
      torsionPoints E (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) N := by
  refine mem_torsionPoints_of_comp_mulByHom E N _ ?_
  show pullback.lift _ _ _ ≫ pullback.fst E.π _ ≫ E.mulByHom (N : ℤ) = _
  rw [pullback.lift_fst_assoc, Category.assoc,
    show E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero from
      pullback.condition,
    Category.id_comp, ← Category.assoc, ← pullback.condition]

end Universal

section RestrictBase

variable {S : Scheme.{u}} (E : EllipticCurve S) {T T' : Scheme.{u}}

/-- Transport of a point along an equality of structure morphisms — the additive
equivalence `subst` gives. -/
noncomputable def pointCongr {σ σ' : T ⟶ S} (h : σ = σ') : E.Point σ ≃+ E.Point σ' := by
  subst h; exact AddEquiv.refl _

@[simp] theorem pointCongr_apply_coe {σ σ' : T ⟶ S} (h : σ = σ') (P : E.Point σ) :
    ((pointCongr E h P : E.Point σ') : T ⟶ E.E) = (P : T ⟶ E.E) := by
  subst h; rfl

/-- **(AP-E1-NAT0)** Restriction of a section of the base-changed curve along `g : T' ⟶ T`,
in the `pullback E.π t` presentation: transport to `E.Point`, restrict, transport back. -/
noncomputable def restrictBase (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t')
    (P : (E.baseChange t).Point (𝟙 T)) : (E.baseChange t').Point (𝟙 T') :=
  (EllipticCurve.Point.baseChangeEquiv E t' (𝟙 T')).symm
    (pointCongr E (by simp only [Category.id_comp]; exact hg)
      (EllipticCurve.Point.restrict E g
        (EllipticCurve.Point.baseChangeEquiv E t (𝟙 T) P)))

/-- `restrictBase` is additive: each of its three constituents is. -/
theorem restrictBase_add (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t')
    (P Q : (E.baseChange t).Point (𝟙 T)) :
    restrictBase E t g hg (P + Q) =
      restrictBase E t g hg P + restrictBase E t g hg Q := by
  unfold restrictBase
  rw [map_add, EllipticCurve.restrict_add, map_add, map_add]

/-- `restrictBase` sends zero to zero. -/
theorem restrictBase_zero (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') :
    restrictBase E t g hg 0 = 0 := by
  unfold restrictBase
  rw [map_zero, EllipticCurve.restrict_zero, map_zero, map_zero]

/-- `restrictBase`, bundled. -/
noncomputable def restrictBaseHom (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T)
    (hg : g ≫ t = t') :
    (E.baseChange t).Point (𝟙 T) →+ (E.baseChange t').Point (𝟙 T') where
  toFun := restrictBase E t g hg
  map_zero' := restrictBase_zero E t g hg
  map_add' := restrictBase_add E t g hg

/-- **(AP-E1-NAT0)** Restriction preserves `N`-torsion. -/
theorem restrictBase_mem_torsionPoints (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T)
    (hg : g ≫ t = t') {N : ℕ} {P : (E.baseChange t).Point (𝟙 T)}
    (hP : P ∈ torsionPoints E t N) :
    restrictBase E t g hg P ∈ torsionPoints E t' N := by
  rw [mem_torsionPoints] at hP ⊢
  have h := (restrictBaseHom E t g hg).map_zsmul (N : ℤ) P
  rw [hP, map_zero] at h
  exact h.symm

/-- The first leg of `baseChangeMap`. -/
theorem baseChangeMap_fst (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') :
    baseChangeMap E.π g hg ≫ pullback.fst E.π t = pullback.fst E.π t' := by
  simp only [baseChangeMap]
  rw [pullback.lift_fst]
  exact Category.comp_id _

/-- The second leg of `baseChangeMap`. -/
theorem baseChangeMap_snd (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') :
    baseChangeMap E.π g hg ≫ pullback.snd E.π t = pullback.snd E.π t' ≫ g := by
  simp only [baseChangeMap]
  exact pullback.lift_snd _ _ _

/-- The first leg of the restricted point: restriction of the first leg. -/
theorem restrictBase_coe_fst (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t')
    (Q : (E.baseChange t).Point (𝟙 T)) :
    ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫ pullback.fst E.π t' =
      g ≫ ((Q.1 : T ⟶ pullback E.π t) ≫ pullback.fst E.π t) :=
  (pullback.lift_fst _ _ _).trans (pointCongr_apply_coe E _ _)

/-- The restricted point's leg through `baseChangeMap`: the naturality square commutes. -/
theorem restrictBase_comp_baseChangeMap (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T)
    (hg : g ≫ t = t') (Q : (E.baseChange t).Point (𝟙 T)) :
    ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫ baseChangeMap E.π g hg =
      g ≫ (Q.1 : T ⟶ pullback E.π t) := by
  apply pullback.hom_ext
  · calc (((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫
          baseChangeMap E.π g hg) ≫ pullback.fst E.π t
        = ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫
            (baseChangeMap E.π g hg ≫ pullback.fst E.π t) := Category.assoc _ _ _
      _ = ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫ pullback.fst E.π t' :=
          congrArg _ (baseChangeMap_fst E t g hg)
      _ = g ≫ ((Q.1 : T ⟶ pullback E.π t) ≫ pullback.fst E.π t) :=
          restrictBase_coe_fst E t g hg Q
      _ = (g ≫ (Q.1 : T ⟶ pullback E.π t)) ≫ pullback.fst E.π t :=
          (Category.assoc _ _ _).symm
  · calc (((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫
          baseChangeMap E.π g hg) ≫ pullback.snd E.π t
        = ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫
            (baseChangeMap E.π g hg ≫ pullback.snd E.π t) := Category.assoc _ _ _
      _ = ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫
            (pullback.snd E.π t' ≫ g) := congrArg _ (baseChangeMap_snd E t g hg)
      _ = (((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫
            pullback.snd E.π t') ≫ g := (Category.assoc _ _ _).symm
      _ = 𝟙 T' ≫ g := congrArg (· ≫ g) (restrictBase E t g hg Q).2
      _ = g := Category.id_comp g
      _ = g ≫ 𝟙 T := (Category.comp_id g).symm
      _ = g ≫ ((Q.1 : T ⟶ pullback E.π t) ≫ pullback.snd E.π t) := congrArg _ Q.2.symm
      _ = (g ≫ (Q.1 : T ⟶ pullback E.π t)) ≫ pullback.snd E.π t :=
          (Category.assoc _ _ _).symm

/-- **(AP-E1-NAT1, step 1)** The restriction square of a section along `g : T' ⟶ T` is
cartesian. -/
theorem isPullback_restrictBase (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t')
    (Q : (E.baseChange t).Point (𝟙 T)) :
    IsPullback ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') g
      (baseChangeMap E.π g hg) (Q.1 : T ⟶ pullback E.π t) := by
  have hb' : ∀ s : Limits.PullbackCone (baseChangeMap E.π g hg)
      (Q.1 : T ⟶ pullback E.π t),
      (s.fst ≫ pullback.snd E.π t') ≫ g = s.snd := by
    intro s
    calc (s.fst ≫ pullback.snd E.π t') ≫ g
        = s.fst ≫ (pullback.snd E.π t' ≫ g) := Category.assoc _ _ _
      _ = s.fst ≫ (baseChangeMap E.π g hg ≫ pullback.snd E.π t) :=
          congrArg _ (baseChangeMap_snd E t g hg).symm
      _ = (s.fst ≫ baseChangeMap E.π g hg) ≫ pullback.snd E.π t :=
          (Category.assoc _ _ _).symm
      _ = (s.snd ≫ (Q.1 : T ⟶ pullback E.π t)) ≫ pullback.snd E.π t :=
          congrArg (· ≫ pullback.snd E.π t) s.condition
      _ = s.snd ≫ ((Q.1 : T ⟶ pullback E.π t) ≫ pullback.snd E.π t) :=
          Category.assoc _ _ _
      _ = s.snd ≫ 𝟙 T := congrArg _ Q.2
      _ = s.snd := Category.comp_id _
  refine IsPullback.of_isLimit'
    ⟨restrictBase_comp_baseChangeMap E t g hg Q⟩ ?_
  refine Limits.PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ pullback.snd E.π t')
    (fun s => ?_) (fun s => hb' s) (fun s m hm₁ hm₂ => ?_)
  · apply pullback.hom_ext
    · calc ((s.fst ≫ pullback.snd E.π t') ≫
            ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t')) ≫ pullback.fst E.π t'
          = (s.fst ≫ pullback.snd E.π t') ≫
              (((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫
                pullback.fst E.π t') := Category.assoc _ _ _
        _ = (s.fst ≫ pullback.snd E.π t') ≫
              (g ≫ ((Q.1 : T ⟶ pullback E.π t) ≫ pullback.fst E.π t)) :=
            congrArg _ (restrictBase_coe_fst E t g hg Q)
        _ = ((s.fst ≫ pullback.snd E.π t') ≫ g) ≫
              ((Q.1 : T ⟶ pullback E.π t) ≫ pullback.fst E.π t) :=
            (Category.assoc _ _ _).symm
        _ = s.snd ≫ ((Q.1 : T ⟶ pullback E.π t) ≫ pullback.fst E.π t) :=
            congrArg (· ≫ _) (hb' s)
        _ = (s.snd ≫ (Q.1 : T ⟶ pullback E.π t)) ≫ pullback.fst E.π t :=
            (Category.assoc _ _ _).symm
        _ = (s.fst ≫ baseChangeMap E.π g hg) ≫ pullback.fst E.π t :=
            congrArg (· ≫ pullback.fst E.π t) s.condition.symm
        _ = s.fst ≫ (baseChangeMap E.π g hg ≫ pullback.fst E.π t) :=
            Category.assoc _ _ _
        _ = s.fst ≫ pullback.fst E.π t' := congrArg _ (baseChangeMap_fst E t g hg)
    · calc ((s.fst ≫ pullback.snd E.π t') ≫
            ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t')) ≫ pullback.snd E.π t'
          = (s.fst ≫ pullback.snd E.π t') ≫
              (((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫
                pullback.snd E.π t') := Category.assoc _ _ _
        _ = (s.fst ≫ pullback.snd E.π t') ≫ 𝟙 T' :=
            congrArg _ (restrictBase E t g hg Q).2
        _ = s.fst ≫ pullback.snd E.π t' := Category.comp_id _
  · calc m = m ≫ 𝟙 T' := (Category.comp_id m).symm
      _ = m ≫ (((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t') ≫
            pullback.snd E.π t') := congrArg _ (restrictBase E t g hg Q).2.symm
      _ = (m ≫ ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t')) ≫
            pullback.snd E.π t' := (Category.assoc _ _ _).symm
      _ = s.fst ≫ pullback.snd E.π t' := congrArg (· ≫ pullback.snd E.π t') hm₁

/-- **(AP-E1-NAT1, step 2)** The kernel of the restricted section is the comap of the
kernel along `baseChangeMap` — the ideal-sheaf half of `κ`-naturality. Mirrors
`RelEffCartierDiv.ker_sectionBaseChange`, with the cartesian square supplied by
`isPullback_restrictBase`. -/
theorem ker_restrictBase (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t')
    (Q : (E.baseChange t).Point (𝟙 T)) [IsSeparated E.π] :
    ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t').ker =
      (Scheme.Hom.ker (Q.1 : T ⟶ pullback E.π t)).comap (baseChangeMap E.π g hg) := by
  haveI hsep : IsSeparated (pullback.snd E.π t) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π t ‹_›
  haveI : IsClosedImmersion (Q.1 : T ⟶ pullback E.π t) :=
    RelEffCartierDiv.SectionsIdeal.isClosedImmersion Q.2
  rw [← (isPullback_restrictBase E t g hg Q).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (Q.1 : T ⟶ pullback E.π t)
    (baseChangeMap E.π g hg)

/-- **(AP-E1-NAT1, step 3)** The class of a section divisor commutes with base change
along `g : T' ⟶ T`: `Pic(g_E)([𝒪(Q)]) = [𝒪(Q|_{T'})]`. The ideal-module comparison is
`nonempty_pullback_idealModule` at `f := baseChangeMap` with both local-principality sides
from `sectionDivisor_isOfficial`, glued by `ker_restrictBase`. -/
theorem sectionCls_restrictBase (hsm : SmoothOfRelativeDimension 1 E.π)
    [IsSeparated E.π] (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t')
    (Q : (E.baseChange t).Point (𝟙 T)) :
    Scheme.Pic.map (baseChangeMap E.π g hg) (sectionCls E hsm t Q.1 Q.2) =
      sectionCls E hsm t' ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t')
        (restrictBase E t g hg Q).2 := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  letI := Scheme.Modules.monoidalCategory (pullback E.π t')
  haveI hsepT : IsSeparated (pullback.snd E.π t) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π t ‹_›
  haveI hsepT' : IsSeparated (pullback.snd E.π t') :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π t' ‹_›
  have hsmT : SmoothOfRelativeDimension 1 (pullback.snd E.π t) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.π t hsm
  have hsmT' : SmoothOfRelativeDimension 1 (pullback.snd E.π t') :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.π t' hsm
  -- the ideal-module comparison along `baseChangeMap`
  have hJ : ∀ c : ↥(pullback E.π t), ∃ V : (pullback E.π t).affineOpens, c ∈ V.1 ∧
      ∃ f : Γ(pullback E.π t, V.1),
        (Scheme.Hom.ker (Q.1 : T ⟶ pullback E.π t)).ideal V = Ideal.span {f} ∧
          f ∈ nonZeroDivisors Γ(pullback E.π t, V.1) :=
    (RelEffCartierDiv.sectionDivisor_isOfficial hsmT
      (Q.1 : T ⟶ pullback E.π t) Q.2).locallyPrincipal
  have hJ' : ∀ c : ↥(pullback E.π t'), ∃ V : (pullback E.π t').affineOpens, c ∈ V.1 ∧
      ∃ f : Γ(pullback E.π t', V.1),
        ((Scheme.Hom.ker (Q.1 : T ⟶ pullback E.π t)).comap
          (baseChangeMap E.π g hg)).ideal V = Ideal.span {f} ∧
          f ∈ nonZeroDivisors Γ(pullback E.π t', V.1) := by
    rw [← ker_restrictBase E t g hg Q]
    exact (RelEffCartierDiv.sectionDivisor_isOfficial hsmT'
      ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t')
      (restrictBase E t g hg Q).2).locallyPrincipal
  obtain ⟨eiso⟩ := nonempty_pullback_idealModule (baseChangeMap E.π g hg)
    (Scheme.Hom.ker (Q.1 : T ⟶ pullback E.π t)) hJ hJ'
  have hcore : Scheme.Pic.map (baseChangeMap E.π g hg)
      (((RelEffCartierDiv.sectionDivisor (pullback.snd E.π t)
          (Q.1 : T ⟶ pullback E.π t) Q.2).isInvertible_idealModule
        (RelEffCartierDiv.sectionDivisor_isOfficial hsmT _ Q.2)).isUnit_toSkeleton.unit) =
      ((RelEffCartierDiv.sectionDivisor (pullback.snd E.π t')
          ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t')
          (restrictBase E t g hg Q).2).isInvertible_idealModule
        (RelEffCartierDiv.sectionDivisor_isOfficial hsmT' _
          (restrictBase E t g hg Q).2)).isUnit_toSkeleton.unit := by
    refine Units.ext ?_
    refine (Scheme.Pic.map_val (baseChangeMap E.π g hg) _).trans ?_
    refine (congrArg (Scheme.Modules.pullback (baseChangeMap E.π g hg)).mapSkeleton.obj
      (IsUnit.unit_spec _)).trans ?_
    refine (Functor.mapSkeleton_obj_toSkeleton _ _).trans ?_
    refine (toSkeleton_eq_toSkeleton_iff.mpr
      ⟨eiso ≪≫ eqToIso (congrArg Scheme.Modules.idealModule (ker_restrictBase E t g hg Q).symm)⟩).trans ?_
    exact (IsUnit.unit_spec _).symm
  refine Eq.trans (map_inv (Scheme.Pic.map (baseChangeMap E.π g hg)) _) ?_
  exact congrArg (·⁻¹) hcore

/-- `sectionCls` depends on the section only through its underlying morphism. -/
theorem sectionCls_congr (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (t : T ⟶ S) {P P' : T ⟶ pullback E.π t}
    (hP : P ≫ pullback.snd E.π t = 𝟙 T) (hP' : P' ≫ pullback.snd E.π t = 𝟙 T)
    (h : P = P') : sectionCls E hsm t P hP = sectionCls E hsm t P' hP' := by
  subst h; rfl

/-- **(AP-E1-NAT1, step 4)** The zero class commutes with base change: restrict the
zero *point* and identify it with the base-changed zero section. -/
theorem zeroCls_restrictBase (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') :
    Scheme.Pic.map (baseChangeMap E.π g hg) (zeroCls E hsm t) = zeroCls E hsm t' := by
  have hzval : ((0 : (E.baseChange t).Point (𝟙 T)).1 : T ⟶ pullback E.π t) =
      baseChangeZero E.π E.zero E.zero_π t :=
    ((E.baseChange t).point_zero_val (𝟙 T)).trans (Category.id_comp _)
  have hzval' : ((0 : (E.baseChange t').Point (𝟙 T')).1 : T' ⟶ pullback E.π t') =
      baseChangeZero E.π E.zero E.zero_π t' :=
    ((E.baseChange t').point_zero_val (𝟙 T')).trans (Category.id_comp _)
  calc Scheme.Pic.map (baseChangeMap E.π g hg) (zeroCls E hsm t)
      = Scheme.Pic.map (baseChangeMap E.π g hg)
          (sectionCls E hsm t ((0 : (E.baseChange t).Point (𝟙 T)).1 : T ⟶ pullback E.π t)
            (0 : (E.baseChange t).Point (𝟙 T)).2) :=
        congrArg _ (sectionCls_congr E hsm t _ _ hzval.symm)
    _ = sectionCls E hsm t'
          ((restrictBase E t g hg (0 : (E.baseChange t).Point (𝟙 T))).1 :
            T' ⟶ pullback E.π t')
          (restrictBase E t g hg (0 : (E.baseChange t).Point (𝟙 T))).2 :=
        sectionCls_restrictBase E hsm t g hg 0
    _ = sectionCls E hsm t' ((0 : (E.baseChange t').Point (𝟙 T')).1 : T' ⟶ pullback E.π t')
          (0 : (E.baseChange t').Point (𝟙 T')).2 :=
        congrArg (fun P : (E.baseChange t').Point (𝟙 T') =>
          sectionCls E hsm t' (P.1 : T' ⟶ pullback E.π t') P.2)
          (restrictBase_zero E t g hg)
    _ = zeroCls E hsm t' := sectionCls_congr E hsm t' _ _ hzval'

/-- **(AP-E1-NAT1, COMPLETE)** `κ` commutes with base change:
`Pic(g_E)(κ_T(Q)) = κ_{T'}(Q|_{T'})`. Assembled from `sectionCls_restrictBase`,
`zeroCls_restrictBase`, and the `MonoidHom` algebra of the kernel-projection
`picRelProj`, using the two commuting squares of `baseChangeMap` with the structure and
zero sections. -/
theorem kappa_restrictBase (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t')
    (Q : (E.baseChange t).Point (𝟙 T)) :
    Scheme.Pic.map (baseChangeMap E.π g hg) (kappa E hsm t Q) =
      kappa E hsm t' (restrictBase E t g hg Q) := by
  have hval : ∀ (x : Scheme.Pic (pullback E.π t)),
      ((picRelProj E.π E.zero E.zero_π t x : picRel E.π E.zero E.zero_π t) :
        Scheme.Pic (pullback E.π t)) =
      x * (Scheme.Pic.map (pullback.snd E.π t)
        (Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) x))⁻¹ := fun _ => rfl
  have hval' : ∀ (x : Scheme.Pic (pullback E.π t')),
      ((picRelProj E.π E.zero E.zero_π t' x : picRel E.π E.zero E.zero_π t') :
        Scheme.Pic (pullback E.π t')) =
      x * (Scheme.Pic.map (pullback.snd E.π t')
        (Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t') x))⁻¹ := fun _ => rfl
  set x := sectionCls E hsm t Q.1 Q.2 * (zeroCls E hsm t)⁻¹ with hx
  set x' := sectionCls E hsm t'
      ((restrictBase E t g hg Q).1 : T' ⟶ pullback E.π t')
      (restrictBase E t g hg Q).2 * (zeroCls E hsm t')⁻¹ with hx'
  have hratio : Scheme.Pic.map (baseChangeMap E.π g hg) x = x' := by
    rw [hx, hx', map_mul, map_inv, sectionCls_restrictBase E hsm t g hg Q,
      zeroCls_restrictBase E hsm t g hg]
  have hsq1 : ∀ y, Scheme.Pic.map (baseChangeMap E.π g hg)
      (Scheme.Pic.map (pullback.snd E.π t) y) =
      Scheme.Pic.map (pullback.snd E.π t') (Scheme.Pic.map g y) := by
    intro y
    calc Scheme.Pic.map (baseChangeMap E.π g hg) (Scheme.Pic.map (pullback.snd E.π t) y)
        = Scheme.Pic.map (baseChangeMap E.π g hg ≫ pullback.snd E.π t) y := by
          rw [Scheme.Pic.map_comp]; rfl
      _ = Scheme.Pic.map (pullback.snd E.π t' ≫ g) y := by
          rw [baseChangeMap_snd E t g hg]
      _ = Scheme.Pic.map (pullback.snd E.π t') (Scheme.Pic.map g y) := by
          rw [Scheme.Pic.map_comp]; rfl
  have hsq2 : ∀ y, Scheme.Pic.map g
      (Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) y) =
      Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t')
        (Scheme.Pic.map (baseChangeMap E.π g hg) y) := by
    intro y
    calc Scheme.Pic.map g (Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) y)
        = Scheme.Pic.map (g ≫ baseChangeZero E.π E.zero E.zero_π t) y := by
          rw [Scheme.Pic.map_comp]; rfl
      _ = Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t' ≫
            baseChangeMap E.π g hg) y := by
          rw [baseChangeZero_baseChangeMap]
      _ = Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t')
            (Scheme.Pic.map (baseChangeMap E.π g hg) y) := by
          rw [Scheme.Pic.map_comp]; rfl
  calc Scheme.Pic.map (baseChangeMap E.π g hg) (kappa E hsm t Q)
      = Scheme.Pic.map (baseChangeMap E.π g hg)
          (x * (Scheme.Pic.map (pullback.snd E.π t)
            (Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) x))⁻¹) :=
        congrArg _ ((kappa_eq_picRelProj E hsm t Q).trans (hval x))
    _ = Scheme.Pic.map (baseChangeMap E.π g hg) x *
          (Scheme.Pic.map (baseChangeMap E.π g hg)
            (Scheme.Pic.map (pullback.snd E.π t)
              (Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t) x)))⁻¹ := by
        rw [map_mul, map_inv]
    _ = x' * (Scheme.Pic.map (pullback.snd E.π t')
          (Scheme.Pic.map (baseChangeZero E.π E.zero E.zero_π t') x'))⁻¹ := by
        simp only [hsq1, hsq2, hratio]
    _ = kappa E hsm t' (restrictBase E t g hg Q) :=
        ((kappa_eq_picRelProj E hsm t' (restrictBase E t g hg Q)).trans (hval' x')).symm

/-- `[N]` commutes with `baseChangeMap`: multiplication is defined over the base. -/
theorem baseChangeMap_mulByN (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t')
    (N : ℕ) :
    baseChangeMap E.π g hg ≫ mulByN E t N = mulByN E t' N ≫ baseChangeMap E.π g hg := by
  apply pullback.hom_ext
  · calc (baseChangeMap E.π g hg ≫ mulByN E t N) ≫ pullback.fst E.π t
        = baseChangeMap E.π g hg ≫ (mulByN E t N ≫ pullback.fst E.π t) :=
          Category.assoc _ _ _
      _ = baseChangeMap E.π g hg ≫ (pullback.fst E.π t ≫ E.mulByHom (N : ℤ)) :=
          congrArg _ (E.mulByHom_baseChange_fst t (N : ℤ))
      _ = (baseChangeMap E.π g hg ≫ pullback.fst E.π t) ≫ E.mulByHom (N : ℤ) :=
          (Category.assoc _ _ _).symm
      _ = pullback.fst E.π t' ≫ E.mulByHom (N : ℤ) :=
          congrArg (· ≫ E.mulByHom (N : ℤ)) (baseChangeMap_fst E t g hg)
      _ = mulByN E t' N ≫ pullback.fst E.π t' :=
          (E.mulByHom_baseChange_fst t' (N : ℤ)).symm
      _ = mulByN E t' N ≫ (baseChangeMap E.π g hg ≫ pullback.fst E.π t) :=
          congrArg _ (baseChangeMap_fst E t g hg).symm
      _ = (mulByN E t' N ≫ baseChangeMap E.π g hg) ≫ pullback.fst E.π t :=
          (Category.assoc _ _ _).symm
  · calc (baseChangeMap E.π g hg ≫ mulByN E t N) ≫ pullback.snd E.π t
        = baseChangeMap E.π g hg ≫ (mulByN E t N ≫ pullback.snd E.π t) :=
          Category.assoc _ _ _
      _ = baseChangeMap E.π g hg ≫ pullback.snd E.π t :=
          congrArg _ (E.mulByHom_baseChange_snd t (N : ℤ))
      _ = pullback.snd E.π t' ≫ g := baseChangeMap_snd E t g hg
      _ = (mulByN E t' N ≫ pullback.snd E.π t') ≫ g :=
          congrArg (· ≫ g) (E.mulByHom_baseChange_snd t' (N : ℤ)).symm
      _ = mulByN E t' N ≫ (pullback.snd E.π t' ≫ g) := Category.assoc _ _ _
      _ = mulByN E t' N ≫ (baseChangeMap E.π g hg ≫ pullback.snd E.π t) :=
          congrArg _ (baseChangeMap_snd E t g hg).symm
      _ = (mulByN E t' N ≫ baseChangeMap E.π g hg) ≫ pullback.snd E.π t :=
          (Category.assoc _ _ _).symm

/-- Evaluation along a composite is the pullback of the evaluation: the `appLE`-normalised
form of `Scheme.Hom.comp_app`. -/
theorem sectionEval_comp {Y : Scheme.{u}} (g : T' ⟶ T) (w : T ⟶ Y) (V : Y.Opens)
    (u : Γ(Y, V)ˣ) :
    sectionEval (g ≫ w) V u =
      unitPullback g (w ⁻¹ᵁ V) ((g ≫ w) ⁻¹ᵁ V) (le_of_eq rfl) (sectionEval w V u) := by
  refine Eq.trans ?_ (map_app_eq_unitPullback g (w ⁻¹ᵁ V) (sectionEval w V u))
  apply Units.ext
  show ((g ≫ w).app V).hom (u : Γ(Y, V)) =
    (g.app (w ⁻¹ᵁ V)).hom ((w.app V).hom (u : Γ(Y, V)))
  rw [Scheme.Hom.comp_app]
  rfl

/-- **(AP-E1-NAT2)** The Katz–Mazur value commutes with base change: the pulled-back
dataset — module `(baseChangeMap)^* M`, cover `baseChangeMap ⁻¹ᵁ W`, trivialisations
`localPullbackTrivializationT` — computes the `g`-pullback of the value.

The normalised splitting over `T` pulls back to one over `T'`: normalisation transports
through `0' ≫ baseChangeMap = g ≫ 0` and splitting through
`baseChangeMap ≫ [N] = [N'] ≫ baseChangeMap`, both absorbed by `unitPullback_congr`; the
value identification reads `P' ≫ baseChangeMap = g ≫ P`. The proof-irrelevant dataset
hypotheses `hM'`, `hnorm'` are arguments (any derivation gives the same value). -/
theorem torsionSplittingEval_restrictBase (hsm : SmoothOfRelativeDimension 1 E.π)
    [IsSeparated E.π] (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') (N : ℕ)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)
    (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M)
    {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N)
    (hM' : letI := Scheme.Modules.monoidalCategory (pullback E.π t')
      (kappa E hsm t' (restrictBase E t g hg Q)).val =
        toSkeleton ((Scheme.Modules.pullback (baseChangeMap E.π g hg)).obj M))
    (hnorm' : ∀ i j, transitionUnitOfCover
        ((Scheme.Modules.pullback (baseChangeMap E.π g hg)).obj M)
        (fun i => baseChangeMap E.π g hg ⁻¹ᵁ W i)
        (fun i => localPullbackTrivializationT (baseChangeMap E.π g hg) M (W i) (e i)) i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t')
        (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j)) :
    torsionSplittingEval E hsm t' N (restrictBase E t g hg Q)
        (restrictBase_mem_torsionPoints E t g hg hQ)
        ((Scheme.Modules.pullback (baseChangeMap E.π g hg)).obj M) hM'
        (fun i => baseChangeMap E.π g hg ⁻¹ᵁ W i)
        ((baseChangeMap E.π g hg).iSup_preimage_eq_top hW)
        (fun i => localPullbackTrivializationT (baseChangeMap E.π g hg) M (W i) (e i))
        hnorm'
        (restrictBase E t g hg P) (restrictBase_mem_torsionPoints E t g hg hP) =
      unitPullback g ⊤ ⊤ le_rfl
        (torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP) := by
  obtain ⟨h, hn, hsplit⟩ :=
    exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints E hsm t N Q hQ M hM W hW e
      hnorm
  -- the preimage path: `[N']⁻¹(bcm⁻¹ W i) = bcm⁻¹([N]⁻¹ W i)`
  have hpatheq : ∀ i, mulByN E t' N ⁻¹ᵁ (baseChangeMap E.π g hg ⁻¹ᵁ W i) =
      baseChangeMap E.π g hg ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) := by
    intro i
    have hcomm := baseChangeMap_mulByN E t g hg N
    calc mulByN E t' N ⁻¹ᵁ (baseChangeMap E.π g hg ⁻¹ᵁ W i)
        = (mulByN E t' N ≫ baseChangeMap E.π g hg) ⁻¹ᵁ W i := rfl
      _ = (baseChangeMap E.π g hg ≫ mulByN E t N) ⁻¹ᵁ W i := by rw [hcomm]
      _ = baseChangeMap E.π g hg ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) := rfl
  have hpath : ∀ i, mulByN E t' N ⁻¹ᵁ (baseChangeMap E.π g hg ⁻¹ᵁ W i) ≤
      baseChangeMap E.π g hg ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) := fun i => le_of_eq (hpatheq i)
  -- the pulled splitting units
  set h' : ∀ i, Γ(pullback E.π t',
      mulByN E t' N ⁻¹ᵁ (baseChangeMap E.π g hg ⁻¹ᵁ W i))ˣ :=
    fun i => unitPullback (baseChangeMap E.π g hg) (mulByN E t N ⁻¹ᵁ W i)
      (mulByN E t' N ⁻¹ᵁ (baseChangeMap E.π g hg ⁻¹ᵁ W i)) (hpath i) (h i) with hh'
  have hzcomp : baseChangeZero E.π E.zero E.zero_π t' ≫ baseChangeMap E.π g hg =
      g ≫ baseChangeZero E.π E.zero E.zero_π t :=
    baseChangeZero_baseChangeMap E.π E.zero E.zero_π g hg
  refine (eq_torsionSplittingEval E hsm t' N (restrictBase E t g hg Q)
    (restrictBase_mem_torsionPoints E t g hg hQ) _ hM' _
    ((baseChangeMap E.π g hg).iSup_preimage_eq_top hW) _ hnorm'
    (restrictBase E t g hg P) (restrictBase_mem_torsionPoints E t g hg hP) h'
    (fun i => ?_) (fun i j => ?_) (fun i => ?_)).symm
  · -- the pulled splitting is normalised along the zero section of `T'`
    rw [mem_sectionUnits_iff, hh']
    refine (sectionEval_unitPullback (baseChangeMap E.π g hg)
      (baseChangeZero E.π E.zero E.zero_π t') (hpath i) (h i)).trans ?_
    refine ((resUnit_sectionEval_congr hzcomp (mulByN E t N ⁻¹ᵁ W i) (h i)
      ((baseChangeZero E.π E.zero E.zero_π t').preimage_mono (hpath i))
      (by rw [← hzcomp]
          exact (baseChangeZero E.π E.zero E.zero_π t').preimage_mono (hpath i))).trans
      ?_)
    refine (congrArg _ ((sectionEval_comp g (baseChangeZero E.π E.zero E.zero_π t)
      (mulByN E t N ⁻¹ᵁ W i) (h i)).trans ?_)).trans (map_one _)
    rw [show sectionEval (baseChangeZero E.π E.zero E.zero_π t)
        (mulByN E t N ⁻¹ᵁ W i) (h i) = 1 from hn i]
    exact map_one _
  · -- the pulled splitting splits the pulled cocycle
    sorry
  · -- the value along the restricted point reads the `g`-pullback of the value
    sorry

end RestrictBase

end ModularCurves
