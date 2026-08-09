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

end RestrictBase

end ModularCurves
