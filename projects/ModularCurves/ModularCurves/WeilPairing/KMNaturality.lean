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
  AlgebraicGeometry.Scheme.Modules CategoryTheory.MonoidalCategory

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
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
    have hpullco : transitionUnitOfCover
        ((Scheme.Modules.pullback (baseChangeMap E.π g hg)).obj M)
        (fun i => baseChangeMap E.π g hg ⁻¹ᵁ W i)
        (fun i => localPullbackTrivializationT (baseChangeMap E.π g hg) M (W i) (e i))
        i j =
        Units.map ((baseChangeMap E.π g hg).app (W i ⊓ W j)).hom.toMonoidHom
          (transitionUnitOfCover M W e i j) :=
      (congrArg₂ (trivializationTransitionUnit _)
        (restrict_localPullbackTrivialization (baseChangeMap E.π g hg) M
          (inf_le_left : W i ⊓ W j ≤ W i) (e i))
        (restrict_localPullbackTrivialization (baseChangeMap E.π g hg) M
          (inf_le_right : W i ⊓ W j ≤ W j) (e j))).trans
      (trivializationTransitionUnit_localPullbackTrivialization
        (baseChangeMap E.π g hg) M (W i ⊓ W j) _ _)
    -- typed barrier steps: each equation elaborates in isolation
    have hle : mulByN E t' N ⁻¹ᵁ
        (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j) ≤
        baseChangeMap E.π g hg ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ (W i ⊓ W j)) :=
      inf_le_inf (hpath i) (hpath j)
    have hb1 : Units.map ((mulByN E t' N).app
        (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j)).hom.toMonoidHom
        (Units.map ((baseChangeMap E.π g hg).app (W i ⊓ W j)).hom.toMonoidHom
          (transitionUnitOfCover M W e i j)) =
        unitPullback (mulByN E t' N ≫ baseChangeMap E.π g hg) (W i ⊓ W j)
          (mulByN E t' N ⁻¹ᵁ
            (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j))
          (le_of_eq rfl) (transitionUnitOfCover M W e i j) :=
      (congrArg (Units.map ((mulByN E t' N).app
          (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j)).hom.toMonoidHom)
        (map_app_eq_unitPullback (baseChangeMap E.π g hg) (W i ⊓ W j)
          (transitionUnitOfCover M W e i j))).trans
      ((map_app_eq_unitPullback (mulByN E t' N)
          (baseChangeMap E.π g hg ⁻¹ᵁ (W i ⊓ W j))
          (unitPullback (baseChangeMap E.π g hg) (W i ⊓ W j)
            (baseChangeMap E.π g hg ⁻¹ᵁ (W i ⊓ W j)) le_rfl
            (transitionUnitOfCover M W e i j))).trans
        (unitPullback_unitPullback (mulByN E t' N) (baseChangeMap E.π g hg)
          le_rfl le_rfl (transitionUnitOfCover M W e i j)))
    have hb2 : unitPullback (mulByN E t' N ≫ baseChangeMap E.π g hg) (W i ⊓ W j)
        (mulByN E t' N ⁻¹ᵁ
          (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j))
        (le_of_eq rfl) (transitionUnitOfCover M W e i j) =
        unitPullback (baseChangeMap E.π g hg ≫ mulByN E t N) (W i ⊓ W j)
          (mulByN E t' N ⁻¹ᵁ
            (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j))
          hle (transitionUnitOfCover M W e i j) :=
      unitPullback_congr (baseChangeMap_mulByN E t g hg N).symm (W i ⊓ W j)
        (mulByN E t' N ⁻¹ᵁ
          (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j))
        (le_of_eq rfl) hle (transitionUnitOfCover M W e i j)
    have hb3 : unitPullback (baseChangeMap E.π g hg ≫ mulByN E t N) (W i ⊓ W j)
        (mulByN E t' N ⁻¹ᵁ
          (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j))
        hle (transitionUnitOfCover M W e i j) =
        unitPullback (baseChangeMap E.π g hg) (mulByN E t N ⁻¹ᵁ (W i ⊓ W j))
          (mulByN E t' N ⁻¹ᵁ
            (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j))
          hle (Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
            (transitionUnitOfCover M W e i j)) :=
      ((unitPullback_unitPullback (baseChangeMap E.π g hg) (mulByN E t N)
          le_rfl hle (transitionUnitOfCover M W e i j)).symm).trans
        (congrArg (unitPullback (baseChangeMap E.π g hg)
            (mulByN E t N ⁻¹ᵁ (W i ⊓ W j))
            (mulByN E t' N ⁻¹ᵁ
              (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j)) hle)
          (map_app_eq_unitPullback (mulByN E t N) (W i ⊓ W j)
            (transitionUnitOfCover M W e i j)).symm)
    have hb4 : unitPullback (baseChangeMap E.π g hg) (mulByN E t N ⁻¹ᵁ (W i ⊓ W j))
        (mulByN E t' N ⁻¹ᵁ
          (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j))
        hle (Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
          (transitionUnitOfCover M W e i j)) =
        Scheme.resUnit (inf_le_left : mulByN E t' N ⁻¹ᵁ (baseChangeMap E.π g hg ⁻¹ᵁ W i) ⊓
            mulByN E t' N ⁻¹ᵁ (baseChangeMap E.π g hg ⁻¹ᵁ W j) ≤
            mulByN E t' N ⁻¹ᵁ (baseChangeMap E.π g hg ⁻¹ᵁ W i)) (h' i) *
          (Scheme.resUnit (inf_le_right : mulByN E t' N ⁻¹ᵁ
              (baseChangeMap E.π g hg ⁻¹ᵁ W i) ⊓
              mulByN E t' N ⁻¹ᵁ (baseChangeMap E.π g hg ⁻¹ᵁ W j) ≤
              mulByN E t' N ⁻¹ᵁ (baseChangeMap E.π g hg ⁻¹ᵁ W j)) (h' j))⁻¹ := by
      refine (congrArg (unitPullback (baseChangeMap E.π g hg)
        (mulByN E t N ⁻¹ᵁ (W i ⊓ W j))
        (mulByN E t' N ⁻¹ᵁ
          (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j)) hle)
        (hsplit i j)).trans ?_
      refine ((map_mul _ _ _).trans ?_)
      refine ((congrArg (_ * ·) (map_inv _ _)).trans ?_)
      rw [hh']
      exact congrArg₂ (fun x y => x * y⁻¹)
        ((unitPullback_resUnit (baseChangeMap E.π g hg) _ _ (h i)).trans
          (resUnit_unitPullback (baseChangeMap E.π g hg) (hpath i) _ (h i)).symm)
        ((unitPullback_resUnit (baseChangeMap E.π g hg) _ _ (h j)).trans
          (resUnit_unitPullback (baseChangeMap E.π g hg) (hpath j) _ (h j)).symm)
    exact (congrArg (Units.map ((mulByN E t' N).app
        (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j)).hom.toMonoidHom)
      hpullco).trans (hb1.trans (hb2.trans (hb3.trans hb4)))
  · -- the value along the restricted point reads the `g`-pullback of the value
    have hspec := resUnit_torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP h hn
      hsplit i
    have hPcomp : ((restrictBase E t g hg P).1 : T' ⟶ pullback E.π t') ≫
        baseChangeMap E.π g hg = g ≫ (P.1 : T ⟶ pullback E.π t) :=
      restrictBase_comp_baseChangeMap E t g hg P
    have p2 : ((restrictBase E t g hg P).1 : T' ⟶ pullback E.π t') ⁻¹ᵁ
        (mulByN E t' N ⁻¹ᵁ (baseChangeMap E.π g hg ⁻¹ᵁ W i)) ≤
        (g ≫ (P.1 : T ⟶ pullback E.π t)) ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) := by
      rw [← hPcomp]
      exact ((restrictBase E t g hg P).1 : T' ⟶ pullback E.π t').preimage_mono (hpath i)
    refine Eq.trans ?_ ((sectionEval_unitPullback (baseChangeMap E.π g hg)
      ((restrictBase E t g hg P).1 : T' ⟶ pullback E.π t') (hpath i) (h i)).symm)
    refine Eq.trans ?_ ((resUnit_sectionEval_congr hPcomp (mulByN E t N ⁻¹ᵁ W i) (h i)
      (((restrictBase E t g hg P).1 : T' ⟶ pullback E.π t').preimage_mono (hpath i))
      p2).symm)
    refine Eq.trans ?_ ((congrArg (Scheme.resUnit p2)
      (sectionEval_comp g (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i) (h i))).symm)
    refine Eq.trans ?_ ((resUnit_unitPullback g (le_of_eq rfl) p2
      (sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i) (h i))).symm)
    refine Eq.trans ?_
      ((congrArg (unitPullback g ((P.1 : T ⟶ pullback E.π t) ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i))
        _ _) hspec))
    refine Eq.trans ?_ ((unitPullback_resUnit g le_top _
      (torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP)).symm)
    exact resUnit_unitPullback g le_rfl le_top
      (torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP)

/-- The transition cocycle of the pulled-back dataset is the image of the original
cocycle (the exported form of NAT2's first barrier step). -/
theorem transitionUnitOfCover_localPullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules) {ι : Type*} (W : ι → X.Opens)
    (e : ∀ i, M.over (W i) ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i)))
    (i j : ι) :
    transitionUnitOfCover ((Scheme.Modules.pullback f).obj M) (fun i => f ⁻¹ᵁ W i)
        (fun i => localPullbackTrivializationT f M (W i) (e i)) i j =
      Units.map (f.app (W i ⊓ W j)).hom.toMonoidHom (transitionUnitOfCover M W e i j) :=
  (congrArg₂ (trivializationTransitionUnit _)
    (restrict_localPullbackTrivialization f M (inf_le_left : W i ⊓ W j ≤ W i) (e i))
    (restrict_localPullbackTrivialization f M (inf_le_right : W i ⊓ W j ≤ W j) (e j))).trans
  (trivializationTransitionUnit_localPullbackTrivialization f M (W i ⊓ W j) _ _)

/-- The pulled-back dataset's module represents the restricted `κ`-class: the `hM`-side of
the pulled dataset, from `kappa_restrictBase`. -/
theorem hM_localPullback (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t')
    (Q : (E.baseChange t).Point (𝟙 T)) (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M) :
    letI := Scheme.Modules.monoidalCategory (pullback E.π t')
    (kappa E hsm t' (restrictBase E t g hg Q)).val =
      toSkeleton ((Scheme.Modules.pullback (baseChangeMap E.π g hg)).obj M) := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  letI := Scheme.Modules.monoidalCategory (pullback E.π t')
  have hM'' : (kappa E hsm t Q).val = toSkeleton M := hM
  calc (kappa E hsm t' (restrictBase E t g hg Q)).val
      = (Scheme.Pic.map (baseChangeMap E.π g hg) (kappa E hsm t Q)).val :=
        congrArg Units.val (kappa_restrictBase E hsm t g hg Q).symm
    _ = (Scheme.Modules.pullback (baseChangeMap E.π g hg)).mapSkeleton.obj
          (kappa E hsm t Q).val := Scheme.Pic.map_val _ _
    _ = (Scheme.Modules.pullback (baseChangeMap E.π g hg)).mapSkeleton.obj
          (toSkeleton M) := congrArg _ hM''
    _ = toSkeleton ((Scheme.Modules.pullback (baseChangeMap E.π g hg)).obj M) :=
        Functor.mapSkeleton_obj_toSkeleton _ M

/-- The pulled-back dataset's cocycle is normalised along the zero section of `T'`: the
`hnorm`-side of the pulled dataset. -/
theorem hnorm_localPullback (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t')
    (M : (pullback E.π t).Modules)
    {ι : Type*} (W : ι → (pullback E.π t).Opens)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j)) (i j : ι) :
    transitionUnitOfCover ((Scheme.Modules.pullback (baseChangeMap E.π g hg)).obj M)
        (fun i => baseChangeMap E.π g hg ⁻¹ᵁ W i)
        (fun i => localPullbackTrivializationT (baseChangeMap E.π g hg) M (W i) (e i))
        i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t')
        (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j) := by
  have hzcomp : baseChangeZero E.π E.zero E.zero_π t' ≫ baseChangeMap E.π g hg =
      g ≫ baseChangeZero E.π E.zero E.zero_π t :=
    baseChangeZero_baseChangeMap E.π E.zero E.zero_π g hg
  rw [mem_sectionUnits_iff,
    transitionUnitOfCover_localPullback (baseChangeMap E.π g hg) M W e i j]
  refine ((congrArg (sectionEval (baseChangeZero E.π E.zero E.zero_π t')
      (baseChangeMap E.π g hg ⁻¹ᵁ W i ⊓ baseChangeMap E.π g hg ⁻¹ᵁ W j))
      (map_app_eq_unitPullback (baseChangeMap E.π g hg) (W i ⊓ W j)
        (transitionUnitOfCover M W e i j))).trans ?_)
  refine ((sectionEval_unitPullback (baseChangeMap E.π g hg)
    (baseChangeZero E.π E.zero E.zero_π t') (le_of_eq rfl)
    (transitionUnitOfCover M W e i j)).trans ?_)
  refine ((resUnit_sectionEval_congr hzcomp (W i ⊓ W j)
    (transitionUnitOfCover M W e i j)
    ((baseChangeZero E.π E.zero E.zero_π t').preimage_mono (le_of_eq rfl))
    (by rw [← hzcomp]
        exact (baseChangeZero E.π E.zero E.zero_π t').preimage_mono
          (le_of_eq rfl))).trans ?_)
  refine ((congrArg _ ((sectionEval_comp g (baseChangeZero E.π E.zero E.zero_π t)
    (W i ⊓ W j) (transitionUnitOfCover M W e i j)).trans ?_)).trans (map_one _))
  rw [show sectionEval (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j)
      (transitionUnitOfCover M W e i j) = 1 from hnorm i j]
  exact map_one _

/-- **(AP-E1-NAT3, the restriction law)** The canonical pairing commutes with base change:
`e_N(P|_{T'}, Q|_{T'}) = g^#(e_N(P, Q))`. Reads the `T`-value through its chosen dataset,
pulls the dataset back (NAT2), and lets the master independence absorb the difference from
the `T'`-chosen dataset. -/
theorem weilPairingKM_restrictBase (hsm : SmoothOfRelativeDimension 1 E.π)
    [IsSeparated E.π] (t : T ⟶ S) {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') (N : ℕ)
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N) :
    weilPairingKM E hsm t' N (restrictBase E t g hg P)
        (restrictBase_mem_torsionPoints E t g hg hP)
        (restrictBase E t g hg Q) (restrictBase_mem_torsionPoints E t g hg hQ) =
      unitPullback g ⊤ ⊤ le_rfl (weilPairingKM E hsm t N P hP Q hQ) :=
  (weilPairingKM_eq_torsionSplittingEval E hsm t' N (restrictBase E t g hg P)
    (restrictBase_mem_torsionPoints E t g hg hP)
    (restrictBase E t g hg Q) (restrictBase_mem_torsionPoints E t g hg hQ)
    ((Scheme.Modules.pullback (baseChangeMap E.π g hg)).obj
      (exists_normalized_dataset E hsm t Q).choose)
    (hM_localPullback E hsm t g hg Q (exists_normalized_dataset E hsm t Q).choose
      (exists_normalized_dataset E hsm t Q).choose_spec.choose)
    (fun i => baseChangeMap E.π g hg ⁻¹ᵁ
      (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose i)
    ((baseChangeMap E.π g hg).iSup_preimage_eq_top
      (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose)
    (fun i => localPullbackTrivializationT (baseChangeMap E.π g hg)
      (exists_normalized_dataset E hsm t Q).choose
      ((exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose i)
      ((exists_normalized_dataset E hsm t
        Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose i))
    (hnorm_localPullback E t g hg (exists_normalized_dataset E hsm t Q).choose
      (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose
      (exists_normalized_dataset E hsm t
        Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
      (exists_normalized_dataset E hsm t
        Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec)).trans
  (torsionSplittingEval_restrictBase E hsm t g hg N Q hQ
    (exists_normalized_dataset E hsm t Q).choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t
      Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (exists_normalized_dataset E hsm t
      Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
    P hP
    (hM_localPullback E hsm t g hg Q (exists_normalized_dataset E hsm t Q).choose
      (exists_normalized_dataset E hsm t Q).choose_spec.choose)
    (hnorm_localPullback E t g hg (exists_normalized_dataset E hsm t Q).choose
      (exists_normalized_dataset E hsm t Q).choose_spec.choose_spec.choose_spec.choose
      (exists_normalized_dataset E hsm t
        Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
      (exists_normalized_dataset E hsm t
        Q).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec))

end RestrictBase

section Bridge

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- A point killed by `[N]` gives an `N`-torsion section of the base-changed curve. -/
theorem asSection_mem_torsionPoints {T : Scheme.{u}} {g : T ⟶ S} {N : ℕ} (x : E.Point g)
    (hx : (x : T ⟶ E.E) ≫ E.mulByHom N = g ≫ E.zero) :
    EllipticCurve.Point.asSection E g x ∈ torsionPoints E g N := by
  refine mem_torsionPoints_of_comp_mulByHom E N _ ?_
  calc ((EllipticCurve.Point.asSection E g x).1 : T ⟶ pullback E.π g) ≫
        pullback.fst E.π g ≫ E.mulByHom (N : ℤ)
      = (((EllipticCurve.Point.asSection E g x).1 : T ⟶ pullback E.π g) ≫
          pullback.fst E.π g) ≫ E.mulByHom (N : ℤ) := (Category.assoc _ _ _).symm
    _ = (x : T ⟶ E.E) ≫ E.mulByHom (N : ℤ) :=
        congrArg (· ≫ E.mulByHom (N : ℤ)) (EllipticCurve.Point.asSection_val_fst E g x)
    _ = g ≫ E.zero := hx
    _ = (𝟙 T ≫ g) ≫ E.zero := congrArg (· ≫ E.zero) (Category.id_comp g).symm

/-- **(AP-E1-YON1, reconstruction)** Restricting the first tautological point along the
classifying map of a pair `(x, y)` recovers `x` (as a section of the base-changed curve). -/
theorem restrictBase_univTorsionFst {T : Scheme.{u}} {g : T ⟶ S} {N : ℕ}
    (x y : E.Point g)
    (hx : (x : T ⟶ E.E) ≫ E.mulByHom N = g ≫ E.zero)
    (hy : (y : T ⟶ E.E) ≫ E.mulByHom N = g ≫ E.zero)
    (hk : (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy)
        (by simp) : T ⟶ pullback (E.torsionπ N) (E.torsionπ N)) ≫
      (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) = g) :
    restrictBase E (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
        (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) (by simp)) hk
        (univTorsionFst E N) =
      EllipticCurve.Point.asSection E g x := by
  refine Subtype.ext ?_
  apply pullback.hom_ext
  · refine (restrictBase_coe_fst E _ _ hk (univTorsionFst E N)).trans
      (Eq.trans ?_ (EllipticCurve.Point.asSection_val_fst E g x).symm)
    calc pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) (by simp) ≫
          ((univTorsionFst E N).1 ≫
            pullback.fst E.π (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N))
        = pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) (by simp) ≫
            (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N) :=
          congrArg _ (pullback.lift_fst _ _ _)
      _ = (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) (by simp) ≫
            pullback.fst (E.torsionπ N) (E.torsionπ N)) ≫ E.torsionι N :=
          (Category.assoc _ _ _).symm
      _ = E.pointToTorsion x hx ≫ E.torsionι N :=
          congrArg (· ≫ E.torsionι N) (pullback.lift_fst _ _ _)
      _ = (x : T ⟶ E.E) := E.pointToTorsion_torsionι x hx
  · refine ((restrictBase E _ _ hk (univTorsionFst E N)).2).trans ?_
    exact ((EllipticCurve.Point.asSection E g x).2).symm

/-- **(AP-E1-YON1, reconstruction — second slot)** Restricting the second tautological
point recovers `y`. -/
theorem restrictBase_univTorsionSnd {T : Scheme.{u}} {g : T ⟶ S} {N : ℕ}
    (x y : E.Point g)
    (hx : (x : T ⟶ E.E) ≫ E.mulByHom N = g ≫ E.zero)
    (hy : (y : T ⟶ E.E) ≫ E.mulByHom N = g ≫ E.zero)
    (hk : (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy)
        (by simp) : T ⟶ pullback (E.torsionπ N) (E.torsionπ N)) ≫
      (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N) = g) :
    restrictBase E (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
        (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) (by simp)) hk
        (univTorsionSnd E N) =
      EllipticCurve.Point.asSection E g y := by
  refine Subtype.ext ?_
  apply pullback.hom_ext
  · refine (restrictBase_coe_fst E _ _ hk (univTorsionSnd E N)).trans
      (Eq.trans ?_ (EllipticCurve.Point.asSection_val_fst E g y).symm)
    calc pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) (by simp) ≫
          ((univTorsionSnd E N).1 ≫
            pullback.fst E.π (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N))
        = pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) (by simp) ≫
            (pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N) :=
          congrArg _ (pullback.lift_fst _ _ _)
      _ = (pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) (by simp) ≫
            pullback.snd (E.torsionπ N) (E.torsionπ N)) ≫ E.torsionι N :=
          (Category.assoc _ _ _).symm
      _ = E.pointToTorsion y hy ≫ E.torsionι N :=
          congrArg (· ≫ E.torsionι N) (pullback.lift_snd _ _ _)
      _ = (y : T ⟶ E.E) := E.pointToTorsion_torsionι y hy
  · refine ((restrictBase E _ _ hk (univTorsionSnd E N)).2).trans ?_
    exact ((EllipticCurve.Point.asSection E g y).2).symm

/-- `Point.asSection` is the base-change equivalence composed with the transport along
`𝟙 ≫ g = g` — in particular it is additive. -/
theorem asSection_eq_baseChangeEquiv_symm {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    EllipticCurve.Point.asSection E g P =
      (EllipticCurve.Point.baseChangeEquiv E g (𝟙 T)).symm
        (pointCongr E (Category.id_comp g).symm P) := by
  refine Subtype.ext (pullback.hom_ext ?_ ?_)
  · exact (EllipticCurve.Point.asSection_val_fst E g P).trans
      ((pointCongr_apply_coe E (Category.id_comp g).symm P).symm.trans
        (pullback.lift_fst _ _ _).symm)
  · exact ((EllipticCurve.Point.asSection E g P).2).trans
      (pullback.lift_snd _ _ _).symm

/-- `Point.asSection` is additive. -/
theorem asSection_add {T : Scheme.{u}} (g : T ⟶ S) (x y : E.Point g) :
    EllipticCurve.Point.asSection E g (x + y) =
      EllipticCurve.Point.asSection E g x + EllipticCurve.Point.asSection E g y := by
  rw [asSection_eq_baseChangeEquiv_symm, asSection_eq_baseChangeEquiv_symm,
    asSection_eq_baseChangeEquiv_symm, map_add, map_add]

/-- `restrictBase` depends on the restriction morphism only through its value. -/
theorem restrictBase_congr_hom {T T' : Scheme.{u}} (t : T ⟶ S) {t' : T' ⟶ S}
    {g g' : T' ⟶ T} (hgg : g = g') (hg : g ≫ t = t') (hg' : g' ≫ t = t')
    (Q : (E.baseChange t).Point (𝟙 T)) :
    restrictBase E t g hg Q = restrictBase E t g' hg' Q := by
  subst hgg; rfl

/-- `weilPairingKM` depends only on the points, not on the membership witnesses or the
way the points were assembled. -/
theorem weilPairingKM_congr (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    {T : Scheme.{u}} (t : T ⟶ S) (N : ℕ)
    {P P' Q Q' : (E.baseChange t).Point (𝟙 T)} (hPP : P = P') (hQQ : Q = Q')
    (hP : P ∈ torsionPoints E t N) (hQ : Q ∈ torsionPoints E t N)
    (hP' : P' ∈ torsionPoints E t N) (hQ' : Q' ∈ torsionPoints E t N) :
    weilPairingKM E hsm t N P hP Q hQ = weilPairingKM E hsm t N P' hP' Q' hQ' := by
  subst hPP; subst hQQ; rfl

/-- **(AP-E3, bilinearity in the second variable)** The canonical pairing is additive in
`Q`: refine the two chosen datasets to a common cover, tensor them — the frames of
`exists_frame_mul` and the trivialising family of `exists_over_trivialization_of_frames`
give a dataset for `Q + Q'` (via `kappa_add`) whose cocycle is the product — and
`torsionSplittingEval_mul_of_transitionUnitOfCover_mul` multiplies the values. -/
theorem weilPairingKM_add_right {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S) (N : ℕ)
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N)
    (Q Q' : (E.baseChange t).Point (𝟙 T))
    (hQ : Q ∈ torsionPoints E t N) (hQ' : Q' ∈ torsionPoints E t N) :
    weilPairingKM E hsm t N P hP (Q + Q') (add_mem hQ hQ') =
      weilPairingKM E hsm t N P hP Q hQ * weilPairingKM E hsm t N P hP Q' hQ' := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  obtain ⟨M, hM, ι, W, hW, e, hnorm⟩ := exists_normalized_dataset E hsm t Q
  obtain ⟨M', hM', ι', W', hW', e', hnorm'⟩ := exists_normalized_dataset E hsm t Q'
  -- the common refinement
  set V : ι × ι' → (pullback E.π t).Opens := fun p => W p.1 ⊓ W' p.2 with hVdef
  have hV : iSup V = ⊤ := by
    rw [hVdef, iSup_prod]
    have hstep : ∀ i, ⨆ j, (W i ⊓ W' j) = W i ⊓ ⨆ j, W' j := fun i =>
      (inf_iSup_eq _ _).symm
    calc ⨆ i, ⨆ j, (W i ⊓ W' j) = ⨆ i, (W i ⊓ ⨆ j, W' j) := iSup_congr hstep
      _ = ⊤ := by rw [hW']; simp only [inf_top_eq]; exact hW
  set eV : ∀ p : ι × ι', M.over (V p) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (V p)) :=
    fun p => SheafOfModules.restrictOverTrivialization
      (pullback E.π t).ringCatSheaf M (W p.1) (e p.1)
      (Over.mk (homOfLE (inf_le_left : V p ≤ W p.1))) with heV
  set e'V : ∀ p : ι × ι', M'.over (V p) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (V p)) :=
    fun p => SheafOfModules.restrictOverTrivialization
      (pullback E.π t).ringCatSheaf M' (W' p.2) (e' p.2)
      (Over.mk (homOfLE (inf_le_right : V p ≤ W' p.2))) with he'V
  have hnormV : ∀ p q, transitionUnitOfCover M V eV p q ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (V p ⊓ V q) := fun p q =>
    transitionUnitOfCover_restrict_mem_sectionUnits M W e hnorm Prod.fst V
      (fun p => inf_le_left) p q
  have hnorm'V : ∀ p q, transitionUnitOfCover M' V e'V p q ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (V p ⊓ V q) := fun p q =>
    transitionUnitOfCover_restrict_mem_sectionUnits M' W' e' hnorm' Prod.snd V
      (fun p => inf_le_right) p q
  -- the tensor dataset for `Q + Q'`
  obtain ⟨σ, hfr, hrel⟩ := exists_frame_mul M M' V eV e'V
  obtain ⟨e'', hmulco⟩ := exists_over_trivialization_of_frames (M ⊗ M') V σ hfr
    (fun p q => transitionUnitOfCover M V eV p q * transitionUnitOfCover M' V e'V p q)
    (fun p q => by rw [Units.val_mul]; exact hrel p q)
  have hM'' : (kappa E hsm t (Q + Q')).val = toSkeleton (M ⊗ M') := by
    have hMv : (kappa E hsm t Q).val = toSkeleton M := hM
    have hM'v : (kappa E hsm t Q').val = toSkeleton M' := hM'
    calc (kappa E hsm t (Q + Q')).val
        = (kappa E hsm t Q * kappa E hsm t Q').val :=
          congrArg Units.val (kappa_add E hsm t Q Q')
      _ = (kappa E hsm t Q).val * (kappa E hsm t Q').val := Units.val_mul _ _
      _ = toSkeleton M * toSkeleton M' := by rw [hMv, hM'v]
      _ = toSkeleton (M ⊗ M') := (Skeleton.toSkeleton_tensorObj _ _).symm
  have hnorm'' : ∀ p q, transitionUnitOfCover (M ⊗ M') V e'' p q ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (V p ⊓ V q) := fun p q => by
    rw [hmulco p q]
    exact mul_mem (hnormV p q) (hnorm'V p q)
  calc weilPairingKM E hsm t N P hP (Q + Q') (add_mem hQ hQ')
      = torsionSplittingEval E hsm t N (Q + Q') (add_mem hQ hQ') (M ⊗ M') hM'' V hV e''
          hnorm'' P hP :=
        weilPairingKM_eq_torsionSplittingEval E hsm t N P hP (Q + Q') (add_mem hQ hQ')
          (M ⊗ M') hM'' V hV e'' hnorm''
    _ = torsionSplittingEval E hsm t N Q hQ M hM V hV eV hnormV P hP *
          torsionSplittingEval E hsm t N Q' hQ' M' hM' V hV e'V hnorm'V P hP :=
        torsionSplittingEval_mul_of_transitionUnitOfCover_mul E hsm t N Q hQ M hM V hV eV
          hnormV Q' (Q + Q') hQ' (add_mem hQ hQ') M' (M ⊗ M') hM' hM'' e'V e'' hnorm'V
          hnorm'' hmulco P hP
    _ = weilPairingKM E hsm t N P hP Q hQ * weilPairingKM E hsm t N P hP Q' hQ' := by
        rw [← weilPairingKM_eq_torsionSplittingEval E hsm t N P hP Q hQ M hM V hV eV
            hnormV,
          ← weilPairingKM_eq_torsionSplittingEval E hsm t N P hP Q' hQ' M' hM' V hV e'V
            hnorm'V]

end Bridge

section MapIso

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {S : Scheme.{u}}

namespace EllipticCurve

/-! ## U1 — transport along pointed isomorphisms of elliptic records -/

/-- Transport of a `T`-point along a pointed isomorphism of elliptic records over the
same base. -/
noncomputable def Point.mapIso {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g) : F.Point g :=
  ⟨x.1 ≫ φ.hom.left, by
    rw [Category.assoc, show φ.hom.left ≫ F.π = E.π from Over.w φ.hom, x.2]⟩

/-- Kill-by-`N` transports along a pointed (monoid) isomorphism:
`mulByHom_comp_left_of_isMonHom` conjugates the `[N]`s. -/
theorem zero_comp_left_of_isMonHom {E F : EllipticCurve S}
    (φ : E.asOver ⟶ F.asOver) [IsMonHom φ] :
    E.zero ≫ φ.left = F.zero := by
  have h2' : ((𝟙_ (Over S)).hom ≫ E.zero) ≫ φ.left = (𝟙_ (Over S)).hom ≫ F.zero := by
    have h1 : η[E.asOver] ≫ φ = η[F.asOver] := IsMonHom.one_hom φ
    have h2 := congrArg CommaMorphism.left h1
    simp only [Over.comp_left] at h2
    rw [← E.one_eq_zero, ← F.one_eq_zero]
    exact h2
  simpa using h2'

theorem Point.mapIso_killedBy {E F : EllipticCurve S} [IsLocallyNoetherian S]
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} {g : T ⟶ S}
    {N : ℕ} {x : E.Point g} (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (Point.mapIso φ x).1 ≫ F.mulByHom N = g ≫ F.zero := by
  show (x.1 ≫ φ.hom.left) ≫ F.mulByHom N = g ≫ F.zero
  rw [Category.assoc, ← mulByHom_comp_left_of_isMonHom E F φ.hom (N : ℤ),
    ← Category.assoc, hx, Category.assoc, zero_comp_left_of_isMonHom φ.hom]

/-- **([PB-ISO])** The induced isomorphism on `π`-pullbacks from a record iso over the
same base: `pullback.map` along `φ.hom.left`, `𝟙 T`, `𝟙 S`. -/
noncomputable def pullbackMapIso {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} (g : T ⟶ S) : pullback E.π g ≅ pullback F.π g := by
  haveI : IsIso φ.hom := inferInstance
  haveI : IsIso φ.hom.left := (Over.forget S).map_isIso φ.hom
  exact asIso (pullback.map E.π g F.π g φ.hom.left (𝟙 T) (𝟙 S)
    (by rw [Category.comp_id]; exact (Over.w φ.hom).symm) (by simp))

@[simp] theorem pullbackMapIso_hom_fst {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} (g : T ⟶ S) :
    (pullbackMapIso φ g).hom ≫ pullback.fst F.π g = pullback.fst E.π g ≫ φ.hom.left :=
  pullback.lift_fst _ _ _

@[simp] theorem pullbackMapIso_hom_snd {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} (g : T ⟶ S) :
    (pullbackMapIso φ g).hom ≫ pullback.snd F.π g = pullback.snd E.π g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The zero sections correspond under [PB-ISO] (pointedness). -/
theorem baseChangeZero_comp_pullbackMapIso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} (g : T ⟶ S) :
    Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g ≫ (pullbackMapIso φ g).hom =
      Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackMapIso_hom_fst, ← Category.assoc]
    rw [show Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g ≫ pullback.fst E.π g =
      g ≫ E.zero from pullback.lift_fst _ _ _,
      show Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g ≫ pullback.fst F.π g =
      g ≫ F.zero from pullback.lift_fst _ _ _]
    rw [Category.assoc, zero_comp_left_of_isMonHom φ.hom]
  · rw [Category.assoc, pullbackMapIso_hom_snd]
    rw [show Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g ≫ pullback.snd E.π g =
      𝟙 T from pullback.lift_snd _ _ _,
      show Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g ≫ pullback.snd F.π g =
      𝟙 T from pullback.lift_snd _ _ _]

/-- **([ASSEC-MAPISO])** `asSection` intertwines the point transport and [PB-ISO]. -/
theorem asSection_mapIso {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g) :
    (EllipticCurve.Point.asSection E g x).1 ≫ (pullbackMapIso φ g).hom =
      (EllipticCurve.Point.asSection F g (Point.mapIso φ x)).1 := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => (EllipticCurve.Point.asSection E g x).1 ≫ m)
        (pullback.lift_fst _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ φ.hom.left)
        (EllipticCurve.Point.asSection_val_fst E g x)).trans
      (EllipticCurve.Point.asSection_val_fst F g (Point.mapIso φ x)).symm)))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => (EllipticCurve.Point.asSection E g x).1 ≫ m)
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _))).trans
      ((EllipticCurve.Point.asSection_val_snd E g x).trans
      (EllipticCurve.Point.asSection_val_snd F g (Point.mapIso φ x)).symm))


/-- **([KER-MAPISO])** Kernel ideal-sheaf comap along an isomorphism: the comap of a
closed-immersion kernel along `e.hom` is the kernel of the `e.inv`-conjugated morphism. -/
theorem ker_comap_iso {X Y W : Scheme.{u}} (e : X ≅ Y) (z : W ⟶ Y)
    [IsClosedImmersion z] :
    (Scheme.Hom.ker z).comap e.hom = Scheme.Hom.ker (z ≫ e.inv) := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion z e.hom]
  have hfst : pullback.fst e.hom z = pullback.snd e.hom z ≫ z ≫ e.inv := by
    conv_lhs => rw [← Category.comp_id (pullback.fst e.hom z), ← e.hom_inv_id,
      ← Category.assoc, pullback.condition, Category.assoc]
  rw [hfst]
  haveI : IsIso (pullback.snd e.hom z) := inferInstance
  exact Scheme.Hom.ker_comp_of_isIso _ _

/-- **([SECTIONCLS-MAPISO])** The section class transports along a pointed record iso:
`Pic.map (pullbackMapIso φ g).hom` carries the `F`-side class of the transported section
to the `E`-side class. The comap of the transported kernel collapses on the nose to the
original kernel via [KER-MAPISO]. -/
theorem sectionCls_mapIso {E F : EllipticCurve S}
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (hsm' : SmoothOfRelativeDimension 1 F.π) [IsSeparated F.π]
    (φ : E.asOver ≅ F.asOver) {T : Scheme.{u}} (g : T ⟶ S)
    (P : T ⟶ pullback E.π g) (hP : P ≫ pullback.snd E.π g = 𝟙 T) :
    Scheme.Pic.map (pullbackMapIso φ g).hom
      (sectionCls F hsm' g (P ≫ (pullbackMapIso φ g).hom)
        (by rw [Category.assoc, show (pullbackMapIso φ g).hom ≫ pullback.snd F.π g =
          pullback.snd E.π g from (pullback.lift_snd _ _ _).trans (Category.comp_id _), hP])) =
      sectionCls E hsm g P hP := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π g)
  letI := Scheme.Modules.monoidalCategory (pullback F.π g)
  haveI hsepE : IsSeparated (pullback.snd E.π g) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π g ‹_›
  haveI hsepF : IsSeparated (pullback.snd F.π g) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) F.π g ‹_›
  have hsmE : SmoothOfRelativeDimension 1 (pullback.snd E.π g) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.π g hsm
  have hsmF : SmoothOfRelativeDimension 1 (pullback.snd F.π g) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) F.π g hsm'
  have hPF : (P ≫ (pullbackMapIso φ g).hom) ≫ pullback.snd F.π g = 𝟙 T := by
    rw [Category.assoc, show (pullbackMapIso φ g).hom ≫ pullback.snd F.π g =
      pullback.snd E.π g from (pullback.lift_snd _ _ _).trans (Category.comp_id _), hP]
  haveI hciP : IsClosedImmersion P := by
    refine MorphismProperty.of_postcomp (W := @IsClosedImmersion)
      (W' := @IsSeparated) _ (pullback.snd E.π g) hsepE ?_
    rw [hP]
    infer_instance
  haveI hciPF : IsClosedImmersion (P ≫ (pullbackMapIso φ g).hom) := by
    refine MorphismProperty.of_postcomp (W := @IsClosedImmersion)
      (W' := @IsSeparated) _ (pullback.snd F.π g) hsepF ?_
    rw [hPF]
    infer_instance
  -- the comap of the transported kernel is the original kernel on the nose
  have hkercollapse : (Scheme.Hom.ker (P ≫ (pullbackMapIso φ g).hom)).comap
      (pullbackMapIso φ g).hom = Scheme.Hom.ker P := by
    rw [ker_comap_iso (pullbackMapIso φ g) (P ≫ (pullbackMapIso φ g).hom)]
    exact congrArg Scheme.Hom.ker
      (by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id])
  have hJ : ∀ c : ↥(pullback F.π g), ∃ V : (pullback F.π g).affineOpens, c ∈ V.1 ∧
      ∃ f : Γ(pullback F.π g, V.1),
        (Scheme.Hom.ker (P ≫ (pullbackMapIso φ g).hom)).ideal V = Ideal.span {f} ∧
          f ∈ nonZeroDivisors Γ(pullback F.π g, V.1) :=
    (RelEffCartierDiv.sectionDivisor_isOfficial hsmF _ hPF).locallyPrincipal
  have hJ' : ∀ c : ↥(pullback E.π g), ∃ V : (pullback E.π g).affineOpens, c ∈ V.1 ∧
      ∃ f : Γ(pullback E.π g, V.1),
        ((Scheme.Hom.ker (P ≫ (pullbackMapIso φ g).hom)).comap
          (pullbackMapIso φ g).hom).ideal V = Ideal.span {f} ∧
          f ∈ nonZeroDivisors Γ(pullback E.π g, V.1) := by
    rw [hkercollapse]
    exact (RelEffCartierDiv.sectionDivisor_isOfficial hsmE P hP).locallyPrincipal
  obtain ⟨eiso⟩ := nonempty_pullback_idealModule (pullbackMapIso φ g).hom
    (Scheme.Hom.ker (P ≫ (pullbackMapIso φ g).hom)) hJ hJ'
  have hcore : Scheme.Pic.map (pullbackMapIso φ g).hom
      (((RelEffCartierDiv.sectionDivisor (pullback.snd F.π g)
          (P ≫ (pullbackMapIso φ g).hom) hPF).isInvertible_idealModule
        (RelEffCartierDiv.sectionDivisor_isOfficial hsmF _ hPF)).isUnit_toSkeleton.unit) =
      ((RelEffCartierDiv.sectionDivisor (pullback.snd E.π g)
          P hP).isInvertible_idealModule
        (RelEffCartierDiv.sectionDivisor_isOfficial hsmE P hP)).isUnit_toSkeleton.unit := by
    refine Units.ext ?_
    refine (Scheme.Pic.map_val (pullbackMapIso φ g).hom _).trans ?_
    refine (congrArg (Scheme.Modules.pullback (pullbackMapIso φ g).hom).mapSkeleton.obj
      (IsUnit.unit_spec _)).trans ?_
    refine (Functor.mapSkeleton_obj_toSkeleton _ _).trans ?_
    refine (toSkeleton_eq_toSkeleton_iff.mpr
      ⟨eiso ≪≫ eqToIso (congrArg Scheme.Modules.idealModule hkercollapse)⟩).trans ?_
    exact (IsUnit.unit_spec _).symm
  refine Eq.trans (map_inv (Scheme.Pic.map (pullbackMapIso φ g).hom) _) ?_
  exact congrArg (·⁻¹) hcore

/-- **([ZEROCLS-MAPISO])** The zero class transports along a pointed record iso:
the transported zero section IS the `F`-side zero section (pointedness). -/
theorem zeroCls_mapIso {E F : EllipticCurve S}
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (hsm' : SmoothOfRelativeDimension 1 F.π) [IsSeparated F.π]
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} (g : T ⟶ S) :
    Scheme.Pic.map (pullbackMapIso φ g).hom (zeroCls F hsm' g) =
      zeroCls E hsm g := by
  have hz : Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g ≫
      (pullbackMapIso φ g).hom =
      Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g :=
    baseChangeZero_comp_pullbackMapIso φ g
  have hzsnd : (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g ≫
      (pullbackMapIso φ g).hom) ≫ pullback.snd F.π g = 𝟙 T := by
    rw [hz]
    exact Scheme.Modules.baseChangeZero_snd F.π F.zero F.zero_π g
  calc Scheme.Pic.map (pullbackMapIso φ g).hom (zeroCls F hsm' g)
      = Scheme.Pic.map (pullbackMapIso φ g).hom
          (sectionCls F hsm' g
            (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g ≫
              (pullbackMapIso φ g).hom) hzsnd) :=
        congrArg _ (sectionCls_congr F hsm' g _ _ hz.symm)
    _ = sectionCls E hsm g (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g)
          (Scheme.Modules.baseChangeZero_snd E.π E.zero E.zero_π g) :=
        sectionCls_mapIso hsm hsm' φ g _ _
    _ = zeroCls E hsm g := rfl

/-- **([KAPPA-MAPISO])** `κ` transports along a pointed record iso over the same base:
the `Pic`-pullback along [PB-ISO] of the `F`-side `κ` at the transported point is the
`E`-side `κ`. Mirror of `kappa_restrictBase` with the fixed base `T`. -/
theorem kappa_mapIso {E F : EllipticCurve S}
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (hsm' : SmoothOfRelativeDimension 1 F.π) [IsSeparated F.π]
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} (g : T ⟶ S)
    (Q : (E.baseChange g).Point (𝟙 T))
    (hQF : (Q.1 ≫ (pullbackMapIso φ g).hom) ≫ pullback.snd F.π g = 𝟙 T) :
    Scheme.Pic.map (pullbackMapIso φ g).hom
      (kappa F hsm' g (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ :
        (F.baseChange g).Point (𝟙 T))) =
      kappa E hsm g Q := by
  have hval : ∀ (x : Scheme.Pic (pullback F.π g)),
      ((picRelProj F.π F.zero F.zero_π g x : picRel F.π F.zero F.zero_π g) :
        Scheme.Pic (pullback F.π g)) =
      x * (Scheme.Pic.map (pullback.snd F.π g)
        (Scheme.Pic.map (Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g) x))⁻¹ :=
    fun _ => rfl
  set x := sectionCls F hsm' g (Q.1 ≫ (pullbackMapIso φ g).hom) hQF *
    (zeroCls F hsm' g)⁻¹ with hx
  set x' := sectionCls E hsm g Q.1 Q.2 * (zeroCls E hsm g)⁻¹ with hx'
  have hratio : Scheme.Pic.map (pullbackMapIso φ g).hom x = x' := by
    rw [hx, hx', map_mul, map_inv]
    congr 1
    · exact sectionCls_mapIso hsm hsm' φ g Q.1 Q.2
    · exact congrArg (·⁻¹) (zeroCls_mapIso hsm hsm' φ g)
  have hsq1 : ∀ y : Scheme.Pic T,
      Scheme.Pic.map (pullbackMapIso φ g).hom
        (Scheme.Pic.map (pullback.snd F.π g) y) =
      Scheme.Pic.map (pullback.snd E.π g) y := by
    intro y
    calc Scheme.Pic.map (pullbackMapIso φ g).hom
          (Scheme.Pic.map (pullback.snd F.π g) y)
        = Scheme.Pic.map ((pullbackMapIso φ g).hom ≫ pullback.snd F.π g) y := by
          rw [Scheme.Pic.map_comp]; rfl
      _ = Scheme.Pic.map (pullback.snd E.π g) y := by
          rw [show (pullbackMapIso φ g).hom ≫ pullback.snd F.π g =
            pullback.snd E.π g from
            (pullback.lift_snd _ _ _).trans (Category.comp_id _)]
  have hsq2 : ∀ y : Scheme.Pic (pullback F.π g),
      Scheme.Pic.map (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g)
        (Scheme.Pic.map (pullbackMapIso φ g).hom y) =
      Scheme.Pic.map (Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g) y := by
    intro y
    calc Scheme.Pic.map (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g)
          (Scheme.Pic.map (pullbackMapIso φ g).hom y)
        = Scheme.Pic.map (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g ≫
            (pullbackMapIso φ g).hom) y := by
          rw [Scheme.Pic.map_comp]; rfl
      _ = Scheme.Pic.map (Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g) y := by
          rw [baseChangeZero_comp_pullbackMapIso φ g]
  calc Scheme.Pic.map (pullbackMapIso φ g).hom
        (kappa F hsm' g (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ :
          (F.baseChange g).Point (𝟙 T)))
      = Scheme.Pic.map (pullbackMapIso φ g).hom
          (x * (Scheme.Pic.map (pullback.snd F.π g)
            (Scheme.Pic.map (Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g) x))⁻¹) :=
        congrArg _ ((kappa_eq_picRelProj F hsm' g _).trans (hval x))
    _ = Scheme.Pic.map (pullbackMapIso φ g).hom x *
          (Scheme.Pic.map (pullbackMapIso φ g).hom
            (Scheme.Pic.map (pullback.snd F.π g)
              (Scheme.Pic.map (Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g) x)))⁻¹ := by
        rw [map_mul, map_inv]
    _ = x' * (Scheme.Pic.map (pullback.snd E.π g)
          (Scheme.Pic.map (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g) x'))⁻¹ := by
        rw [hratio, hsq1, ← hsq2, hratio]
    _ = kappa E hsm g Q := ((kappa_eq_picRelProj E hsm g Q).trans
        (show ((picRelProj E.π E.zero E.zero_π g x' : picRel E.π E.zero E.zero_π g) :
            Scheme.Pic (pullback E.π g)) =
          x' * (Scheme.Pic.map (pullback.snd E.π g)
            (Scheme.Pic.map (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g) x'))⁻¹
          from rfl)).symm

/-- **([HM-MAPISO])** The dataset skeleton-condition transports along [PB-ISO]:
a `κ_F`-representative pulls back to a `κ_E`-representative. -/
theorem hM_mapIso {E F : EllipticCurve S}
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (hsm' : SmoothOfRelativeDimension 1 F.π) [IsSeparated F.π]
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} (g : T ⟶ S)
    (Q : (E.baseChange g).Point (𝟙 T))
    (hQF : (Q.1 ≫ (pullbackMapIso φ g).hom) ≫ pullback.snd F.π g = 𝟙 T)
    (A : (pullback F.π g).Modules)
    (hA : letI := Scheme.Modules.monoidalCategory (pullback F.π g)
      (kappa F hsm' g (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ :
        (F.baseChange g).Point (𝟙 T))).val = toSkeleton A) :
    letI := Scheme.Modules.monoidalCategory (pullback E.π g)
    (kappa E hsm g Q).val =
      toSkeleton ((Scheme.Modules.pullback (pullbackMapIso φ g).hom).obj A) := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π g)
  letI := Scheme.Modules.monoidalCategory (pullback F.π g)
  have hA' : (kappa F hsm' g (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ :
      (F.baseChange g).Point (𝟙 T))).val = toSkeleton A := hA
  calc (kappa E hsm g Q).val
      = (Scheme.Pic.map (pullbackMapIso φ g).hom
          (kappa F hsm' g (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ :
            (F.baseChange g).Point (𝟙 T)))).val :=
        congrArg Units.val (kappa_mapIso hsm hsm' φ g Q hQF).symm
    _ = (Scheme.Modules.pullback (pullbackMapIso φ g).hom).mapSkeleton.obj
          (kappa F hsm' g (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ :
            (F.baseChange g).Point (𝟙 T))).val := Scheme.Pic.map_val _ _
    _ = (Scheme.Modules.pullback (pullbackMapIso φ g).hom).mapSkeleton.obj
          (toSkeleton A) := congrArg _ hA'
    _ = toSkeleton ((Scheme.Modules.pullback (pullbackMapIso φ g).hom).obj A) :=
        Functor.mapSkeleton_obj_toSkeleton _ A

/-- **([HNORM-MAPISO])** Normalisation of the pulled dataset along [PB-ISO]: the
transported transitions are still zero-section normalised (pointedness). -/
theorem hnorm_mapIso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} (g : T ⟶ S)
    (A : (pullback F.π g).Modules)
    {J : Type*} (W : J → (pullback F.π g).Opens)
    (e : ∀ i, A.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback F.π g).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover A W e i j ∈
      sectionUnits (Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g) (W i ⊓ W j))
    (i j : J) :
    transitionUnitOfCover ((Scheme.Modules.pullback (pullbackMapIso φ g).hom).obj A)
        (fun i => (pullbackMapIso φ g).hom ⁻¹ᵁ W i)
        (fun i => localPullbackTrivializationT (pullbackMapIso φ g).hom A (W i) (e i)) i j ∈
      sectionUnits (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g)
        ((pullbackMapIso φ g).hom ⁻¹ᵁ W i ⊓ (pullbackMapIso φ g).hom ⁻¹ᵁ W j) := by
  rw [transitionUnitOfCover_localPullback (pullbackMapIso φ g).hom A W e i j]
  exact mem_sectionUnits_pullback (baseChangeZero_comp_pullbackMapIso φ g)
    (W i ⊓ W j) (hnorm i j)

/-- **([MULBYN-PBISO])** [PB-ISO] intertwines the base-changed multiplication maps:
the `[N]`-conjugation square for pointed record isos. -/
theorem mulByN_comp_pullbackMapIso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} (g : T ⟶ S) (N : ℕ) :
    mulByN E g N ≫ (pullbackMapIso φ g).hom =
      (pullbackMapIso φ g).hom ≫ mulByN F g N := by
  have hmE : mulByN E g N = (E.baseChange g).mulByHom (N : ℤ) := rfl
  have hmF : mulByN F g N = (F.baseChange g).mulByHom (N : ℤ) := rfl
  have hfstIso : (pullbackMapIso φ g).hom ≫ pullback.fst F.π g =
      pullback.fst E.π g ≫ φ.hom.left := pullback.lift_fst _ _ _
  have hsndIso : (pullbackMapIso φ g).hom ≫ pullback.snd F.π g =
      pullback.snd E.π g := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine pullback.hom_ext ?_ ?_
  · calc (mulByN E g N ≫ (pullbackMapIso φ g).hom) ≫ pullback.fst F.π g
        = mulByN E g N ≫ ((pullbackMapIso φ g).hom ≫ pullback.fst F.π g) :=
          Category.assoc _ _ _
      _ = mulByN E g N ≫ (pullback.fst E.π g ≫ φ.hom.left) := by rw [hfstIso]
      _ = (mulByN E g N ≫ pullback.fst E.π g) ≫ φ.hom.left :=
          (Category.assoc _ _ _).symm
      _ = (pullback.fst E.π g ≫ E.mulByHom (N : ℤ)) ≫ φ.hom.left := by
          rw [hmE]; exact congrArg (· ≫ φ.hom.left) (mulByHom_baseChange_fst E g (N : ℤ))
      _ = pullback.fst E.π g ≫ (E.mulByHom (N : ℤ) ≫ φ.hom.left) :=
          Category.assoc _ _ _
      _ = pullback.fst E.π g ≫ (φ.hom.left ≫ F.mulByHom (N : ℤ)) := by
          rw [mulByHom_comp_left_of_isMonHom E F φ.hom (N : ℤ)]
      _ = (pullback.fst E.π g ≫ φ.hom.left) ≫ F.mulByHom (N : ℤ) :=
          (Category.assoc _ _ _).symm
      _ = ((pullbackMapIso φ g).hom ≫ pullback.fst F.π g) ≫ F.mulByHom (N : ℤ) := by
          rw [hfstIso]
      _ = (pullbackMapIso φ g).hom ≫ (pullback.fst F.π g ≫ F.mulByHom (N : ℤ)) :=
          Category.assoc _ _ _
      _ = (pullbackMapIso φ g).hom ≫ (mulByN F g N ≫ pullback.fst F.π g) := by
          rw [hmF]
          exact congrArg ((pullbackMapIso φ g).hom ≫ ·)
            (mulByHom_baseChange_fst F g (N : ℤ)).symm
      _ = ((pullbackMapIso φ g).hom ≫ mulByN F g N) ≫ pullback.fst F.π g :=
          (Category.assoc _ _ _).symm
  · calc (mulByN E g N ≫ (pullbackMapIso φ g).hom) ≫ pullback.snd F.π g
        = mulByN E g N ≫ ((pullbackMapIso φ g).hom ≫ pullback.snd F.π g) :=
          Category.assoc _ _ _
      _ = mulByN E g N ≫ pullback.snd E.π g := by rw [hsndIso]
      _ = pullback.snd E.π g := by
          rw [hmE]; exact mulByHom_baseChange_snd E g (N : ℤ)
      _ = (pullbackMapIso φ g).hom ≫ pullback.snd F.π g := hsndIso.symm
      _ = (pullbackMapIso φ g).hom ≫ (mulByN F g N ≫ pullback.snd F.π g) := by
          rw [hmF]
          exact congrArg ((pullbackMapIso φ g).hom ≫ ·)
            (mulByHom_baseChange_snd F g (N : ℤ)).symm
      _ = ((pullbackMapIso φ g).hom ≫ mulByN F g N) ≫ pullback.snd F.π g :=
          (Category.assoc _ _ _).symm

/-- The preimage square of [MULBYN-PBISO]. -/
theorem mulByN_preimage_pullbackMapIso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} (g : T ⟶ S) (N : ℕ)
    (V : (pullback F.π g).Opens) :
    mulByN E g N ⁻¹ᵁ ((pullbackMapIso φ g).hom ⁻¹ᵁ V) = (pullbackMapIso φ g).hom ⁻¹ᵁ (mulByN F g N ⁻¹ᵁ V) :=
  (Scheme.Hom.comp_preimage _ _ _).symm.trans
    ((congrArg (· ⁻¹ᵁ V) (mulByN_comp_pullbackMapIso φ g N)).trans
      (Scheme.Hom.comp_preimage _ _ _))

/-- **([UMAP-SQ])** The `Units.map ∘ app` collapse along the [MULBYN-PBISO] square. -/
private theorem unitsMap_app_mulByN_pullbackMapIso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} (g : T ⟶ S) (N : ℕ)
    (V : (pullback F.π g).Opens) (a : Γ(pullback F.π g, V)ˣ) :
    Units.map ((mulByN E g N).app ((pullbackMapIso φ g).hom ⁻¹ᵁ V)).hom.toMonoidHom
        (Units.map (((pullbackMapIso φ g).hom).app V).hom.toMonoidHom a) =
      Scheme.resUnit (le_of_eq (mulByN_preimage_pullbackMapIso φ g N V))
        (Units.map (((pullbackMapIso φ g).hom).app (mulByN F g N ⁻¹ᵁ V)).hom.toMonoidHom
          (Units.map ((mulByN F g N).app V).hom.toMonoidHom a)) := by
  refine ((congrArg (Units.map ((mulByN E g N).app ((pullbackMapIso φ g).hom ⁻¹ᵁ V)).hom.toMonoidHom)
    (map_app_eq_unitPullback ((pullbackMapIso φ g).hom) V a)).trans ?_)
  refine ((map_app_eq_unitPullback (mulByN E g N) ((pullbackMapIso φ g).hom ⁻¹ᵁ V)
    (unitPullback ((pullbackMapIso φ g).hom) V ((pullbackMapIso φ g).hom ⁻¹ᵁ V) le_rfl a)).trans ?_)
  refine ((unitPullback_unitPullback (mulByN E g N) ((pullbackMapIso φ g).hom) le_rfl le_rfl a).trans ?_)
  refine ((unitPullback_congr (mulByN_comp_pullbackMapIso φ g N) V _ _
    (le_of_eq (mulByN_preimage_pullbackMapIso φ g N V)) a).trans ?_)
  refine Eq.trans ?_ (congrArg (Scheme.resUnit (le_of_eq
      (mulByN_preimage_pullbackMapIso φ g N V)))
    ((congrArg (Units.map (((pullbackMapIso φ g).hom).app (mulByN F g N ⁻¹ᵁ V)).hom.toMonoidHom)
      (map_app_eq_unitPullback (mulByN F g N) V a)).trans
     ((map_app_eq_unitPullback ((pullbackMapIso φ g).hom) (mulByN F g N ⁻¹ᵁ V)
        (unitPullback (mulByN F g N) V (mulByN F g N ⁻¹ᵁ V) le_rfl a)).trans
      (unitPullback_unitPullback ((pullbackMapIso φ g).hom) (mulByN F g N) le_rfl le_rfl a))).symm)
  exact (resUnit_unitPullback (((pullbackMapIso φ g).hom) ≫ mulByN F g N)
    (le_rfl.trans ((((pullbackMapIso φ g).hom)).preimage_mono le_rfl))
    (le_of_eq (mulByN_preimage_pullbackMapIso φ g N V)) a).symm

/-- **([RES-UMAP-RES])** The abstract four-restriction collapse: restricting a pulled
unit of a restriction equals the doubly-restricted pull of the unit. Both sides are the
`unitPullback` to the bottom open. -/
private theorem resUnit_unitsMap_app_resUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U₁ U₂ : Y.Opens} (hU : U₂ ≤ U₁) {V₁ V₂ : X.Opens}
    (hV : V₂ ≤ f ⁻¹ᵁ U₂) (hV' : V₁ ≤ f ⁻¹ᵁ U₁) (hV₂₁ : V₂ ≤ V₁) (u : Γ(Y, U₁)ˣ) :
    Scheme.resUnit hV (Units.map (f.app U₂).hom.toMonoidHom (Scheme.resUnit hU u)) =
      Scheme.resUnit hV₂₁ (Scheme.resUnit hV' (Units.map (f.app U₁).hom.toMonoidHom u)) := by
  have h1 : Units.map (f.app U₂).hom.toMonoidHom (Scheme.resUnit hU u) =
      unitPullback f U₁ (f ⁻¹ᵁ U₂) (f.preimage_mono hU) u :=
    (map_app_eq_unitPullback f U₂ (Scheme.resUnit hU u)).trans
      (unitPullback_resUnit f hU le_rfl u)
  have h2 : Scheme.resUnit hV (Units.map (f.app U₂).hom.toMonoidHom (Scheme.resUnit hU u)) =
      unitPullback f U₁ V₂ (hV.trans (f.preimage_mono hU)) u :=
    (congrArg (Scheme.resUnit hV) h1).trans
      (resUnit_unitPullback f (f.preimage_mono hU) hV u)
  have h3 : Scheme.resUnit hV' (Units.map (f.app U₁).hom.toMonoidHom u) =
      unitPullback f U₁ V₁ hV' u :=
    (congrArg (Scheme.resUnit hV') (map_app_eq_unitPullback f U₁ u)).trans
      (resUnit_unitPullback f le_rfl hV' u)
  have h4 : Scheme.resUnit hV₂₁ (Scheme.resUnit hV' (Units.map (f.app U₁).hom.toMonoidHom u)) =
      unitPullback f U₁ V₂ (hV₂₁.trans hV') u :=
    (congrArg (Scheme.resUnit hV₂₁) h3).trans
      (resUnit_unitPullback f hV' hV₂₁ u)
  exact h2.trans h4.symm

/-- **([TSE-MAPISO], the E6-d mirror)** The torsion-splitting value is invariant under
pointed record isos: the `E`-side evaluation on the [PB-ISO]-pulled dataset equals the
`F`-side evaluation on the original dataset, both read at corresponding points. -/
theorem torsionSplittingEval_mapIso {E F : EllipticCurve S}
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (hsm' : SmoothOfRelativeDimension 1 F.π) [IsSeparated F.π]
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] {T : Scheme.{u}} (g : T ⟶ S) (N : ℕ)
    (Q : (E.baseChange g).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E g N)
    (hQF : (Q.1 ≫ (pullbackMapIso φ g).hom) ≫ pullback.snd F.π g = 𝟙 T)
    (hQFt : (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ : (F.baseChange g).Point (𝟙 T)) ∈ torsionPoints F g N)
    (A : (pullback F.π g).Modules)
    (hA : letI := Scheme.Modules.monoidalCategory (pullback F.π g)
      (kappa F hsm' g (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ : (F.baseChange g).Point (𝟙 T))).val =
        toSkeleton A)
    {J : Type*} (W : J → (pullback F.π g).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, A.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback F.π g).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover A W e i j ∈
      sectionUnits (Scheme.Modules.baseChangeZero F.π F.zero F.zero_π g) (W i ⊓ W j))
    (Pt : (E.baseChange g).Point (𝟙 T)) (hPt : Pt ∈ torsionPoints E g N)
    (hPF : (Pt.1 ≫ (pullbackMapIso φ g).hom) ≫ pullback.snd F.π g = 𝟙 T)
    (hPFt : (⟨Pt.1 ≫ (pullbackMapIso φ g).hom, hPF⟩ : (F.baseChange g).Point (𝟙 T)) ∈ torsionPoints F g N) :
    torsionSplittingEval E hsm g N Q hQ
        ((Scheme.Modules.pullback (pullbackMapIso φ g).hom).obj A)
        (hM_mapIso hsm hsm' φ g Q hQF A hA)
        (fun i => (pullbackMapIso φ g).hom ⁻¹ᵁ W i)
        (((pullbackMapIso φ g).hom).iSup_preimage_eq_top hW)
        (fun i => localPullbackTrivializationT (pullbackMapIso φ g).hom A (W i) (e i))
        (hnorm_mapIso φ g A W e hnorm)
        Pt hPt =
      torsionSplittingEval F hsm' g N
        (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ : (F.baseChange g).Point (𝟙 T)) hQFt A hA W hW e hnorm
        (⟨Pt.1 ≫ (pullbackMapIso φ g).hom, hPF⟩ : (F.baseChange g).Point (𝟙 T)) hPFt := by
  obtain ⟨h, hn, hsplit⟩ := exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints
    F hsm' g N (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ : (F.baseChange g).Point (𝟙 T)) hQFt A hA W hW e hnorm
  have hres := resUnit_torsionSplittingEval
    F hsm' g N (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ : (F.baseChange g).Point (𝟙 T)) hQFt A hA W hW e hnorm
    (⟨Pt.1 ≫ (pullbackMapIso φ g).hom, hPF⟩ : (F.baseChange g).Point (𝟙 T)) hPFt h hn hsplit
  have hle : ∀ i, mulByN E g N ⁻¹ᵁ ((pullbackMapIso φ g).hom ⁻¹ᵁ W i) ≤ (pullbackMapIso φ g).hom ⁻¹ᵁ (mulByN F g N ⁻¹ᵁ W i) :=
    fun i => le_of_eq (mulByN_preimage_pullbackMapIso φ g N (W i))
  -- the transported normalisation
  have hn' : ∀ i, Scheme.resUnit (hle i)
      (Units.map (((pullbackMapIso φ g).hom).app (mulByN F g N ⁻¹ᵁ W i)).hom.toMonoidHom (h i)) ∈
      sectionUnits (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g)
        (mulByN E g N ⁻¹ᵁ ((pullbackMapIso φ g).hom ⁻¹ᵁ W i)) := by
    intro i
    rw [mem_sectionUnits_iff, sectionEval_resUnit,
      show sectionEval (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π g)
        ((pullbackMapIso φ g).hom ⁻¹ᵁ (mulByN F g N ⁻¹ᵁ W i))
        (Units.map (((pullbackMapIso φ g).hom).app (mulByN F g N ⁻¹ᵁ W i)).hom.toMonoidHom (h i)) = 1 from
      mem_sectionUnits_pullback (baseChangeZero_comp_pullbackMapIso φ g)
        (mulByN F g N ⁻¹ᵁ W i) (hn i), map_one]
  -- the transported splitting property
  have hsplit' : ∀ i j,
      Units.map ((mulByN E g N).app
          ((pullbackMapIso φ g).hom ⁻¹ᵁ W i ⊓ (pullbackMapIso φ g).hom ⁻¹ᵁ W j)).hom.toMonoidHom
        (transitionUnitOfCover ((Scheme.Modules.pullback (pullbackMapIso φ g).hom).obj A)
          (fun i => (pullbackMapIso φ g).hom ⁻¹ᵁ W i)
          (fun i => localPullbackTrivializationT (pullbackMapIso φ g).hom A (W i) (e i)) i j) =
      Scheme.resUnit inf_le_left (Scheme.resUnit (hle i)
        (Units.map (((pullbackMapIso φ g).hom).app (mulByN F g N ⁻¹ᵁ W i)).hom.toMonoidHom (h i))) *
        (Scheme.resUnit inf_le_right (Scheme.resUnit (hle j)
          (Units.map (((pullbackMapIso φ g).hom).app (mulByN F g N ⁻¹ᵁ W j)).hom.toMonoidHom (h j))))⁻¹ := by
    intro i j
    refine ((congrArg (Units.map ((mulByN E g N).app
        ((pullbackMapIso φ g).hom ⁻¹ᵁ W i ⊓ (pullbackMapIso φ g).hom ⁻¹ᵁ W j)).hom.toMonoidHom)
        (transitionUnitOfCover_localPullback ((pullbackMapIso φ g).hom) A W e i j)).trans ?_)
    refine ((unitsMap_app_mulByN_pullbackMapIso φ g N (W i ⊓ W j)
        (transitionUnitOfCover A W e i j)).trans ?_)
    refine ((congrArg (Scheme.resUnit _) (congrArg
        (Units.map (((pullbackMapIso φ g).hom).app (mulByN F g N ⁻¹ᵁ (W i ⊓ W j))).hom.toMonoidHom)
        (hsplit i j))).trans ?_)
    refine ((congrArg (Scheme.resUnit _) (map_mul _ _ _)).trans ?_)
    refine ((map_mul _ _ _).trans ?_)
    have hVi : mulByN E g N ⁻¹ᵁ ((pullbackMapIso φ g).hom ⁻¹ᵁ W i) ⊓ mulByN E g N ⁻¹ᵁ ((pullbackMapIso φ g).hom ⁻¹ᵁ W j) ≤
        (pullbackMapIso φ g).hom ⁻¹ᵁ (mulByN F g N ⁻¹ᵁ W i ⊓ mulByN F g N ⁻¹ᵁ W j) :=
      le_of_eq (by exact mulByN_preimage_pullbackMapIso φ g N (W i ⊓ W j))
    refine congrArg₂ (· * ·) ?_ ?_
    · exact resUnit_unitsMap_app_resUnit ((pullbackMapIso φ g).hom)
        (inf_le_left : mulByN F g N ⁻¹ᵁ W i ⊓ mulByN F g N ⁻¹ᵁ W j ≤ mulByN F g N ⁻¹ᵁ W i)
        hVi (le_of_eq (mulByN_preimage_pullbackMapIso φ g N (W i)))
        inf_le_left (h i)
    · refine ((congrArg (Scheme.resUnit _) (map_inv _ _)).trans ?_)
      refine ((map_inv _ _).trans ?_)
      refine congrArg (·⁻¹) ?_
      exact resUnit_unitsMap_app_resUnit ((pullbackMapIso φ g).hom)
        (inf_le_right : mulByN F g N ⁻¹ᵁ W i ⊓ mulByN F g N ⁻¹ᵁ W j ≤ mulByN F g N ⁻¹ᵁ W j)
        hVi (le_of_eq (mulByN_preimage_pullbackMapIso φ g N (W j)))
        inf_le_right (h j)
  -- the value condition, read through the point crossing
  have hC : ∀ i, Scheme.resUnit
      (le_top : (Pt.1 : T ⟶ pullback E.π g) ⁻¹ᵁ
        (mulByN E g N ⁻¹ᵁ ((pullbackMapIso φ g).hom ⁻¹ᵁ W i)) ≤ ⊤)
      (torsionSplittingEval F hsm' g N
        (⟨Q.1 ≫ (pullbackMapIso φ g).hom, hQF⟩ : (F.baseChange g).Point (𝟙 T)) hQFt A hA W hW e hnorm
        (⟨Pt.1 ≫ (pullbackMapIso φ g).hom, hPF⟩ : (F.baseChange g).Point (𝟙 T)) hPFt) =
      sectionEval (Pt.1 : T ⟶ pullback E.π g)
        (mulByN E g N ⁻¹ᵁ ((pullbackMapIso φ g).hom ⁻¹ᵁ W i))
        (Scheme.resUnit (hle i)
          (Units.map (((pullbackMapIso φ g).hom).app (mulByN F g N ⁻¹ᵁ W i)).hom.toMonoidHom (h i))) := by
    intro i
    refine Eq.symm ?_
    refine ((sectionEval_resUnit (Pt.1 : T ⟶ pullback E.π g) (hle i) _).trans ?_)
    refine ((congrArg (Scheme.resUnit _)
      (sectionEval_pullback ((pullbackMapIso φ g).hom) Pt.1 (mulByN F g N ⁻¹ᵁ W i) (h i))).trans ?_)
    refine ((congrArg (Scheme.resUnit _) (hres i).symm).trans ?_)
    exact Scheme.resUnit_resUnit _ _ _
  exact (eq_torsionSplittingEval E hsm g N Q hQ
    ((Scheme.Modules.pullback (pullbackMapIso φ g).hom).obj A)
    (hM_mapIso hsm hsm' φ g Q hQF A hA)
    (fun i => (pullbackMapIso φ g).hom ⁻¹ᵁ W i)
    (((pullbackMapIso φ g).hom).iSup_preimage_eq_top hW)
    (fun i => localPullbackTrivializationT (pullbackMapIso φ g).hom A (W i) (e i))
    (hnorm_mapIso φ g A W e hnorm)
    Pt hPt
    (fun i => Scheme.resUnit (hle i)
      (Units.map (((pullbackMapIso φ g).hom).app (mulByN F g N ⁻¹ᵁ W i)).hom.toMonoidHom (h i)))
    hn' hsplit' hC).symm

end EllipticCurve

end MapIso

section BcSwapDefs

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}} (t : T ⟶ S)

/-- **([BC-SWAP ι])** The tautological collapse of the identity pullback of a base
change: `pullback ((E.baseChange t).π) (𝟙 T) ≅ pullback E.π t` via the first
projection (`𝟙` on the right leg makes `fst` an isomorphism). -/
noncomputable def bcSwapIso :
    pullback ((E.baseChange t).π) (𝟙 T) ≅ pullback E.π t where
  hom := pullback.fst ((E.baseChange t).π) (𝟙 T)
  inv := pullback.lift (𝟙 _) (pullback.snd E.π t)
    ((Category.id_comp _).trans
      ((show (E.baseChange t).π = pullback.snd E.π t from rfl).trans
        (Category.comp_id _).symm))
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun m => pullback.fst ((E.baseChange t).π) (𝟙 T) ≫ m)
          (pullback.lift_fst _ _ _)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun m => pullback.fst ((E.baseChange t).π) (𝟙 T) ≫ m)
          (pullback.lift_snd _ _ _)).trans
        ((pullback.condition (f := (E.baseChange t).π) (g := 𝟙 T)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
  inv_hom_id := pullback.lift_fst _ _ _

@[simp] theorem bcSwapIso_hom :
    (bcSwapIso E t).hom = pullback.fst ((E.baseChange t).π) (𝟙 T) := rfl

/-- The zero sections correspond under [BC-SWAP ι]. -/
theorem baseChangeZero_comp_bcSwapIso :
    Scheme.Modules.baseChangeZero ((E.baseChange t).π) ((E.baseChange t).zero)
        ((E.baseChange t).zero_π) (𝟙 T) ≫ (bcSwapIso E t).hom =
      Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t := by
  rw [bcSwapIso_hom]
  exact (pullback.lift_fst _ _ _).trans (Category.id_comp _)

end BcSwapDefs

/-- **([SECTIONCLS-BCSWAP])** The section class transports along the collapse iso:
the `PB`-side class of `P` pulls back to the doubled-pullback-side class of
`P ≫ (bcSwapIso E t).inv`. Mirror of `sectionCls_mapIso` at ι. -/
theorem sectionCls_bcSwap {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (t : T ⟶ S)
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (hsmBC : SmoothOfRelativeDimension 1 ((E.baseChange t).π))
    [IsSeparated ((E.baseChange t).π)]
    (P : T ⟶ pullback E.π t) (hP : P ≫ pullback.snd E.π t = 𝟙 T)
    (hPsw : (P ≫ (bcSwapIso E t).inv) ≫
      pullback.snd ((E.baseChange t).π) (𝟙 T) = 𝟙 T) :
    Scheme.Pic.map (bcSwapIso E t).hom
      (sectionCls E hsm t P hP) =
      sectionCls (E.baseChange t) hsmBC
        (𝟙 T) (P ≫ (bcSwapIso E t).inv) hPsw := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  letI := Scheme.Modules.monoidalCategory (pullback ((E.baseChange t).π) (𝟙 T))
  haveI hsepE : IsSeparated (pullback.snd E.π t) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π t ‹_›
  haveI hsepB : IsSeparated (pullback.snd ((E.baseChange t).π) (𝟙 T)) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ ‹_›
  have hsmE : SmoothOfRelativeDimension 1 (pullback.snd E.π t) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.π t hsm
  have hsmB : SmoothOfRelativeDimension 1 (pullback.snd ((E.baseChange t).π) (𝟙 T)) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ hsmBC
  haveI hciP : IsClosedImmersion P := by
    refine MorphismProperty.of_postcomp (W := @IsClosedImmersion)
      (W' := @IsSeparated) _ (pullback.snd E.π t) hsepE ?_
    rw [hP]
    infer_instance
  haveI hciPsw : IsClosedImmersion (P ≫ (bcSwapIso E t).inv) := by
    refine MorphismProperty.of_postcomp (W := @IsClosedImmersion)
      (W' := @IsSeparated) _ (pullback.snd ((E.baseChange t).π) (𝟙 T)) hsepB ?_
    rw [hPsw]
    infer_instance
  have hkercollapse : (Scheme.Hom.ker P).comap (bcSwapIso E t).hom =
      Scheme.Hom.ker (P ≫ (bcSwapIso E t).inv) :=
    EllipticCurve.ker_comap_iso (bcSwapIso E t) P
  have hJ : ∀ c : ↥(pullback E.π t), ∃ V : (pullback E.π t).affineOpens, c ∈ V.1 ∧
      ∃ f : Γ(pullback E.π t, V.1),
        (Scheme.Hom.ker P).ideal V = Ideal.span {f} ∧
          f ∈ nonZeroDivisors Γ(pullback E.π t, V.1) :=
    (RelEffCartierDiv.sectionDivisor_isOfficial hsmE P hP).locallyPrincipal
  have hJ' : ∀ c : ↥(pullback ((E.baseChange t).π) (𝟙 T)),
      ∃ V : (pullback ((E.baseChange t).π) (𝟙 T)).affineOpens, c ∈ V.1 ∧
      ∃ f : Γ(pullback ((E.baseChange t).π) (𝟙 T), V.1),
        ((Scheme.Hom.ker P).comap (bcSwapIso E t).hom).ideal V = Ideal.span {f} ∧
          f ∈ nonZeroDivisors Γ(pullback ((E.baseChange t).π) (𝟙 T), V.1) := by
    rw [hkercollapse]
    exact (RelEffCartierDiv.sectionDivisor_isOfficial hsmB _ hPsw).locallyPrincipal
  obtain ⟨eiso⟩ := nonempty_pullback_idealModule (bcSwapIso E t).hom
    (Scheme.Hom.ker P) hJ hJ'
  have hcore : Scheme.Pic.map (bcSwapIso E t).hom
      (((RelEffCartierDiv.sectionDivisor (pullback.snd E.π t)
          P hP).isInvertible_idealModule
        (RelEffCartierDiv.sectionDivisor_isOfficial hsmE P hP)).isUnit_toSkeleton.unit) =
      ((RelEffCartierDiv.sectionDivisor (pullback.snd ((E.baseChange t).π) (𝟙 T))
          (P ≫ (bcSwapIso E t).inv) hPsw).isInvertible_idealModule
        (RelEffCartierDiv.sectionDivisor_isOfficial hsmB _ hPsw)).isUnit_toSkeleton.unit := by
    refine Units.ext ?_
    refine (Scheme.Pic.map_val (bcSwapIso E t).hom _).trans ?_
    refine (congrArg (Scheme.Modules.pullback (bcSwapIso E t).hom).mapSkeleton.obj
      (IsUnit.unit_spec _)).trans ?_
    refine (Functor.mapSkeleton_obj_toSkeleton _ _).trans ?_
    refine (toSkeleton_eq_toSkeleton_iff.mpr
      ⟨eiso ≪≫ eqToIso (congrArg Scheme.Modules.idealModule hkercollapse)⟩).trans ?_
    exact (IsUnit.unit_spec _).symm
  refine Eq.trans (map_inv (Scheme.Pic.map (bcSwapIso E t).hom) _) ?_
  exact congrArg (·⁻¹) hcore

/-- **([ZEROCLS-BCSWAP])** The zero class transports along the collapse iso. -/
theorem zeroCls_bcSwap {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (t : T ⟶ S)
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (hsmBC : SmoothOfRelativeDimension 1 ((E.baseChange t).π))
    [IsSeparated ((E.baseChange t).π)] :
    Scheme.Pic.map (bcSwapIso E t).hom (zeroCls E hsm t) =
      zeroCls (E.baseChange t) hsmBC (𝟙 T) := by
  have hz : Scheme.Modules.baseChangeZero ((E.baseChange t).π) ((E.baseChange t).zero)
      ((E.baseChange t).zero_π) (𝟙 T) ≫ (bcSwapIso E t).hom =
      Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t :=
    baseChangeZero_comp_bcSwapIso E t
  have hswap : Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t ≫
      (bcSwapIso E t).inv =
      Scheme.Modules.baseChangeZero ((E.baseChange t).π) ((E.baseChange t).zero)
        ((E.baseChange t).zero_π) (𝟙 T) :=
    (congrArg (fun m => m ≫ (bcSwapIso E t).inv) hz.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => Scheme.Modules.baseChangeZero ((E.baseChange t).π)
            ((E.baseChange t).zero) ((E.baseChange t).zero_π) (𝟙 T) ≫ m)
          (bcSwapIso E t).hom_inv_id).trans (Category.comp_id _)))
  have hzsw : (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t ≫
      (bcSwapIso E t).inv) ≫ pullback.snd ((E.baseChange t).π) (𝟙 T) = 𝟙 T :=
    (congrArg (fun m => m ≫ pullback.snd ((E.baseChange t).π) (𝟙 T)) hswap).trans
      (Scheme.Modules.baseChangeZero_snd _ _ _ _)
  calc Scheme.Pic.map (bcSwapIso E t).hom (zeroCls E hsm t)
      = sectionCls (E.baseChange t) hsmBC (𝟙 T)
          (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t ≫ (bcSwapIso E t).inv)
          hzsw :=
        sectionCls_bcSwap E t hsm hsmBC _
          (Scheme.Modules.baseChangeZero_snd E.π E.zero E.zero_π t) hzsw
    _ = zeroCls (E.baseChange t) hsmBC (𝟙 T) :=
        sectionCls_congr (E.baseChange t) hsmBC (𝟙 T) _ _ hswap

/-- The abstract shape of a `picRelProj`-transport: a group map intertwining the two
section/zero legs carries one relative-projection expression to the other. -/
private theorem map_mul_inv_transport {A B C : Type*} [CommGroup A] [CommGroup B]
    [CommGroup C] (φ : A →* B) (sA : C →* A) (sB : C →* B) (zA : A →* C) (zB : B →* C)
    (hs : ∀ y, φ (sA y) = sB y) (hz : ∀ y, zB (φ y) = zA y) {x : A} {x' : B}
    (hx : φ x = x') :
    φ (x * (sA (zA x))⁻¹) = x' * (sB (zB x'))⁻¹ := by
  rw [map_mul, map_inv, hs, hx, ← hz x, hx]

/-- The `snd`-square of the collapse iso (split out for the elaboration budget). -/
private theorem picMap_bcSwap_snd {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (t : T ⟶ S) : ∀ y : Scheme.Pic T,
    Scheme.Pic.map (bcSwapIso E t).hom (Scheme.Pic.map (pullback.snd E.π t) y) =
      Scheme.Pic.map (pullback.snd ((E.baseChange t).π) (𝟙 T)) y := by
  intro y
  calc Scheme.Pic.map (bcSwapIso E t).hom (Scheme.Pic.map (pullback.snd E.π t) y)
      = Scheme.Pic.map ((bcSwapIso E t).hom ≫ pullback.snd E.π t) y := by
        rw [Scheme.Pic.map_comp]; rfl
    _ = Scheme.Pic.map (pullback.snd ((E.baseChange t).π) (𝟙 T)) y := by
        refine congrArg (fun m => Scheme.Pic.map m y) ?_
        exact (pullback.condition
          (f := (E.baseChange t).π) (g := 𝟙 T)).trans (Category.comp_id _)

/-- The zero-square of the collapse iso (split out for the elaboration budget). -/
private theorem picMap_bcSwap_zero {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (t : T ⟶ S) : ∀ y : Scheme.Pic (pullback E.π t),
    Scheme.Pic.map (Scheme.Modules.baseChangeZero ((E.baseChange t).π)
        ((E.baseChange t).zero) ((E.baseChange t).zero_π) (𝟙 T))
      (Scheme.Pic.map (bcSwapIso E t).hom y) =
    Scheme.Pic.map (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t) y := by
  intro y
  calc Scheme.Pic.map (Scheme.Modules.baseChangeZero ((E.baseChange t).π)
          ((E.baseChange t).zero) ((E.baseChange t).zero_π) (𝟙 T))
        (Scheme.Pic.map (bcSwapIso E t).hom y)
      = Scheme.Pic.map (Scheme.Modules.baseChangeZero ((E.baseChange t).π)
          ((E.baseChange t).zero) ((E.baseChange t).zero_π) (𝟙 T) ≫
            (bcSwapIso E t).hom) y := by
        rw [Scheme.Pic.map_comp]; rfl
    _ = Scheme.Pic.map (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t) y := by
        rw [baseChangeZero_comp_bcSwapIso]

/-- The `picRelProj` value-unfold on the doubled base change (rfl, split out for the
elaboration budget). -/
private theorem picRelProj_val_bc {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (t : T ⟶ S) (x : Scheme.Pic (pullback ((E.baseChange t).π) (𝟙 T))) :
    ((picRelProj ((E.baseChange t).π) ((E.baseChange t).zero)
        ((E.baseChange t).zero_π) (𝟙 T) x :
        picRel ((E.baseChange t).π) ((E.baseChange t).zero)
          ((E.baseChange t).zero_π) (𝟙 T)) :
        Scheme.Pic (pullback ((E.baseChange t).π) (𝟙 T))) =
      x * (Scheme.Pic.map (pullback.snd ((E.baseChange t).π) (𝟙 T))
        (Scheme.Pic.map (Scheme.Modules.baseChangeZero ((E.baseChange t).π)
          ((E.baseChange t).zero) ((E.baseChange t).zero_π) (𝟙 T)) x))⁻¹ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `κ` on the doubled base change, unfolded to the section/zero expression (own
elaboration budget). -/
private theorem kappa_bc_unfold {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (t : T ⟶ S) (hsmBC : SmoothOfRelativeDimension 1 ((E.baseChange t).π))
    [IsSeparated ((E.baseChange t).π)]
    (Q' : ((E.baseChange t).baseChange (𝟙 T)).Point (𝟙 T)) :
    kappa (E.baseChange t) hsmBC (𝟙 T) Q' =
      (sectionCls (E.baseChange t) hsmBC (𝟙 T) Q'.1 Q'.2 *
          (zeroCls (E.baseChange t) hsmBC (𝟙 T))⁻¹) *
        (Scheme.Pic.map (pullback.snd ((E.baseChange t).π) (𝟙 T))
          (Scheme.Pic.map (Scheme.Modules.baseChangeZero ((E.baseChange t).π)
            ((E.baseChange t).zero) ((E.baseChange t).zero_π) (𝟙 T))
            (sectionCls (E.baseChange t) hsmBC (𝟙 T) Q'.1 Q'.2 *
              (zeroCls (E.baseChange t) hsmBC (𝟙 T))⁻¹)))⁻¹ :=
  (kappa_eq_picRelProj (E.baseChange t) hsmBC (𝟙 T) Q').trans
    (picRelProj_val_bc E t _)

/-- **([KAPPA-BCSWAP])** `κ` transports along the collapse iso: the `Pic`-pullback of
the `E/t`-side `κ` at `Q` is the `(E.baseChange t)/𝟙`-side `κ` at the swapped point. -/
theorem kappa_bcSwap {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (t : T ⟶ S)
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (hsmBC : SmoothOfRelativeDimension 1 ((E.baseChange t).π))
    [IsSeparated ((E.baseChange t).π)]
    (Q : (E.baseChange t).Point (𝟙 T))
    (hQsw : (Q.1 ≫ (bcSwapIso E t).inv) ≫
      pullback.snd ((E.baseChange t).π) (𝟙 T) = 𝟙 T) :
    Scheme.Pic.map (bcSwapIso E t).hom (kappa E hsm t Q) =
      kappa (E.baseChange t) hsmBC (𝟙 T)
        (⟨Q.1 ≫ (bcSwapIso E t).inv, hQsw⟩ :
          ((E.baseChange t).baseChange (𝟙 T)).Point (𝟙 T)) := by
  have hval : ∀ (x : Scheme.Pic (pullback E.π t)),
      ((picRelProj E.π E.zero E.zero_π t x : picRel E.π E.zero E.zero_π t) :
        Scheme.Pic (pullback E.π t)) =
      x * (Scheme.Pic.map (pullback.snd E.π t)
        (Scheme.Pic.map (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t) x))⁻¹ :=
    fun _ => rfl
  set x := sectionCls E hsm t Q.1 Q.2 * (zeroCls E hsm t)⁻¹ with hx
  set x' := sectionCls (E.baseChange t) hsmBC (𝟙 T) (Q.1 ≫ (bcSwapIso E t).inv) hQsw *
    (zeroCls (E.baseChange t) hsmBC (𝟙 T))⁻¹ with hx'
  have hratio : Scheme.Pic.map (bcSwapIso E t).hom x = x' := by
    rw [hx, hx', map_mul, map_inv]
    congr 1
    · exact sectionCls_bcSwap E t hsm hsmBC Q.1 Q.2 hQsw
    · exact congrArg (·⁻¹) (zeroCls_bcSwap E t hsm hsmBC)
  have hsq1 := picMap_bcSwap_snd E t
  have hsq2 := picMap_bcSwap_zero E t
  refine ((congrArg (Scheme.Pic.map (bcSwapIso E t).hom)
    ((kappa_eq_picRelProj E hsm t Q).trans (hval x))).trans ?_).trans
    (kappa_bc_unfold E t hsmBC _).symm
  exact map_mul_inv_transport (Scheme.Pic.map (bcSwapIso E t).hom)
    (Scheme.Pic.map (pullback.snd E.π t))
    (Scheme.Pic.map (pullback.snd ((E.baseChange t).π) (𝟙 T)))
    (Scheme.Pic.map (Scheme.Modules.baseChangeZero E.π E.zero E.zero_π t))
    (Scheme.Pic.map (Scheme.Modules.baseChangeZero ((E.baseChange t).π)
      ((E.baseChange t).zero) ((E.baseChange t).zero_π) (𝟙 T)))
    hsq1 hsq2 hratio

end ModularCurves
