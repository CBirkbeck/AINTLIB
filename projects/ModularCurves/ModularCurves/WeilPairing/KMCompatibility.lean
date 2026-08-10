/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMNaturality
import ModularCurves.EllipticCurve.EndomorphismDegree

/-!
# Level compatibility of the Katz–Mazur pairing (AP-E6, KM 2.8.4.1 at `π₁ = [N]`, `π₂ = [M]`)

KM's composability formula `⟨P₀, P₂⟩_{π₂∘π₁} = ⟨P₀, π₂ᵗP₂⟩_{π₁}` (2.8.4.1), instantiated at
the self-dual isogenies `π₁ = [N]`, `π₂ = [M]`, becomes the level-compatibility law

  `e_{N·M}(P, Q) = e_N(P, M • Q)`   for `P ∈ E[N]`, `Q ∈ E[N·M]`,

and KM's "follows immediately from the definition, via the interpretation of `P₂` as a
suitable line bundle" is, in the `torsionSplittingEval` backend, the **shared-splittings
argument**: the `[M]`-pulled dataset of a `κ(Q)`-dataset is a `κ(M • Q)`-dataset
(`[M]^*κ(Q) = κ(Q)^M = κ(M • Q)`, the theorem of the square + `κ`-additivity), and since
`[N]⁻¹([M]⁻¹W) = [N·M]⁻¹W`, a normalised splitting family for the `N·M`-construction on the
original dataset *is* one for the `N`-construction on the pulled dataset. Both evaluations
read the same functions at the same point.

* `mulByN_comp` — `[N] ≫ [M] = [N·M]` on the base-changed curve.
* `hM_mulByNPullback` / `hnorm_mulByNPullback` — the `[M]`-pulled dataset is a normalised
  dataset for `M • Q` (the `[M]`-endomorphism siblings of `hM_localPullback` /
  `hnorm_localPullback`).
* `torsionSplittingEval_mulByN_pullback` — the shared-splittings evaluation identity.
* `weilPairingKM_mul_smul_right` — `e_{N·M}(P, Q) = e_N(P, M • Q)` for the canonical pairing.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules CategoryTheory.MonoidalCategory

namespace ModularCurves

section Compatibility

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)

omit [IsSeparated E.π] in
/-- **(AP-E6-a)** `[N] ≫ [M] = [N·M]` on the base-changed curve: the scheme-level projection
of `mulBy_comp`. -/
theorem mulByN_comp (N M : ℕ) :
    mulByN E t N ≫ mulByN E t M = mulByN E t (N * M) := by
  have h := congrArg CommaMorphism.left ((E.baseChange t).mulBy_comp (N : ℤ) (M : ℤ))
  simp only [Over.comp_left] at h
  rwa [← Int.natCast_mul] at h

omit [IsSeparated E.π] in
/-- An `N`-torsion point is `N·M`-torsion. -/
theorem mem_torsionPoints_mul_right {N : ℕ} (M : ℕ) {P : (E.baseChange t).Point (𝟙 T)}
    (hP : P ∈ torsionPoints E t N) : P ∈ torsionPoints E t (N * M) := by
  rw [mem_torsionPoints] at hP ⊢
  rw [Int.natCast_mul, mul_comm, ← smul_smul, hP, smul_zero]

omit [IsSeparated E.π] in
/-- The `M`-multiple of an `N·M`-torsion point is `N`-torsion. -/
theorem smul_mem_torsionPoints_of_mul {N M : ℕ} {Q : (E.baseChange t).Point (𝟙 T)}
    (hQ : Q ∈ torsionPoints E t (N * M)) : M • Q ∈ torsionPoints E t N := by
  rw [mem_torsionPoints] at hQ ⊢
  rw [← natCast_zsmul Q M, smul_smul, ← Int.natCast_mul]
  exact hQ

/-- **(AP-E6-b)** The `[M]`-pulled module of a `κ(Q)`-representative represents `κ(M • Q)`:
`[M]^*κ(Q) = κ(Q)^M` (theorem of the square, `picMap_mulByHom_kappa_pow`) and
`κ(M • Q) = κ(Q)^M` (`kappa_nsmul`). The `[M]`-endomorphism sibling of `hM_localPullback`. -/
theorem hM_mulByNPullback (M₀ : ℕ) (Q : (E.baseChange t).Point (𝟙 T))
    (A : (pullback E.π t).Modules)
    (hA : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton A) :
    letI := Scheme.Modules.monoidalCategory (pullback E.π t)
    (kappa E hsm t (M₀ • Q)).val =
      toSkeleton ((Scheme.Modules.pullback (mulByN E t M₀)).obj A) := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  have hA' : (kappa E hsm t Q).val = toSkeleton A := hA
  calc (kappa E hsm t (M₀ • Q)).val
      = (Scheme.Pic.map (mulByN E t M₀) (kappa E hsm t Q)).val :=
        congrArg Units.val ((kappa_nsmul E hsm t Q M₀).trans
          (picMap_mulByHom_kappa_pow E hsm t M₀ Q).symm)
    _ = (Scheme.Modules.pullback (mulByN E t M₀)).mapSkeleton.obj
          (kappa E hsm t Q).val := Scheme.Pic.map_val _ _
    _ = (Scheme.Modules.pullback (mulByN E t M₀)).mapSkeleton.obj (toSkeleton A) :=
        congrArg _ hA'
    _ = toSkeleton ((Scheme.Modules.pullback (mulByN E t M₀)).obj A) :=
        Functor.mapSkeleton_obj_toSkeleton _ A

/-- **(AP-E6-c)** The `[M]`-pulled dataset's cocycle is normalised along the same zero
section: `0 ≫ [M] = 0` (`zero_comp_mulByHom_baseChange`) pushes the normalisation through
`mem_sectionUnits_pullback`. The `[M]`-endomorphism sibling of `hnorm_localPullback`. -/
theorem hnorm_mulByNPullback (M₀ : ℕ) (A : (pullback E.π t).Modules)
    {ι : Type*} (W : ι → (pullback E.π t).Opens)
    (e : ∀ i, A.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover A W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j)) (i j : ι) :
    transitionUnitOfCover ((Scheme.Modules.pullback (mulByN E t M₀)).obj A)
        (fun i => mulByN E t M₀ ⁻¹ᵁ W i)
        (fun i => localPullbackTrivializationT (mulByN E t M₀) A (W i) (e i)) i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t)
        (mulByN E t M₀ ⁻¹ᵁ W i ⊓ mulByN E t M₀ ⁻¹ᵁ W j) := by
  rw [transitionUnitOfCover_localPullback (mulByN E t M₀) A W e i j]
  exact mem_sectionUnits_pullback (zero_comp_mulByHom_baseChange E t (M₀ : ℤ))
    (W i ⊓ W j) (hnorm i j)

omit [IsSeparated E.π] in
/-- Composite pullback of a unit along `[N]` then `[M]` is pullback along `[N·M]`, read on the
composite preimage: the `Units.map∘app`-level form of `[N] ≫ [M] = [N·M]`, with the opens
identified by `Scheme.resUnit` along `[N]⁻¹([M]⁻¹V) = [N·M]⁻¹V`. Stated for a single open `V`
so that no `⊓`-of-preimages clothing enters. -/
private theorem unitsMap_app_mulByN_mulByN (N M₀ : ℕ) (V : (pullback E.π t).Opens)
    (a : Γ(pullback E.π t, V)ˣ) :
    Units.map ((mulByN E t N).app (mulByN E t M₀ ⁻¹ᵁ V)).hom.toMonoidHom
        (Units.map ((mulByN E t M₀).app V).hom.toMonoidHom a) =
      Scheme.resUnit
        (le_of_eq ((Scheme.Hom.comp_preimage _ _ _).symm.trans
          (congrArg (· ⁻¹ᵁ V) (mulByN_comp E t N M₀))))
        (Units.map ((mulByN E t (N * M₀)).app V).hom.toMonoidHom a) := by
  have hop : mulByN E t N ⁻¹ᵁ (mulByN E t M₀ ⁻¹ᵁ V) = mulByN E t (N * M₀) ⁻¹ᵁ V :=
    (Scheme.Hom.comp_preimage _ _ _).symm.trans
      (congrArg (· ⁻¹ᵁ V) (mulByN_comp E t N M₀))
  refine ((congrArg (Units.map ((mulByN E t N).app (mulByN E t M₀ ⁻¹ᵁ V)).hom.toMonoidHom)
    (map_app_eq_unitPullback (mulByN E t M₀) V a)).trans ?_)
  refine ((map_app_eq_unitPullback (mulByN E t N) (mulByN E t M₀ ⁻¹ᵁ V)
    (unitPullback (mulByN E t M₀) V (mulByN E t M₀ ⁻¹ᵁ V) le_rfl a)).trans ?_)
  refine ((unitPullback_unitPullback (mulByN E t N) (mulByN E t M₀) le_rfl le_rfl a).trans ?_)
  refine ((unitPullback_congr (mulByN_comp E t N M₀) V _ _ (le_of_eq hop) a).trans ?_)
  refine ((resUnit_unitPullback (mulByN E t (N * M₀)) le_rfl (le_of_eq hop) a).symm.trans ?_)
  exact congrArg (Scheme.resUnit (le_of_eq hop))
    (map_app_eq_unitPullback (mulByN E t (N * M₀)) V a).symm

/-- **(AP-E6-d, the shared-splittings identity — KM 2.8.4.1's mechanism at `[N]`, `[M]`)**
The `N`-level evaluation on the `[M]`-pulled dataset equals the `N·M`-level evaluation on the
original dataset: `[N]⁻¹([M]⁻¹W) = [N·M]⁻¹W` makes any normalised splitting family of the
`N·M`-construction a normalised splitting family of the `N`-construction on the pulled
dataset, and both values read the same functions at the same point `P`. -/
theorem torsionSplittingEval_mulByN_pullback (N M₀ : ℕ)
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t (N * M₀))
    (hMQ : M₀ • Q ∈ torsionPoints E t N)
    (A : (pullback E.π t).Modules)
    (hA : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton A)
    {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, A.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover A W e i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N)
    (hP' : P ∈ torsionPoints E t (N * M₀)) :
    torsionSplittingEval E hsm t N (M₀ • Q) hMQ
        ((Scheme.Modules.pullback (mulByN E t M₀)).obj A)
        (hM_mulByNPullback E hsm t M₀ Q A hA)
        (fun i => mulByN E t M₀ ⁻¹ᵁ W i)
        ((mulByN E t M₀).iSup_preimage_eq_top hW)
        (fun i => localPullbackTrivializationT (mulByN E t M₀) A (W i) (e i))
        (hnorm_mulByNPullback E t M₀ A W e hnorm)
        P hP
      = torsionSplittingEval E hsm t (N * M₀) Q hQ A hA W hW e hnorm P hP' := by
  obtain ⟨h, hn, hsplit⟩ := exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints
    E hsm t (N * M₀) Q hQ A hA W hW e hnorm
  have hres := resUnit_torsionSplittingEval
    E hsm t (N * M₀) Q hQ A hA W hW e hnorm P hP' h hn hsplit
  have hop : ∀ V : (pullback E.π t).Opens,
      mulByN E t N ⁻¹ᵁ (mulByN E t M₀ ⁻¹ᵁ V) = mulByN E t (N * M₀) ⁻¹ᵁ V := fun V =>
    (Scheme.Hom.comp_preimage _ _ _).symm.trans
      (congrArg (· ⁻¹ᵁ V) (mulByN_comp E t N M₀))
  have hle : ∀ i, mulByN E t N ⁻¹ᵁ (mulByN E t M₀ ⁻¹ᵁ W i) ≤
      mulByN E t (N * M₀) ⁻¹ᵁ W i := fun i => le_of_eq (hop (W i))
  -- the transported normalisation
  have hn' : ∀ i, Scheme.resUnit (hle i) (h i) ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t)
        (mulByN E t N ⁻¹ᵁ (mulByN E t M₀ ⁻¹ᵁ W i)) := by
    intro i
    rw [mem_sectionUnits_iff, sectionEval_resUnit,
      show sectionEval (baseChangeZero E.π E.zero E.zero_π t)
        (mulByN E t (N * M₀) ⁻¹ᵁ W i) (h i) = 1 from hn i, map_one]
  -- the transported splitting property
  have hsplit' : ∀ i j,
      Units.map ((mulByN E t N).app
          (mulByN E t M₀ ⁻¹ᵁ W i ⊓ mulByN E t M₀ ⁻¹ᵁ W j)).hom.toMonoidHom
        (transitionUnitOfCover ((Scheme.Modules.pullback (mulByN E t M₀)).obj A)
          (fun i => mulByN E t M₀ ⁻¹ᵁ W i)
          (fun i => localPullbackTrivializationT (mulByN E t M₀) A (W i) (e i)) i j) =
      Scheme.resUnit inf_le_left (Scheme.resUnit (hle i) (h i)) *
        (Scheme.resUnit inf_le_right (Scheme.resUnit (hle j) (h j)))⁻¹ := by
    intro i j
    refine ((congrArg (Units.map ((mulByN E t N).app
        (mulByN E t M₀ ⁻¹ᵁ W i ⊓ mulByN E t M₀ ⁻¹ᵁ W j)).hom.toMonoidHom)
        (transitionUnitOfCover_localPullback (mulByN E t M₀) A W e i j)).trans ?_)
    refine ((unitsMap_app_mulByN_mulByN E t N M₀ (W i ⊓ W j)
        (transitionUnitOfCover A W e i j)).trans ?_)
    refine ((congrArg (Scheme.resUnit _) (hsplit i j)).trans ?_)
    refine ((map_mul _ _ _).trans ?_)
    refine congrArg₂ (· * ·) ?_ ?_
    · exact (Scheme.resUnit_resUnit _ _ _).trans (Scheme.resUnit_resUnit _ _ _).symm
    · refine ((map_inv _ _).trans ?_)
      exact congrArg (·⁻¹)
        ((Scheme.resUnit_resUnit _ _ _).trans (Scheme.resUnit_resUnit _ _ _).symm)
  -- the value condition, read off the `N·M`-side spec
  have hC : ∀ i, Scheme.resUnit
      (le_top : (P.1 : T ⟶ pullback E.π t) ⁻¹ᵁ
        (mulByN E t N ⁻¹ᵁ (mulByN E t M₀ ⁻¹ᵁ W i)) ≤ ⊤)
      (torsionSplittingEval E hsm t (N * M₀) Q hQ A hA W hW e hnorm P hP') =
      sectionEval (P.1 : T ⟶ pullback E.π t)
        (mulByN E t N ⁻¹ᵁ (mulByN E t M₀ ⁻¹ᵁ W i)) (Scheme.resUnit (hle i) (h i)) := by
    intro i
    refine Eq.symm ?_
    refine ((sectionEval_resUnit (P.1 : T ⟶ pullback E.π t) (hle i) (h i)).trans ?_)
    refine ((congrArg (Scheme.resUnit _) (hres i).symm).trans ?_)
    exact Scheme.resUnit_resUnit _ _ _
  exact (eq_torsionSplittingEval E hsm t N (M₀ • Q) hMQ
    ((Scheme.Modules.pullback (mulByN E t M₀)).obj A)
    (hM_mulByNPullback E hsm t M₀ Q A hA)
    (fun i => mulByN E t M₀ ⁻¹ᵁ W i)
    ((mulByN E t M₀).iSup_preimage_eq_top hW)
    (fun i => localPullbackTrivializationT (mulByN E t M₀) A (W i) (e i))
    (hnorm_mulByNPullback E t M₀ A W e hnorm)
    P hP (fun i => Scheme.resUnit (hle i) (h i)) hn' hsplit' hC).symm

/-- **(AP-E6-e, KM 2.8.4.1 for the canonical pairing)** Level compatibility:
`e_{N·M}(P, Q) = e_N(P, M • Q)` for `P ∈ E[N]` and `Q ∈ E[N·M]`. One dataset for `Q` serves
both levels (the dataset conditions are level-free); the left value reads it directly, the
right value reads its `[M]`-pullback, and `torsionSplittingEval_mulByN_pullback` equates
the two readings. -/
theorem weilPairingKM_mul_smul_right (N M₀ : ℕ)
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N)
    (hP' : P ∈ torsionPoints E t (N * M₀))
    (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t (N * M₀))
    (hMQ : M₀ • Q ∈ torsionPoints E t N) :
    weilPairingKM E hsm t (N * M₀) P hP' Q hQ =
      weilPairingKM E hsm t N P hP (M₀ • Q) hMQ := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  obtain ⟨A, hA, ι, W, hW, e, hnorm⟩ := exists_normalized_dataset E hsm t Q
  rw [weilPairingKM_eq_torsionSplittingEval E hsm t (N * M₀) P hP' Q hQ A hA W hW e hnorm,
    weilPairingKM_eq_torsionSplittingEval E hsm t N P hP (M₀ • Q) hMQ
      ((Scheme.Modules.pullback (mulByN E t M₀)).obj A)
      (hM_mulByNPullback E hsm t M₀ Q A hA)
      (fun i => mulByN E t M₀ ⁻¹ᵁ W i)
      ((mulByN E t M₀).iSup_preimage_eq_top hW)
      (fun i => localPullbackTrivializationT (mulByN E t M₀) A (W i) (e i))
      (hnorm_mulByNPullback E t M₀ A W e hnorm)]
  exact (torsionSplittingEval_mulByN_pullback E hsm t N M₀ Q hQ hMQ A hA W hW e hnorm
    P hP hP').symm

omit hsm [IsSeparated E.π] in
/-- `Point.asSection` commutes with integer scalars: both layers of
`asSection_eq_baseChangeEquiv_symm` are additive. -/
theorem asSection_zsmul {T : Scheme.{u}} (g : T ⟶ S) (a : ℤ) (y : E.Point g) :
    EllipticCurve.Point.asSection E g (a • y) =
      a • EllipticCurve.Point.asSection E g y := by
  rw [asSection_eq_baseChangeEquiv_symm, asSection_eq_baseChangeEquiv_symm,
    map_zsmul, map_zsmul]

end Compatibility

end ModularCurves
