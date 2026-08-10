/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMNaturality
import ModularCurves.Moduli.Representability

/-!
# Curve-direction naturality of the Katz–Mazur pairing (YR-1, KM 2.8.4.2)

`weilPairing_torsionMapOfEllHom` (YRho.lean) asserts that the register pairing commutes
with an `Ell/ℚ`-morphism `g : A ⟶ B`. Since the register is filled by the KM value, this
is now a theorem-obligation of the backend: the KM value is natural in the *curve* slot
along the cartesian square of `g`. Mirror of the proven `T`-direction
(`weilPairingKM_restrictBase`, AP-E1-NAT1/NAT2), with the connecting morphism replaced by
the **pasting map** between the two pullback presentations

  `pullback A.π t ⟶ pullback B.π (t ≫ g.baseHom)`

induced by `g.top`. This file (step 1) builds the pasting map and its three commutation
squares (structure/zero/`[N]`), and the section transport. Source: KM 2.8.4.2 ("the
pairing commutes with base change" — the curve leg).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

-- The `(E.baseChange t).E` vs `pullback E.π t` semireducible wall (the v4.33 idiom, as in
-- `ModularCurve/YRho.lean`): the two spellings are definitionally equal but not at
-- `implicit` transparency, which every `rw` motive check uses.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurves

variable {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B) {T : Scheme.{0}} (t : T ⟶ A.base)

/-- **(YR-1a-i)** The pasting map between the two pullback presentations of the pulled
family: on the `A`-presentation it is `g.top` on the curve leg and the identity on the
`T`-leg. -/
noncomputable def pastingMap : pullback A.curve.π t ⟶ pullback B.curve.π (t ≫ g.baseHom) :=
  pullback.lift (pullback.fst A.curve.π t ≫ g.top) (pullback.snd A.curve.π t) (by
    rw [Category.assoc, g.isPullback.w, ← Category.assoc, pullback.condition,
      Category.assoc])

@[reassoc (attr := simp)]
theorem pastingMap_fst :
    pastingMap g t ≫ pullback.fst B.curve.π (t ≫ g.baseHom) =
      pullback.fst A.curve.π t ≫ g.top :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pastingMap_snd :
    pastingMap g t ≫ pullback.snd B.curve.π (t ≫ g.baseHom) =
      pullback.snd A.curve.π t :=
  pullback.lift_snd _ _ _

/-- The zero sections paste: `0_A ≫ pm = 0_B`. -/
theorem baseChangeZero_pastingMap :
    baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t ≫ pastingMap g t =
      baseChangeZero B.curve.π B.curve.zero B.curve.zero_π (t ≫ g.baseHom) := by
  have hAfst : baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t ≫
      pullback.fst A.curve.π t = t ≫ A.curve.zero := pullback.lift_fst _ _ _
  have hBfst : baseChangeZero B.curve.π B.curve.zero B.curve.zero_π (t ≫ g.baseHom) ≫
      pullback.fst B.curve.π (t ≫ g.baseHom) = (t ≫ g.baseHom) ≫ B.curve.zero :=
    pullback.lift_fst _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, pastingMap_fst, ← Category.assoc, hAfst, hBfst,
      Category.assoc, g.zero_w, ← Category.assoc]
  · rw [Category.assoc, pastingMap_snd, baseChangeZero_snd, baseChangeZero_snd]

/-- `[N]` pastes: `pm ≫ [N]_B = [N]_A ≫ pm`. -/
theorem pastingMap_mulByN (N : ℕ) :
    pastingMap g t ≫ mulByN B.curve (t ≫ g.baseHom) N =
      mulByN A.curve t N ≫ pastingMap g t := by
  have hBfst : mulByN B.curve (t ≫ g.baseHom) N ≫ pullback.fst B.curve.π (t ≫ g.baseHom)
      = pullback.fst B.curve.π (t ≫ g.baseHom) ≫ B.curve.mulByHom (N : ℤ) :=
    EllipticCurve.mulByHom_baseChange_fst B.curve (t ≫ g.baseHom) (N : ℤ)
  have hAfst : mulByN A.curve t N ≫ pullback.fst A.curve.π t
      = pullback.fst A.curve.π t ≫ A.curve.mulByHom (N : ℤ) :=
    EllipticCurve.mulByHom_baseChange_fst A.curve t (N : ℤ)
  have hBsnd : mulByN B.curve (t ≫ g.baseHom) N ≫ pullback.snd B.curve.π (t ≫ g.baseHom)
      = pullback.snd B.curve.π (t ≫ g.baseHom) :=
    EllipticCurve.mulByHom_baseChange_snd B.curve (t ≫ g.baseHom) (N : ℤ)
  have hAsnd : mulByN A.curve t N ≫ pullback.snd A.curve.π t = pullback.snd A.curve.π t :=
    EllipticCurve.mulByHom_baseChange_snd A.curve t (N : ℤ)
  apply pullback.hom_ext
  · rw [Category.assoc, hBfst, ← Category.assoc, pastingMap_fst, Category.assoc,
      ← EllHom.mulByHom_top (R := CommRingCat.of ℚ) (f := g) (n := (N : ℤ)),
      ← Category.assoc, ← hAfst, Category.assoc, ← pastingMap_fst g t, ← Category.assoc]
  · rw [Category.assoc, hBsnd, pastingMap_snd, Category.assoc, pastingMap_snd, hAsnd]

/-- **(YR-1a-i, section transport)** Push a section of the `A`-presentation along the
pasting map. -/
noncomputable def pushSection (P : (A.curve.baseChange t).Point (𝟙 T)) :
    (B.curve.baseChange (t ≫ g.baseHom)).Point (𝟙 T) :=
  ⟨(P.1 : T ⟶ pullback A.curve.π t) ≫ pastingMap g t, by
    rw [Category.assoc]
    show (P.1 : T ⟶ pullback A.curve.π t) ≫ pastingMap g t ≫
      pullback.snd B.curve.π (t ≫ g.baseHom) = 𝟙 T
    rw [pastingMap_snd]
    exact P.2⟩

@[simp] theorem pushSection_coe (P : (A.curve.baseChange t).Point (𝟙 T)) :
    ((pushSection g t P).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom)) =
      (P.1 : T ⟶ pullback A.curve.π t) ≫ pastingMap g t := rfl

/-- Torsion membership transports along the pasting map. -/
theorem pushSection_mem_torsionPoints {N : ℕ} {P : (A.curve.baseChange t).Point (𝟙 T)}
    (hP : P ∈ torsionPoints A.curve t N) :
    pushSection g t P ∈ torsionPoints B.curve (t ≫ g.baseHom) N := by
  have h := comp_mulByN_eq_baseChangeZero A.curve t N P hP
  refine (EllipticCurve.smul_eq_zero_iff_comp_mulByHom
    (B.curve.baseChange (t ≫ g.baseHom)) (𝟙 T) N (pushSection g t P)).mpr ?_
  rw [Category.id_comp]
  show ((pushSection g t P).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom))
      ≫ mulByN B.curve (t ≫ g.baseHom) N =
    baseChangeZero B.curve.π B.curve.zero B.curve.zero_π (t ≫ g.baseHom)
  rw [pushSection_coe, Category.assoc, pastingMap_mulByN, ← Category.assoc, h,
    baseChangeZero_pastingMap]

/-- **(YR-1a-ii, step 0)** The pasted pullback square: `pullback A.π t` is also a pullback
of `B.π` along `t ≫ g.baseHom` (paste the defining square with the cartesian square of
`g`). -/
theorem isPullback_pasting :
    IsPullback (pullback.fst A.curve.π t ≫ g.top) (pullback.snd A.curve.π t)
      B.curve.π (t ≫ g.baseHom) :=
  (IsPullback.of_hasPullback A.curve.π t).paste_horiz g.isPullback

/-- The pasting map is the comparison of two pullback presentations, hence an
isomorphism. -/
instance isIso_pastingMap : IsIso (pastingMap g t) := by
  have h : pastingMap g t = (isPullback_pasting g t).isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pastingMap_fst, IsPullback.isoPullback_hom_fst]
    · rw [pastingMap_snd, IsPullback.isoPullback_hom_snd]
  rw [h]
  infer_instance

/-- **(YR-1a-ii, step 1)** The section square along the pasting map is cartesian. -/
theorem isPullback_pushSection (Q : (A.curve.baseChange t).Point (𝟙 T)) :
    IsPullback (Q.1 : T ⟶ pullback A.curve.π t) (𝟙 T) (pastingMap g t)
      ((pushSection g t Q).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom)) := by
  have hsq : CommSq (Q.1 : T ⟶ pullback A.curve.π t) (𝟙 T) (pastingMap g t)
      ((pushSection g t Q).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom)) :=
    ⟨by rw [pushSection_coe, Category.id_comp]⟩
  exact IsPullback.of_vert_isIso hsq

/-- **(YR-1a-ii, step 2)** The kernel of a section is the comap of the pushed section's
kernel along the pasting map — the ideal-sheaf half of the curve-direction `κ`-naturality.
Mirrors `ker_restrictBase` (AP-E1-NAT1 step 2). -/
theorem ker_pushSection (Q : (A.curve.baseChange t).Point (𝟙 T)) :
    (Q.1 : T ⟶ pullback A.curve.π t).ker =
      (Scheme.Hom.ker ((pushSection g t Q).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom))).comap
        (pastingMap g t) := by
  haveI hsepB : IsSeparated (pullback.snd B.curve.π (t ≫ g.baseHom)) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) B.curve.π (t ≫ g.baseHom)
      inferInstance
  haveI : IsClosedImmersion
      ((pushSection g t Q).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom)) :=
    RelEffCartierDiv.SectionsIdeal.isClosedImmersion (pushSection g t Q).2
  rw [← (isPullback_pushSection g t Q).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
    ((pushSection g t Q).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom)) (pastingMap g t)

/-- **(YR-1a-ii, step 3)** The class of a section divisor is natural along the pasting
map: `Pic(pm)([𝒪(pushQ)]) = [𝒪(Q)]`. Transcription of `sectionCls_restrictBase`
(AP-E1-NAT1 step 3) with the connecting morphism `baseChangeMap ↦ pastingMap`. -/
theorem sectionCls_pastingMap (Q : (A.curve.baseChange t).Point (𝟙 T)) :
    Scheme.Pic.map (pastingMap g t)
        (sectionCls B.curve B.curve.smooth (t ≫ g.baseHom)
          ((pushSection g t Q).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom))
          (pushSection g t Q).2) =
      sectionCls A.curve A.curve.smooth t (Q.1 : T ⟶ pullback A.curve.π t) Q.2 := by
  letI := Scheme.Modules.monoidalCategory (pullback B.curve.π (t ≫ g.baseHom))
  letI := Scheme.Modules.monoidalCategory (pullback A.curve.π t)
  haveI hsepB : IsSeparated (pullback.snd B.curve.π (t ≫ g.baseHom)) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) B.curve.π (t ≫ g.baseHom)
      inferInstance
  haveI hsepA : IsSeparated (pullback.snd A.curve.π t) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) A.curve.π t inferInstance
  have hsmB : SmoothOfRelativeDimension 1 (pullback.snd B.curve.π (t ≫ g.baseHom)) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) B.curve.π
      (t ≫ g.baseHom) B.curve.smooth
  have hsmA : SmoothOfRelativeDimension 1 (pullback.snd A.curve.π t) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) A.curve.π t
      A.curve.smooth
  have hJ : ∀ c : ↥(pullback B.curve.π (t ≫ g.baseHom)),
      ∃ V : (pullback B.curve.π (t ≫ g.baseHom)).affineOpens, c ∈ V.1 ∧
      ∃ f : Γ(pullback B.curve.π (t ≫ g.baseHom), V.1),
        (Scheme.Hom.ker ((pushSection g t Q).1 :
            T ⟶ pullback B.curve.π (t ≫ g.baseHom))).ideal V = Ideal.span {f} ∧
          f ∈ nonZeroDivisors Γ(pullback B.curve.π (t ≫ g.baseHom), V.1) :=
    (RelEffCartierDiv.sectionDivisor_isOfficial hsmB
      ((pushSection g t Q).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom))
      (pushSection g t Q).2).locallyPrincipal
  have hJ' : ∀ c : ↥(pullback A.curve.π t), ∃ V : (pullback A.curve.π t).affineOpens,
      c ∈ V.1 ∧ ∃ f : Γ(pullback A.curve.π t, V.1),
        ((Scheme.Hom.ker ((pushSection g t Q).1 :
            T ⟶ pullback B.curve.π (t ≫ g.baseHom))).comap
          (pastingMap g t)).ideal V = Ideal.span {f} ∧
          f ∈ nonZeroDivisors Γ(pullback A.curve.π t, V.1) := by
    rw [← ker_pushSection g t Q]
    exact (RelEffCartierDiv.sectionDivisor_isOfficial hsmA
      (Q.1 : T ⟶ pullback A.curve.π t) Q.2).locallyPrincipal
  obtain ⟨eiso⟩ := nonempty_pullback_idealModule (pastingMap g t)
    (Scheme.Hom.ker ((pushSection g t Q).1 :
      T ⟶ pullback B.curve.π (t ≫ g.baseHom))) hJ hJ'
  have hcore : Scheme.Pic.map (pastingMap g t)
      (((RelEffCartierDiv.sectionDivisor (pullback.snd B.curve.π (t ≫ g.baseHom))
          ((pushSection g t Q).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom))
          (pushSection g t Q).2).isInvertible_idealModule
        (RelEffCartierDiv.sectionDivisor_isOfficial hsmB _
          (pushSection g t Q).2)).isUnit_toSkeleton.unit) =
      ((RelEffCartierDiv.sectionDivisor (pullback.snd A.curve.π t)
          (Q.1 : T ⟶ pullback A.curve.π t) Q.2).isInvertible_idealModule
        (RelEffCartierDiv.sectionDivisor_isOfficial hsmA _ Q.2)).isUnit_toSkeleton.unit := by
    refine Units.ext ?_
    refine (Scheme.Pic.map_val (pastingMap g t) _).trans ?_
    refine (congrArg (Scheme.Modules.pullback (pastingMap g t)).mapSkeleton.obj
      (IsUnit.unit_spec _)).trans ?_
    refine (Functor.mapSkeleton_obj_toSkeleton _ _).trans ?_
    refine (toSkeleton_eq_toSkeleton_iff.mpr
      ⟨eiso ≪≫ eqToIso (congrArg Scheme.Modules.idealModule
        (ker_pushSection g t Q).symm)⟩).trans ?_
    exact (IsUnit.unit_spec _).symm
  refine Eq.trans (map_inv (Scheme.Pic.map (pastingMap g t)) _) ?_
  exact congrArg (·⁻¹) hcore

/-- The zero point pushes to the zero point. -/
theorem pushSection_zero :
    pushSection g t (0 : (A.curve.baseChange t).Point (𝟙 T)) =
      (0 : (B.curve.baseChange (t ≫ g.baseHom)).Point (𝟙 T)) := by
  have hzvalA : ((0 : (A.curve.baseChange t).Point (𝟙 T)).1 : T ⟶ pullback A.curve.π t) =
      baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t :=
    ((A.curve.baseChange t).point_zero_val (𝟙 T)).trans (Category.id_comp _)
  have hzvalB : ((0 : (B.curve.baseChange (t ≫ g.baseHom)).Point (𝟙 T)).1 :
      T ⟶ pullback B.curve.π (t ≫ g.baseHom)) =
      baseChangeZero B.curve.π B.curve.zero B.curve.zero_π (t ≫ g.baseHom) :=
    ((B.curve.baseChange (t ≫ g.baseHom)).point_zero_val (𝟙 T)).trans (Category.id_comp _)
  refine Subtype.ext ?_
  show ((0 : (A.curve.baseChange t).Point (𝟙 T)).1 : T ⟶ pullback A.curve.π t) ≫
      pastingMap g t =
    ((0 : (B.curve.baseChange (t ≫ g.baseHom)).Point (𝟙 T)).1 :
      T ⟶ pullback B.curve.π (t ≫ g.baseHom))
  rw [hzvalA, hzvalB, baseChangeZero_pastingMap]

/-- **(YR-1a-ii, step 4)** The zero class is natural along the pasting map. -/
theorem zeroCls_pastingMap :
    Scheme.Pic.map (pastingMap g t)
        (zeroCls B.curve B.curve.smooth (t ≫ g.baseHom)) =
      zeroCls A.curve A.curve.smooth t := by
  have hzvalA : ((0 : (A.curve.baseChange t).Point (𝟙 T)).1 : T ⟶ pullback A.curve.π t) =
      baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t :=
    ((A.curve.baseChange t).point_zero_val (𝟙 T)).trans (Category.id_comp _)
  have hzvalB : ((0 : (B.curve.baseChange (t ≫ g.baseHom)).Point (𝟙 T)).1 :
      T ⟶ pullback B.curve.π (t ≫ g.baseHom)) =
      baseChangeZero B.curve.π B.curve.zero B.curve.zero_π (t ≫ g.baseHom) :=
    ((B.curve.baseChange (t ≫ g.baseHom)).point_zero_val (𝟙 T)).trans (Category.id_comp _)
  calc Scheme.Pic.map (pastingMap g t)
        (zeroCls B.curve B.curve.smooth (t ≫ g.baseHom))
      = Scheme.Pic.map (pastingMap g t)
          (sectionCls B.curve B.curve.smooth (t ≫ g.baseHom)
            ((pushSection g t (0 : (A.curve.baseChange t).Point (𝟙 T))).1 :
              T ⟶ pullback B.curve.π (t ≫ g.baseHom))
            (pushSection g t (0 : (A.curve.baseChange t).Point (𝟙 T))).2) :=
        congrArg _ (sectionCls_congr B.curve B.curve.smooth (t ≫ g.baseHom) _ _
          (hzvalB.symm.trans (congrArg (fun P :
              (B.curve.baseChange (t ≫ g.baseHom)).Point (𝟙 T) =>
            (P.1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom)))
            (pushSection_zero g t).symm)))
    _ = sectionCls A.curve A.curve.smooth t
          ((0 : (A.curve.baseChange t).Point (𝟙 T)).1 : T ⟶ pullback A.curve.π t)
          (0 : (A.curve.baseChange t).Point (𝟙 T)).2 :=
        sectionCls_pastingMap g t 0
    _ = zeroCls A.curve A.curve.smooth t :=
        sectionCls_congr A.curve A.curve.smooth t _ _ hzvalA

/-- **(YR-1a-ii, COMPLETE)** `κ` is natural along the pasting map:
`Pic(pm)(κ_B(pushQ)) = κ_A(Q)`. Transcription of `kappa_restrictBase` (AP-E1-NAT1) with
the two commuting squares supplied by `pastingMap_snd` and `baseChangeZero_pastingMap`. -/
theorem kappa_pastingMap (Q : (A.curve.baseChange t).Point (𝟙 T)) :
    Scheme.Pic.map (pastingMap g t)
        (kappa B.curve B.curve.smooth (t ≫ g.baseHom) (pushSection g t Q)) =
      kappa A.curve A.curve.smooth t Q := by
  have hval : ∀ (x : Scheme.Pic (pullback B.curve.π (t ≫ g.baseHom))),
      ((picRelProj B.curve.π B.curve.zero B.curve.zero_π (t ≫ g.baseHom) x :
        picRel B.curve.π B.curve.zero B.curve.zero_π (t ≫ g.baseHom)) :
        Scheme.Pic (pullback B.curve.π (t ≫ g.baseHom))) =
      x * (Scheme.Pic.map (pullback.snd B.curve.π (t ≫ g.baseHom))
        (Scheme.Pic.map (baseChangeZero B.curve.π B.curve.zero B.curve.zero_π
          (t ≫ g.baseHom)) x))⁻¹ := fun _ => rfl
  have hval' : ∀ (x : Scheme.Pic (pullback A.curve.π t)),
      ((picRelProj A.curve.π A.curve.zero A.curve.zero_π t x :
        picRel A.curve.π A.curve.zero A.curve.zero_π t) :
        Scheme.Pic (pullback A.curve.π t)) =
      x * (Scheme.Pic.map (pullback.snd A.curve.π t)
        (Scheme.Pic.map (baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t) x))⁻¹ :=
    fun _ => rfl
  set x := sectionCls B.curve B.curve.smooth (t ≫ g.baseHom)
      ((pushSection g t Q).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom))
      (pushSection g t Q).2 *
    (zeroCls B.curve B.curve.smooth (t ≫ g.baseHom))⁻¹ with hx
  set x' := sectionCls A.curve A.curve.smooth t (Q.1 : T ⟶ pullback A.curve.π t) Q.2 *
    (zeroCls A.curve A.curve.smooth t)⁻¹ with hx'
  have hratio : Scheme.Pic.map (pastingMap g t) x = x' := by
    rw [hx, hx', map_mul, map_inv, sectionCls_pastingMap g t Q, zeroCls_pastingMap g t]
  have hsq1 : ∀ y, Scheme.Pic.map (pastingMap g t)
      (Scheme.Pic.map (pullback.snd B.curve.π (t ≫ g.baseHom)) y) =
      Scheme.Pic.map (pullback.snd A.curve.π t) y := by
    intro y
    calc Scheme.Pic.map (pastingMap g t)
          (Scheme.Pic.map (pullback.snd B.curve.π (t ≫ g.baseHom)) y)
        = Scheme.Pic.map (pastingMap g t ≫ pullback.snd B.curve.π (t ≫ g.baseHom)) y := by
          rw [Scheme.Pic.map_comp]; rfl
      _ = Scheme.Pic.map (pullback.snd A.curve.π t) y := by rw [pastingMap_snd]
  have hsq2 : ∀ y, Scheme.Pic.map (baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t)
      (Scheme.Pic.map (pastingMap g t) y) =
      Scheme.Pic.map (baseChangeZero B.curve.π B.curve.zero B.curve.zero_π
        (t ≫ g.baseHom)) y := by
    intro y
    calc Scheme.Pic.map (baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t)
          (Scheme.Pic.map (pastingMap g t) y)
        = Scheme.Pic.map (baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t ≫
            pastingMap g t) y := by
          rw [Scheme.Pic.map_comp]; rfl
      _ = Scheme.Pic.map (baseChangeZero B.curve.π B.curve.zero B.curve.zero_π
            (t ≫ g.baseHom)) y := by rw [baseChangeZero_pastingMap]
  calc Scheme.Pic.map (pastingMap g t)
        (kappa B.curve B.curve.smooth (t ≫ g.baseHom) (pushSection g t Q))
      = Scheme.Pic.map (pastingMap g t)
          (x * (Scheme.Pic.map (pullback.snd B.curve.π (t ≫ g.baseHom))
            (Scheme.Pic.map (baseChangeZero B.curve.π B.curve.zero B.curve.zero_π
              (t ≫ g.baseHom)) x))⁻¹) :=
        congrArg _ ((kappa_eq_picRelProj B.curve B.curve.smooth (t ≫ g.baseHom)
          (pushSection g t Q)).trans (hval x))
    _ = Scheme.Pic.map (pastingMap g t) x *
          (Scheme.Pic.map (pastingMap g t)
            (Scheme.Pic.map (pullback.snd B.curve.π (t ≫ g.baseHom))
              (Scheme.Pic.map (baseChangeZero B.curve.π B.curve.zero B.curve.zero_π
                (t ≫ g.baseHom)) x)))⁻¹ := by
        rw [map_mul, map_inv]
    _ = x' * (Scheme.Pic.map (pullback.snd A.curve.π t)
          (Scheme.Pic.map (baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t) x'))⁻¹ := by
        rw [hsq1, ← hsq2, hratio]
    _ = kappa A.curve A.curve.smooth t Q :=
        ((kappa_eq_picRelProj A.curve A.curve.smooth t Q).trans (hval' x')).symm

/-- **(YR-1a-iii, hM)** The `pm`-pulled dataset's module represents the `A`-side
`κ`-class: mirror of `hM_localPullback` with `kappa_pastingMap`. -/
theorem hM_pastingMap (Q : (A.curve.baseChange t).Point (𝟙 T))
    (M : (pullback B.curve.π (t ≫ g.baseHom)).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback B.curve.π (t ≫ g.baseHom))
      (kappa B.curve B.curve.smooth (t ≫ g.baseHom) (pushSection g t Q)).val =
        toSkeleton M) :
    letI := Scheme.Modules.monoidalCategory (pullback A.curve.π t)
    (kappa A.curve A.curve.smooth t Q).val =
      toSkeleton ((Scheme.Modules.pullback (pastingMap g t)).obj M) := by
  letI := Scheme.Modules.monoidalCategory (pullback B.curve.π (t ≫ g.baseHom))
  letI := Scheme.Modules.monoidalCategory (pullback A.curve.π t)
  have hM'' : (kappa B.curve B.curve.smooth (t ≫ g.baseHom) (pushSection g t Q)).val =
      toSkeleton M := hM
  calc (kappa A.curve A.curve.smooth t Q).val
      = (Scheme.Pic.map (pastingMap g t)
          (kappa B.curve B.curve.smooth (t ≫ g.baseHom) (pushSection g t Q))).val :=
        congrArg Units.val (kappa_pastingMap g t Q).symm
    _ = (Scheme.Modules.pullback (pastingMap g t)).mapSkeleton.obj
          (kappa B.curve B.curve.smooth (t ≫ g.baseHom) (pushSection g t Q)).val :=
        Scheme.Pic.map_val _ _
    _ = (Scheme.Modules.pullback (pastingMap g t)).mapSkeleton.obj (toSkeleton M) :=
        congrArg _ hM''
    _ = toSkeleton ((Scheme.Modules.pullback (pastingMap g t)).obj M) :=
        Functor.mapSkeleton_obj_toSkeleton _ M

/-- **(YR-1a-iii, hnorm)** The `pm`-pulled dataset's cocycle is normalised along the
`A`-side zero section: mirror of `hnorm_localPullback` with the zero square
`baseChangeZero_pastingMap`. -/
theorem hnorm_pastingMap (M : (pullback B.curve.π (t ≫ g.baseHom)).Modules)
    {ι : Type*} (W : ι → (pullback B.curve.π (t ≫ g.baseHom)).Opens)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit
        ((pullback B.curve.π (t ≫ g.baseHom)).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero B.curve.π B.curve.zero B.curve.zero_π
        (t ≫ g.baseHom)) (W i ⊓ W j)) (i j : ι) :
    transitionUnitOfCover ((Scheme.Modules.pullback (pastingMap g t)).obj M)
        (fun i => pastingMap g t ⁻¹ᵁ W i)
        (fun i => localPullbackTrivializationT (pastingMap g t) M (W i) (e i)) i j ∈
      sectionUnits (baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t)
        (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j) := by
  have hzcomp : baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t ≫ pastingMap g t =
      𝟙 T ≫ baseChangeZero B.curve.π B.curve.zero B.curve.zero_π (t ≫ g.baseHom) :=
    (baseChangeZero_pastingMap g t).trans (Category.id_comp _).symm
  rw [mem_sectionUnits_iff,
    transitionUnitOfCover_localPullback (pastingMap g t) M W e i j]
  refine ((congrArg (sectionEval (baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t)
      (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j))
      (map_app_eq_unitPullback (pastingMap g t) (W i ⊓ W j)
        (transitionUnitOfCover M W e i j))).trans ?_)
  refine ((sectionEval_unitPullback (pastingMap g t)
    (baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t) (le_of_eq rfl)
    (transitionUnitOfCover M W e i j)).trans ?_)
  refine ((resUnit_sectionEval_congr hzcomp (W i ⊓ W j)
    (transitionUnitOfCover M W e i j)
    ((baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t).preimage_mono
      (le_of_eq rfl))
    (by rw [← hzcomp]
        exact (baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t).preimage_mono
          (le_of_eq rfl))).trans ?_)
  refine ((congrArg _ ((sectionEval_comp (𝟙 T)
    (baseChangeZero B.curve.π B.curve.zero B.curve.zero_π (t ≫ g.baseHom))
    (W i ⊓ W j) (transitionUnitOfCover M W e i j)).trans ?_)).trans (map_one _))
  rw [show sectionEval (baseChangeZero B.curve.π B.curve.zero B.curve.zero_π
      (t ≫ g.baseHom)) (W i ⊓ W j) (transitionUnitOfCover M W e i j) = 1 from hnorm i j]
  exact map_one _

/-- **(YR-1a, THE ENGINE)** The Katz–Mazur value is natural in the curve slot: computing
over the `A`-presentation with the `pm`-pulled dataset equals the `B`-value at the pushed
sections. Transcription of `torsionSplittingEval_restrictBase` (AP-E1-NAT2) along the
pasting map; since both presentations share the base `T`, no `unitPullback` appears in
the conclusion. -/
theorem torsionSplittingEval_pastingMap (N : ℕ)
    (Q : (A.curve.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints A.curve t N)
    (M : (pullback B.curve.π (t ≫ g.baseHom)).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback B.curve.π (t ≫ g.baseHom))
      (kappa B.curve B.curve.smooth (t ≫ g.baseHom) (pushSection g t Q)).val =
        toSkeleton M)
    {ι : Type*} (W : ι → (pullback B.curve.π (t ≫ g.baseHom)).Opens) (hW : iSup W = ⊤)
    (e : ∀ i, M.over (W i) ≅
      _root_.SheafOfModules.unit
        ((pullback B.curve.π (t ≫ g.baseHom)).ringCatSheaf.over (W i)))
    (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
      sectionUnits (baseChangeZero B.curve.π B.curve.zero B.curve.zero_π
        (t ≫ g.baseHom)) (W i ⊓ W j))
    (P : (A.curve.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints A.curve t N) :
    torsionSplittingEval A.curve A.curve.smooth t N Q hQ
        ((Scheme.Modules.pullback (pastingMap g t)).obj M) (hM_pastingMap g t Q M hM)
        (fun i => pastingMap g t ⁻¹ᵁ W i) ((pastingMap g t).iSup_preimage_eq_top hW)
        (fun i => localPullbackTrivializationT (pastingMap g t) M (W i) (e i))
        (fun i j => hnorm_pastingMap g t M W e hnorm i j) P hP =
      torsionSplittingEval B.curve B.curve.smooth (t ≫ g.baseHom) N (pushSection g t Q)
        (pushSection_mem_torsionPoints g t hQ) M hM W hW e hnorm (pushSection g t P)
        (pushSection_mem_torsionPoints g t hP) := by
  obtain ⟨h, hn, hsplit⟩ :=
    exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints B.curve
      B.curve.smooth (t ≫ g.baseHom) N (pushSection g t Q)
      (pushSection_mem_torsionPoints g t hQ) M hM W hW e hnorm
  have hpatheq : ∀ i, mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i) =
      pastingMap g t ⁻¹ᵁ (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ W i) := by
    intro i
    have hcomm := pastingMap_mulByN g t N
    calc mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i)
        = (mulByN A.curve t N ≫ pastingMap g t) ⁻¹ᵁ W i := rfl
      _ = (pastingMap g t ≫ mulByN B.curve (t ≫ g.baseHom) N) ⁻¹ᵁ W i := by rw [hcomm]
      _ = pastingMap g t ⁻¹ᵁ (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ W i) := rfl
  have hpath : ∀ i, mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i) ≤
      pastingMap g t ⁻¹ᵁ (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ W i) := fun i =>
    le_of_eq (hpatheq i)
  set h' : ∀ i, Γ(pullback A.curve.π t,
      mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i))ˣ :=
    fun i => unitPullback (pastingMap g t) (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ W i)
      (mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i)) (hpath i) (h i) with hh'
  have hzcomp : baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t ≫ pastingMap g t =
      𝟙 T ≫ baseChangeZero B.curve.π B.curve.zero B.curve.zero_π (t ≫ g.baseHom) :=
    (baseChangeZero_pastingMap g t).trans (Category.id_comp _).symm
  refine (eq_torsionSplittingEval A.curve A.curve.smooth t N Q hQ _
    (hM_pastingMap g t Q M hM) _ ((pastingMap g t).iSup_preimage_eq_top hW) _
    (fun i j => hnorm_pastingMap g t M W e hnorm i j) P hP h'
    (fun i => ?_) (fun i j => ?_) (fun i => ?_)).symm
  · rw [mem_sectionUnits_iff, hh']
    refine (sectionEval_unitPullback (pastingMap g t)
      (baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t) (hpath i) (h i)).trans ?_
    refine ((resUnit_sectionEval_congr hzcomp
      (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ W i) (h i)
      ((baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t).preimage_mono (hpath i))
      (by rw [← hzcomp]
          exact (baseChangeZero A.curve.π A.curve.zero A.curve.zero_π t).preimage_mono
            (hpath i))).trans ?_)
    refine (congrArg _ ((sectionEval_comp (𝟙 T)
      (baseChangeZero B.curve.π B.curve.zero B.curve.zero_π (t ≫ g.baseHom))
      (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ W i) (h i)).trans ?_)).trans (map_one _)
    rw [show sectionEval (baseChangeZero B.curve.π B.curve.zero B.curve.zero_π
        (t ≫ g.baseHom)) (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ W i) (h i) = 1 from hn i]
    exact map_one _
  · have hpullco : transitionUnitOfCover
        ((Scheme.Modules.pullback (pastingMap g t)).obj M)
        (fun i => pastingMap g t ⁻¹ᵁ W i)
        (fun i => localPullbackTrivializationT (pastingMap g t) M (W i) (e i)) i j =
        Units.map ((pastingMap g t).app (W i ⊓ W j)).hom.toMonoidHom
          (transitionUnitOfCover M W e i j) :=
      transitionUnitOfCover_localPullback (pastingMap g t) M W e i j
    have hle : mulByN A.curve t N ⁻¹ᵁ
        (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j) ≤
        pastingMap g t ⁻¹ᵁ (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ (W i ⊓ W j)) :=
      inf_le_inf (hpath i) (hpath j)
    have hb1 : Units.map ((mulByN A.curve t N).app
        (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j)).hom.toMonoidHom
        (Units.map ((pastingMap g t).app (W i ⊓ W j)).hom.toMonoidHom
          (transitionUnitOfCover M W e i j)) =
        unitPullback (mulByN A.curve t N ≫ pastingMap g t) (W i ⊓ W j)
          (mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j))
          (le_of_eq rfl) (transitionUnitOfCover M W e i j) :=
      (congrArg (Units.map ((mulByN A.curve t N).app
          (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j)).hom.toMonoidHom)
        (map_app_eq_unitPullback (pastingMap g t) (W i ⊓ W j)
          (transitionUnitOfCover M W e i j))).trans
      ((map_app_eq_unitPullback (mulByN A.curve t N)
          (pastingMap g t ⁻¹ᵁ (W i ⊓ W j))
          (unitPullback (pastingMap g t) (W i ⊓ W j)
            (pastingMap g t ⁻¹ᵁ (W i ⊓ W j)) le_rfl
            (transitionUnitOfCover M W e i j))).trans
        (unitPullback_unitPullback (mulByN A.curve t N) (pastingMap g t)
          le_rfl le_rfl (transitionUnitOfCover M W e i j)))
    have hb2 : unitPullback (mulByN A.curve t N ≫ pastingMap g t) (W i ⊓ W j)
        (mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j))
        (le_of_eq rfl) (transitionUnitOfCover M W e i j) =
        unitPullback (pastingMap g t ≫ mulByN B.curve (t ≫ g.baseHom) N) (W i ⊓ W j)
          (mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j))
          hle (transitionUnitOfCover M W e i j) :=
      unitPullback_congr (pastingMap_mulByN g t N).symm (W i ⊓ W j)
        (mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j))
        (le_of_eq rfl) hle (transitionUnitOfCover M W e i j)
    have hb3 : unitPullback (pastingMap g t ≫ mulByN B.curve (t ≫ g.baseHom) N)
        (W i ⊓ W j)
        (mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j))
        hle (transitionUnitOfCover M W e i j) =
        unitPullback (pastingMap g t) (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ (W i ⊓ W j))
          (mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j))
          hle (Units.map ((mulByN B.curve (t ≫ g.baseHom) N).app
            (W i ⊓ W j)).hom.toMonoidHom (transitionUnitOfCover M W e i j)) :=
      ((unitPullback_unitPullback (pastingMap g t) (mulByN B.curve (t ≫ g.baseHom) N)
          le_rfl hle (transitionUnitOfCover M W e i j)).symm).trans
        (congrArg (unitPullback (pastingMap g t)
            (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ (W i ⊓ W j))
            (mulByN A.curve t N ⁻¹ᵁ
              (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j)) hle)
          (map_app_eq_unitPullback (mulByN B.curve (t ≫ g.baseHom) N) (W i ⊓ W j)
            (transitionUnitOfCover M W e i j)).symm)
    have hb4 : unitPullback (pastingMap g t)
        (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ (W i ⊓ W j))
        (mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j))
        hle (Units.map ((mulByN B.curve (t ≫ g.baseHom) N).app
          (W i ⊓ W j)).hom.toMonoidHom (transitionUnitOfCover M W e i j)) =
        Scheme.resUnit (inf_le_left :
            mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i) ⊓
              mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W j) ≤
            mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i)) (h' i) *
          (Scheme.resUnit (inf_le_right :
              mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i) ⊓
                mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W j) ≤
              mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W j)) (h' j))⁻¹ := by
      refine (congrArg (unitPullback (pastingMap g t)
        (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ (W i ⊓ W j))
        (mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j)) hle)
        (hsplit i j)).trans ?_
      refine ((map_mul _ _ _).trans ?_)
      refine ((congrArg (_ * ·) (map_inv _ _)).trans ?_)
      rw [hh']
      exact congrArg₂ (fun x y => x * y⁻¹)
        ((unitPullback_resUnit (pastingMap g t) _ _ (h i)).trans
          (resUnit_unitPullback (pastingMap g t) (hpath i) _ (h i)).symm)
        ((unitPullback_resUnit (pastingMap g t) _ _ (h j)).trans
          (resUnit_unitPullback (pastingMap g t) (hpath j) _ (h j)).symm)
    exact (congrArg (Units.map ((mulByN A.curve t N).app
        (pastingMap g t ⁻¹ᵁ W i ⊓ pastingMap g t ⁻¹ᵁ W j)).hom.toMonoidHom)
      hpullco).trans (hb1.trans (hb2.trans (hb3.trans hb4)))
  · have hspec := resUnit_torsionSplittingEval B.curve B.curve.smooth (t ≫ g.baseHom) N
      (pushSection g t Q) (pushSection_mem_torsionPoints g t hQ) M hM W hW e hnorm
      (pushSection g t P) (pushSection_mem_torsionPoints g t hP) h hn hsplit i
    have hPcomp : (P.1 : T ⟶ pullback A.curve.π t) ≫ pastingMap g t =
        ((pushSection g t P).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom)) :=
      (pushSection_coe g t P).symm
    have p2 : (P.1 : T ⟶ pullback A.curve.π t) ⁻¹ᵁ
        (mulByN A.curve t N ⁻¹ᵁ (pastingMap g t ⁻¹ᵁ W i)) ≤
        ((pushSection g t P).1 : T ⟶ pullback B.curve.π (t ≫ g.baseHom)) ⁻¹ᵁ
          (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ W i) := by
      rw [← hPcomp]
      exact (P.1 : T ⟶ pullback A.curve.π t).preimage_mono (hpath i)
    refine Eq.trans ?_ ((sectionEval_unitPullback (pastingMap g t)
      (P.1 : T ⟶ pullback A.curve.π t) (hpath i) (h i)).symm)
    refine Eq.trans ?_ ((resUnit_sectionEval_congr hPcomp
      (mulByN B.curve (t ≫ g.baseHom) N ⁻¹ᵁ W i) (h i)
      ((P.1 : T ⟶ pullback A.curve.π t).preimage_mono (hpath i)) p2).symm)
    refine Eq.trans ?_ (congrArg (Scheme.resUnit p2) hspec)
    exact (Scheme.resUnit_resUnit _ _ _).symm

/-- **(YR-1b)** The canonical pairing is natural in the curve slot: the `A`-value of two
torsion sections equals the `B`-value of their pushes. Mirror of
`weilPairingKM_restrictBase` (AP-E1-NAT3), reading both sides through a `B`-side chosen
dataset and its `pm`-pullback via the engine. -/
theorem weilPairingKM_pastingMap (N : ℕ)
    (P : (A.curve.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints A.curve t N)
    (Q : (A.curve.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints A.curve t N) :
    weilPairingKM A.curve A.curve.smooth t N P hP Q hQ =
      weilPairingKM B.curve B.curve.smooth (t ≫ g.baseHom) N
        (pushSection g t P) (pushSection_mem_torsionPoints g t hP)
        (pushSection g t Q) (pushSection_mem_torsionPoints g t hQ) := by
  letI := Scheme.Modules.monoidalCategory (pullback B.curve.π (t ≫ g.baseHom))
  obtain ⟨M, hM, ι, W, hW, e, hnorm⟩ := exists_normalized_dataset B.curve B.curve.smooth
    (t ≫ g.baseHom) (pushSection g t Q)
  rw [weilPairingKM_eq_torsionSplittingEval B.curve B.curve.smooth (t ≫ g.baseHom) N
      (pushSection g t P) (pushSection_mem_torsionPoints g t hP)
      (pushSection g t Q) (pushSection_mem_torsionPoints g t hQ) M hM W hW e hnorm,
    weilPairingKM_eq_torsionSplittingEval A.curve A.curve.smooth t N P hP Q hQ
      ((Scheme.Modules.pullback (pastingMap g t)).obj M) (hM_pastingMap g t Q M hM)
      (fun i => pastingMap g t ⁻¹ᵁ W i) ((pastingMap g t).iSup_preimage_eq_top hW)
      (fun i => localPullbackTrivializationT (pastingMap g t) M (W i) (e i))
      (fun i j => hnorm_pastingMap g t M W e hnorm i j)]
  exact torsionSplittingEval_pastingMap g t N Q hQ M hM W hW e hnorm P hP

end ModularCurves
