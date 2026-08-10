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

end ModularCurves
