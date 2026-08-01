/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.ChordIdentity
import ModularCurves.ForMathlib.PullbackTensorGeneral
import ModularCurves.Picard.IdealModulePullback

/-!
# The tautological pair of points (W1-d3.0)

The chord identity has to be proved for *all* pairs of points of *all* families, and the
standard device is to prove it once for the tautological pair: over the base
`B = C ×_S C` the curve `C ×_S B` carries two canonical sections — the two projections,
read as sections of the base change — and every pair `(P, Q)` of sections of `C/S` over
a base `T` is the pullback of the tautological pair along `⟨P, Q⟩ : T ⟶ B`.

This file constructs that pair. It is pure fibre-product plumbing (no geometry), and it
is what lets the chord–tangent computation be carried out once, over a base which for
the universal Weierstrass family is a domain.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace ModularCurves

variable {C S : Scheme.{u}} (π : C ⟶ S)

/-- The base of the tautological pair: `C ×_S C`. -/
noncomputable abbrev pairBase : Scheme.{u} := pullback π π

/-- The structure morphism of the tautological pair base. -/
noncomputable abbrev pairBaseπ : pairBase π ⟶ S := pullback.fst π π ≫ π

/-- The curve, base changed to the tautological pair base. -/
noncomputable abbrev pairCurve : Scheme.{u} := pullback π (pairBaseπ π)

/-- The structure morphism of the base-changed curve. -/
noncomputable abbrev pairCurveπ : pairCurve π ⟶ pairBase π :=
  pullback.snd π (pairBaseπ π)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The first tautological point: the first projection, as a section of the
base-changed curve. -/
noncomputable def tautPoint₁ :
    { w : pairBase π ⟶ pairCurve π // w ≫ pairCurveπ π = 𝟙 (pairBase π) } :=
  ⟨pullback.lift (pullback.fst π π) (𝟙 _) (by rw [Category.id_comp]),
    pullback.lift_snd _ _ _⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The second tautological point: the second projection, as a section of the
base-changed curve. -/
noncomputable def tautPoint₂ :
    { w : pairBase π ⟶ pairCurve π // w ≫ pairCurveπ π = 𝟙 (pairBase π) } :=
  ⟨pullback.lift (pullback.snd π π) (𝟙 _)
      (by rw [Category.id_comp]; exact pullback.condition.symm),
    pullback.lift_snd _ _ _⟩

@[simp]
theorem tautPoint₁_fst :
    (tautPoint₁ π).1 ≫ pullback.fst π (pairBaseπ π) = pullback.fst π π :=
  pullback.lift_fst _ _ _

@[simp]
theorem tautPoint₂_fst :
    (tautPoint₂ π).1 ≫ pullback.fst π (pairBaseπ π) = pullback.snd π π :=
  pullback.lift_fst _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The classifying map of a pair of sections.** Two sections of `π` over a base `T`
mapping to `S` determine a map to the tautological pair base. -/
noncomputable def pairClassify {T : Scheme.{u}} (g : T ⟶ S)
    (P Q : { w : T ⟶ C // w ≫ π = g }) : T ⟶ pairBase π :=
  pullback.lift P.1 Q.1 (by rw [P.2, Q.2])

@[reassoc (attr := simp)]
theorem pairClassify_fst {T : Scheme.{u}} (g : T ⟶ S)
    (P Q : { w : T ⟶ C // w ≫ π = g }) :
    pairClassify π g P Q ≫ pullback.fst π π = P.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pairClassify_snd {T : Scheme.{u}} (g : T ⟶ S)
    (P Q : { w : T ⟶ C // w ≫ π = g }) :
    pairClassify π g P Q ≫ pullback.snd π π = Q.1 :=
  pullback.lift_snd _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The classifying map is compatible with the structure morphisms. -/
theorem pairClassify_π {T : Scheme.{u}} (g : T ⟶ S)
    (P Q : { w : T ⟶ C // w ≫ π = g }) :
    pairClassify π g P Q ≫ pairBaseπ π = g := by
  rw [show pairBaseπ π = pullback.fst π π ≫ π from rfl, ← Category.assoc,
    pairClassify_fst, P.2]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.1] Pullback of a tensor of two modules** for an arbitrary morphism of
schemes — the transport step of the tautological-pair argument. -/
theorem nonempty_pullback_tensorObj {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M N : X.Modules) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
        (AlgebraicGeometry.Scheme.Modules.tensorObj M N) ≅
      AlgebraicGeometry.Scheme.Modules.tensorObj
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N)) := by
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory Y
  letI : (AlgebraicGeometry.Scheme.Modules.pullback f).Monoidal :=
    (AlgebraicGeometry.Scheme.Modules.nonempty_pullback_monoidal f).some
  obtain ⟨eM⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_iso_tensor M N
  obtain ⟨eY⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_iso_tensor
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N)
  exact ⟨(AlgebraicGeometry.Scheme.Modules.pullback f).mapIso eM ≪≫
    (Functor.Monoidal.μIso (AlgebraicGeometry.Scheme.Modules.pullback f) M N).symm ≪≫
    eY.symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.1] Pullback of a trivialization.** A module trivial upstairs is trivial
after pullback — with the unit transported by `pullbackUnitIso`. -/
theorem nonempty_pullback_iso_unitObj {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M : X.Modules}
    (h : Nonempty (M ≅ AlgebraicGeometry.Scheme.Modules.unitObj X)) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M ≅
      AlgebraicGeometry.Scheme.Modules.unitObj Y) :=
  ⟨(AlgebraicGeometry.Scheme.Modules.pullback f).mapIso h.some ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.1b] Transport of a triple trivialization along a base change.** The chord
half of a `ChordDatum` pulls back: the pullback functor is monoidal, so the triple
tensor pulls back to the triple tensor of the pullbacks, and each ideal module pulls
back to the ideal module of the comap (GAP-A-7). -/
theorem nonempty_pullback_triple_iso_unitObj {X Y : Scheme.{u}} (f : Y ⟶ X)
    (J₁ J₂ J₃ : X.IdealSheafData) (L : X.Modules)
    (h₁ : ∀ c : ↥X, ∃ V : X.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(X, V.1),
      J₁.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(X, V.1))
    (h₁' : ∀ c : ↥Y, ∃ V : Y.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(Y, V.1),
      (J₁.comap f).ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(Y, V.1))
    (h₂ : ∀ c : ↥X, ∃ V : X.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(X, V.1),
      J₂.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(X, V.1))
    (h₂' : ∀ c : ↥Y, ∃ V : Y.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(Y, V.1),
      (J₂.comap f).ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(Y, V.1))
    (h₃ : ∀ c : ↥X, ∃ V : X.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(X, V.1),
      J₃.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(X, V.1))
    (h₃' : ∀ c : ↥Y, ∃ V : Y.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(Y, V.1),
      (J₃.comap f).ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(Y, V.1))
    (h : Nonempty (AlgebraicGeometry.Scheme.Modules.tensorObj
      (AlgebraicGeometry.Scheme.Modules.idealModule J₁)
      (AlgebraicGeometry.Scheme.Modules.tensorObj
        (AlgebraicGeometry.Scheme.Modules.idealModule J₂)
        (AlgebraicGeometry.Scheme.Modules.tensorObj
          (AlgebraicGeometry.Scheme.Modules.idealModule J₃) L)) ≅
      AlgebraicGeometry.Scheme.Modules.unitObj X)) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.tensorObj
      (AlgebraicGeometry.Scheme.Modules.idealModule (J₁.comap f))
      (AlgebraicGeometry.Scheme.Modules.tensorObj
        (AlgebraicGeometry.Scheme.Modules.idealModule (J₂.comap f))
        (AlgebraicGeometry.Scheme.Modules.tensorObj
          (AlgebraicGeometry.Scheme.Modules.idealModule (J₃.comap f))
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L))) ≅
      AlgebraicGeometry.Scheme.Modules.unitObj Y) := by
  classical
  obtain ⟨e₁⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_idealModule
    f J₁ h₁ h₁'
  obtain ⟨e₂⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_idealModule
    f J₂ h₂ h₂'
  obtain ⟨e₃⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_idealModule
    f J₃ h₃ h₃'
  -- pull the trivialization back and rewrite each tensor factor
  obtain ⟨hpb⟩ := nonempty_pullback_iso_unitObj f h
  obtain ⟨t₁⟩ := nonempty_pullback_tensorObj f
    (AlgebraicGeometry.Scheme.Modules.idealModule J₁)
    (AlgebraicGeometry.Scheme.Modules.tensorObj
      (AlgebraicGeometry.Scheme.Modules.idealModule J₂)
      (AlgebraicGeometry.Scheme.Modules.tensorObj
        (AlgebraicGeometry.Scheme.Modules.idealModule J₃) L))
  obtain ⟨t₂⟩ := nonempty_pullback_tensorObj f
    (AlgebraicGeometry.Scheme.Modules.idealModule J₂)
    (AlgebraicGeometry.Scheme.Modules.tensorObj
      (AlgebraicGeometry.Scheme.Modules.idealModule J₃) L)
  obtain ⟨t₃⟩ := nonempty_pullback_tensorObj f
    (AlgebraicGeometry.Scheme.Modules.idealModule J₃) L
  refine ⟨?_⟩
  refine (AlgebraicGeometry.Scheme.Modules.tensorObjCongr e₁.symm
    (AlgebraicGeometry.Scheme.Modules.tensorObjCongr e₂.symm
      (AlgebraicGeometry.Scheme.Modules.tensorObjCongr e₃.symm
        (Iso.refl _)))) ≪≫ ?_
  refine (AlgebraicGeometry.Scheme.Modules.tensorObjCongr (Iso.refl _)
    (AlgebraicGeometry.Scheme.Modules.tensorObjCongr (Iso.refl _) t₃.symm)) ≪≫ ?_
  refine (AlgebraicGeometry.Scheme.Modules.tensorObjCongr (Iso.refl _) t₂.symm) ≪≫ ?_
  exact t₁.symm ≪≫ hpb

end ModularCurves
