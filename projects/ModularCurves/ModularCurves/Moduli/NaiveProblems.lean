/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Moduli.Representability
import ModularCurves.Moduli.PullSectionCanonicity
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.ForMathlib.BaseChangeAlongCompat

/-!
# The naive level-structure moduli problems (relocated holder, Y1-CLOSER S4)

Relocated byte-identical from `Moduli/Representability.lean` (pointer there; v10.117
doctrine). `EllHom.pullSection_add` and the `gammaOneNaiveProblem.map` naive-`Γ₁(N)`
membership are now discharged — via A's `PullSectionCanonicity.lean` finite-presentation
transport and `isNaiveGammaOne_pullSection_iff`. Two `sorry`s remain, both full-level
producer WIP: the `gammaFullNaiveProblem.map` membership and `gammaFullNaive_representable`
(T-E9). Their discharge bottoms out at the single designed primitive
`isMonHom_of_one_comp_eq'_of_finitePresentation` (route (a) `RigiditySpreadingOut` /
route (c) T-W7a — in flight on other lanes).
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

-- v4.33 bump: the `≃+`-to-`AddMonoidHomClass` search for these point types exceeds the
-- default instance budget, and the nested search does not inherit a per-declaration option.
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 5

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace ModularCurves

section LevelModuli

variable (R : CommRingCat.{u})

theorem EllHom.pullSection_add {X Y : EllObj R} (f : X ⟶ Y)
    (P Q : Y.curve.Section) :
    EllHom.pullSection R f (P + Q) =
      EllHom.pullSection R f P + EllHom.pullSection R f Q :=
  EllHom.pullSection_add_of_finitePresentation R f P Q

/-- **(Y1-D2 bridge)** A pulled section vanishes on the fibre over `τ` iff its `transportSection`
(along the `Ell/R`-morphism's cartesian comparison iso `curveIsoPullback`) does — pure
iso-cancellation on the total spaces (`curveIsoPullback` is an iso, hence mono). This is the
"barehanded" fibrewise transport of the wiring note. -/
private lemma pull_transportSection_eq_zero_iff {X Y : EllObj R} (f : X ⟶ Y) {k : Type u} [Field k]
    (τ : Spec (CommRingCat.of k) ⟶ X.base) (w : X.curve.Section) :
    EllipticCurve.Point.pull X.curve τ w = 0 ↔
      EllipticCurve.Point.pull (Y.curve.baseChange f.baseHom) τ
          (EllHom.transportSection R f w) = 0 := by
  -- `iso.hom`'s codomain is inferred as `(baseChange).E` from these equations, matching
  -- `zero_curveIsoPullback` (avoiding the `pullback … = (baseChange).E` syntactic mismatch).
  have key : (EllipticCurve.Point.pull (Y.curve.baseChange f.baseHom) τ
        (EllHom.transportSection R f w)).1
      = (EllipticCurve.Point.pull X.curve τ w).1 ≫ (EllHom.curveIsoPullback R f).hom :=
    (Category.assoc _ _ _).symm
  have keyzero : (0 : (Y.curve.baseChange f.baseHom).Point τ).1
      = (0 : X.curve.Point τ).1 ≫ (EllHom.curveIsoPullback R f).hom := by
    rw [EllipticCurve.point_zero_val, EllipticCurve.point_zero_val, Category.assoc]
    exact congrArg (τ ≫ ·) (EllHom.zero_curveIsoPullback R f).symm
  rw [Subtype.ext_iff, Subtype.ext_iff, key, keyzero]
  exact (CategoryTheory.cancel_mono (EllHom.curveIsoPullback R f).hom).symm

-- v4.33 bump: the `≃+`-to-`AddMonoidHomClass` search for these point types exceeds the
-- default instance budget; the map arguments are already pinned explicitly below.
/-- **(Y1-D2, naive-structure transport along `Ell/R`-morphisms)** For an `Ell/R`-morphism
`f : X ⟶ Y` and a section `Q` of `Y.curve`, the pulled section `pullSection f Q` is naive-`Γ₁(N)`
on `X.curve` iff the pulled *point* is naive-`Γ₁(N)` on the base-changed curve
`Y.curve ×_{Y.base} X.base`. The cartesian square of `f` identifies the two curves pointedly;
the group-compatibility of that identification is the GME 2.2.5 canonicity chain — the same
**[T-E4-family]** machinery as `EllHom.pullSection_add`. Now proven and consumed by
`gammaOneNaiveProblem.map` (below), discharging its former naive-`Γ₁(N)` membership `sorry`. -/
theorem isNaiveGammaOne_pullSection_iff (N : ℕ) [NeZero N] {X Y : EllObj R} (f : X ⟶ Y)
    (Q : Y.curve.Section) :
    X.curve.IsNaiveGammaOne N (EllHom.pullSection R f Q) ↔
      (Y.curve.baseChange f.baseHom).IsNaiveGammaOne N
        (EllipticCurve.Point.asSection Y.curve f.baseHom
          (EllipticCurve.Point.pull Y.curve f.baseHom Q)) := by
  -- `transportSection` (along `f`'s cartesian comparison iso) as an additive hom — additivity is
  -- A's `T-E4-family` primitive (`transportSection_add_of_finitePresentation`), the "prove once".
  set Φ : X.curve.Section →+ (Y.curve.baseChange f.baseHom).Section :=
    AddMonoidHom.mk' (EllHom.transportSection R f)
      (EllHom.transportSection_add_of_finitePresentation R f) with hΦ
  have hinj : Function.Injective Φ := EllHom.transportSection_injective R f
  have hΦ0 : ∀ y, Φ y = 0 ↔ y = 0 := fun y ↦ by rw [← map_zero Φ]; exact hinj.eq_iff
  -- dictionary: the transport of the pulled section IS the base-changed pulled point-section.
  have hdict : Φ (EllHom.pullSection R f Q)
      = EllipticCurve.Point.asSection Y.curve f.baseHom
          (EllipticCurve.Point.pull Y.curve f.baseHom Q) := by
    refine Subtype.ext ?_
    show (EllHom.transportSection R f (EllHom.pullSection R f Q)).1 = _
    rw [EllHom.transportSection_pullSection]
    rfl
  -- section-level killing transports through the injective additive hom.
  have killing_iff : ((N : ℤ) • EllHom.pullSection R f Q = 0) ↔
      ((N : ℤ) • EllipticCurve.Point.asSection Y.curve f.baseHom
        (EllipticCurve.Point.pull Y.curve f.baseHom Q) = 0) := by
    rw [← hdict, ← map_zsmul Φ, hΦ0]
  -- fibrewise, any integer scalar: pull ∘ (a • ·) then iso-cancel
  -- (`pull_transportSection_eq_zero_iff`).
  have hbridge : ∀ (a : ℤ) {k : Type u} [Field k] (t : Spec (CommRingCat.of k) ⟶ X.base),
      (a • EllipticCurve.Point.pull X.curve t (EllHom.pullSection R f Q) = 0 ↔
        a • EllipticCurve.Point.pull (Y.curve.baseChange f.baseHom) t
          (EllipticCurve.Point.asSection Y.curve f.baseHom
            (EllipticCurve.Point.pull Y.curve f.baseHom Q)) = 0) := by
    intro a k _ t
    rw [← EllipticCurve.Point.pull_zsmul, ← EllipticCurve.Point.pull_zsmul,
      pull_transportSection_eq_zero_iff (R := R) (f := f) (τ := t)
        (w := a • EllHom.pullSection R f Q),
      show EllHom.transportSection R f (a • EllHom.pullSection R f Q)
        = a • Φ (EllHom.pullSection R f Q) from map_zsmul Φ a _, hdict]
  constructor
  · rintro ⟨hkill, hfib⟩
    refine ⟨killing_iff.mp hkill, ?_⟩
    intro k _ _ t
    exact ⟨(hbridge (N : ℤ) t).mp (hfib k t).1,
      fun a ha haN ↦ (not_congr (hbridge (a : ℤ) t)).mp ((hfib k t).2 a ha haN)⟩
  · rintro ⟨hkill, hfib⟩
    refine ⟨killing_iff.mpr hkill, ?_⟩
    intro k _ _ t
    exact ⟨(hbridge (N : ℤ) t).mpr (hfib k t).1,
      fun a ha haN ↦ (not_congr (hbridge (a : ℤ) t)).mpr ((hfib k t).2 a ha haN)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The base-changed pull of `asSection` is the pull along the composite: the
`baseChangeEquiv`-dictionary at geometric points. -/
private lemma baseChangeEquiv_pull_asSection {X Y : EllObj R} (f : X ⟶ Y)
    {T : Scheme.{u}} (t : T ⟶ X.base) (Q : Y.curve.Section) :
    EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom t
        (EllipticCurve.Point.pull (Y.curve.baseChange f.baseHom) t
          (EllipticCurve.Point.asSection Y.curve f.baseHom
            (EllipticCurve.Point.pull Y.curve f.baseHom Q))) =
      EllipticCurve.Point.pull Y.curve (t ≫ f.baseHom) Q := by
  refine Subtype.ext ?_
  rw [EllipticCurve.Point.baseChangeEquiv_apply_coe]
  show (t ≫ (EllipticCurve.Point.asSection Y.curve f.baseHom
    (EllipticCurve.Point.pull Y.curve f.baseHom Q)).1) ≫ _ = _
  rw [Category.assoc, EllipticCurve.Point.asSection_val_fst]
  rfl

/-- Naive `Γ₁(N)` structures transport to the base change along an `Ell/R` morphism's base:
the target-side input of `isNaiveGammaOne_pullSection_iff`. -/
private lemma isNaiveGammaOne_asSection_pull (N : ℕ) [NeZero N] {X Y : EllObj R} (f : X ⟶ Y)
    {Q : Y.curve.Section} (hQ : Y.curve.IsNaiveGammaOne N Q) :
    (Y.curve.baseChange f.baseHom).IsNaiveGammaOne N
      (EllipticCurve.Point.asSection Y.curve f.baseHom
        (EllipticCurve.Point.pull Y.curve f.baseHom Q)) := by
  obtain ⟨hkill, hfib⟩ := hQ
  constructor
  · -- global killing transports through `pull` and `asSection` (both additive)
    rw [← EllipticCurve.Point.asSection_zsmul, ← EllipticCurve.Point.pull_zsmul, hkill,
      EllipticCurve.Point.pull_zero]
    refine Subtype.ext (Limits.pullback.hom_ext ?_ ?_)
    · have hL : ((EllipticCurve.Point.asSection Y.curve f.baseHom
          (0 : Y.curve.Point f.baseHom)).1) ≫ Limits.pullback.fst Y.curve.π f.baseHom =
          f.baseHom ≫ Y.curve.zero :=
        (EllipticCurve.Point.asSection_val_fst _ _ _).trans
          (congrArg Subtype.val (rfl : (0 : Y.curve.Point f.baseHom) = 0)).symm ▸
          (EllipticCurve.Point.asSection_val_fst _ _ _).trans
            (Y.curve.point_zero_val f.baseHom)
      have hR : (((0 : (Y.curve.baseChange f.baseHom).Point (𝟙 X.base))).1) ≫
          Limits.pullback.fst Y.curve.π f.baseHom = f.baseHom ≫ Y.curve.zero := by
        have h0 := (Y.curve.baseChange f.baseHom).point_zero_val (𝟙 X.base)
        rw [h0, Category.id_comp]
        exact Limits.pullback.lift_fst _ _ _
      exact hL.trans hR.symm
    · have hL : ((EllipticCurve.Point.asSection Y.curve f.baseHom
          (0 : Y.curve.Point f.baseHom)).1) ≫ Limits.pullback.snd Y.curve.π f.baseHom =
          𝟙 X.base :=
        EllipticCurve.Point.asSection_val_snd _ _ _
      have hR : (((0 : (Y.curve.baseChange f.baseHom).Point (𝟙 X.base))).1) ≫
          Limits.pullback.snd Y.curve.π f.baseHom = 𝟙 X.base := by
        have h0 := (Y.curve.baseChange f.baseHom).point_zero_val (𝟙 X.base)
        rw [h0, Category.id_comp]
        exact Limits.pullback.lift_snd _ _ _
      exact hL.trans hR.symm
  · intro k _ _ t
    have hbc : ∀ (a : ℤ),
        a • EllipticCurve.Point.pull (Y.curve.baseChange f.baseHom) t
          (EllipticCurve.Point.asSection Y.curve f.baseHom
            (EllipticCurve.Point.pull Y.curve f.baseHom Q)) = 0 ↔
        a • EllipticCurve.Point.pull Y.curve (t ≫ f.baseHom) Q = 0 := by
      intro a
      constructor
      · intro h0
        have h1 := congrArg (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom t) h0
        rw [map_zsmul (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom t),
          baseChangeEquiv_pull_asSection,
          map_zero (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom t)] at h1
        exact h1
      · intro h0
        refine (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom t).injective ?_
        rw [map_zsmul (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom t),
          baseChangeEquiv_pull_asSection,
          map_zero (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom t), h0]
    obtain ⟨hk, hord⟩ := hfib k (t ≫ f.baseHom)
    exact ⟨(hbc (N : ℤ)).mpr hk, fun a ha haN h0 ↦ hord a ha haN ((hbc (a : ℤ)).mp h0)⟩

/-- The naive `Γ₁(N)` moduli problem over `R`: `E/S ↦ {P ∈ E(S) : P` has naive exact
order `N}` (fibrewise; the right notion for `N` invertible, KM 1.4.4). Functor laws are
`T-E4`. Source: Loeffler §3.3/§3.8; KM 3.2 + 3.7. -/
noncomputable def gammaOneNaiveProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { P : X.unop.curve.Section // X.unop.curve.IsNaiveGammaOne N P }
  map f := ↾fun P ↦ ⟨EllHom.pullSection R f.unop P.1,
    (isNaiveGammaOne_pullSection_iff R N f.unop P.1).mpr
      (isNaiveGammaOne_asSection_pull R N f.unop P.2)⟩
  map_id X := by
    ext P
    exact congrArg Subtype.val (EllHom.pullSection_id R P.1)
  map_comp f g := by
    ext P
    exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop P.1)

/-- The naive full-level-`N` (`Γ(N)`) moduli problem over `R`:
`E/S ↦ {(P, Q) generating E[N] in every fibre}`. Source: Loeffler Fact 3.8.1 (verbatim:
"pairs of sections `P, Q ∈ E[S]` generating `E[N]` in every fibre"); KM 3.1 + 3.7. -/
noncomputable def gammaFullNaiveProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { PQ : X.unop.curve.Section × X.unop.curve.Section //
    X.unop.curve.IsNaiveFullLevel N PQ.1 PQ.2 }
  map f := ↾fun PQ => ⟨⟨EllHom.pullSection R f.unop PQ.1.1,
    EllHom.pullSection R f.unop PQ.1.2⟩, by sorry⟩
  map_id X := by
    ext PQ
    · exact congrArg Subtype.val (EllHom.pullSection_id R PQ.1.1)
    · exact congrArg Subtype.val (EllHom.pullSection_id R PQ.1.2)
  map_comp f g := by
    ext PQ
    · exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop PQ.1.1)
    · exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop PQ.1.2)

/- **RELOCATED (Y1-CLOSER S6, v10.111/117 doctrine)**: the held T-E7 MASTER
`gammaOneNaive_representable` now lives BYTE-IDENTICAL in `ModularCurve/YOneTatePoint.lean`,
closed by `gammaOneNaive_representable_assembly` (zero code-consumers of the name at
relocation time — the cap theorem). -/

/-- **(T-E9 = Loeffler Prop 3.8.2–3.8.3; KM 3.1/4.7/5.1)** For `N ≥ 3` and `N` invertible
in `R`, the naive full-level problem `[Γ(N)]` is rigid and representable; the representing
scheme `Y(N)` is smooth and affine over `Spec R`.
(Rigidity: Loeffler Prop 3.8.3 covers `Ell/R[1/6]` only; for residue characteristics
2 and 3 the source of record is the GME 2.6.4 Aut-computation ("`ε ∈ Aut(E,φ)`,
`n ≥ 3` invertible ⟹ `ε = 1`", chain B9 in decomposition-gme2 — valid in all
characteristics with `N` invertible); KM locator pending. Smooth+affine conjunct
restored 2026-07-06 — it was in this docstring but missing from the statement.) -/
theorem gammaFullNaive_representable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    ((gammaFullNaiveProblem R N).Rigid ∧ (gammaFullNaiveProblem R N).Representable) ∧
      ∀ X : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by
  sorry

end LevelModuli

end ModularCurves