import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Limits

/-!
# Pullback--pushforward base change for scheme modules

This file constructs the canonical base-change morphism for a scheme module on a
cartesian square. It is the mate, under the pullback--pushforward adjunction, of
pullback pseudofunctoriality followed by the adjunction counit.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S)

private noncomputable def pullbackPushforwardBaseChangeAdj :
    pushforward f ⋙ pullback t ⋙ pullback (Limits.pullback.snd f t) ⟶
      pullback (Limits.pullback.fst f t) :=
  Functor.whiskerLeft (pushforward f)
      (pullbackComp (Limits.pullback.snd f t) t).hom ≫
    Functor.whiskerLeft (pushforward f)
      (pullbackCongr (Limits.pullback.condition.symm :
        Limits.pullback.snd f t ≫ t = Limits.pullback.fst f t ≫ f)).hom ≫
    Functor.whiskerLeft (pushforward f)
      (pullbackComp (Limits.pullback.fst f t) f).inv ≫
    Functor.whiskerRight (pullbackPushforwardAdjunction f).counit
      (pullback (Limits.pullback.fst f t))

private noncomputable def pullbackPushforwardBaseChangeAdjApp (M : X.Modules) :
    (pullback (Limits.pullback.snd f t)).obj
        ((pushforward f ⋙ pullback t).obj M) ⟶
      (pullback (Limits.pullback.fst f t)).obj M := by
  change (pushforward f ⋙ pullback t ⋙
    pullback (Limits.pullback.snd f t)).obj M ⟶ _
  exact (pullbackPushforwardBaseChangeAdj f t).app M

private lemma pullbackPushforwardBaseChangeAdjApp_naturality
    {M N : X.Modules} (φ : M ⟶ N) :
    (pullback (Limits.pullback.snd f t)).map
          ((pushforward f ⋙ pullback t).map φ) ≫
        pullbackPushforwardBaseChangeAdjApp f t N =
      pullbackPushforwardBaseChangeAdjApp f t M ≫
        (pullback (Limits.pullback.fst f t)).map φ := by
  change (pushforward f ⋙ pullback t ⋙
      pullback (Limits.pullback.snd f t)).map φ ≫
      (pullbackPushforwardBaseChangeAdj f t).app N =
    (pullbackPushforwardBaseChangeAdj f t).app M ≫
      (pullback (Limits.pullback.fst f t)).map φ
  exact (pullbackPushforwardBaseChangeAdj f t).naturality φ

private noncomputable abbrev pullbackPushforwardBaseChangeTarget :
    X.Modules ⥤ T.Modules where
  obj M := (pushforward (Limits.pullback.snd f t)).obj
    ((pullback (Limits.pullback.fst f t)).obj M)
  map φ := (pushforward (Limits.pullback.snd f t)).map
    ((pullback (Limits.pullback.fst f t)).map φ)
  map_id M := by simp
  map_comp φ ψ := by simp

private noncomputable def pullbackPushforwardBaseChangeCore :
    pushforward f ⋙ pullback t ⟶ pullbackPushforwardBaseChangeTarget f t where
  app M := (pullbackPushforwardAdjunction (Limits.pullback.snd f t)).homEquiv _ _
    (pullbackPushforwardBaseChangeAdjApp f t M)
  naturality {M N} φ := by
    rw [← Adjunction.homEquiv_naturality_left,
      ← Adjunction.homEquiv_naturality_right]
    exact congrArg
      ((pullbackPushforwardAdjunction (Limits.pullback.snd f t)).homEquiv
        ((pushforward f ⋙ pullback t).obj M)
        ((pullback (Limits.pullback.fst f t)).obj N))
      (pullbackPushforwardBaseChangeAdjApp_naturality f t φ)

private noncomputable def pullbackPushforwardBaseChangeTargetIso :
    pullbackPushforwardBaseChangeTarget f t ≅
      pullback (Limits.pullback.fst f t) ⋙
        pushforward (Limits.pullback.snd f t) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The canonical base-change morphism
`t^*(f_*M) ⟶ f'_*(g^*M)` for the pullback square of `f` along `t`. -/
noncomputable def pullbackPushforwardBaseChange :
    pushforward f ⋙ pullback t ⟶
      pullback (Limits.pullback.fst f t) ⋙
        pushforward (Limits.pullback.snd f t) :=
  pullbackPushforwardBaseChangeCore f t ≫
    (pullbackPushforwardBaseChangeTargetIso f t).hom

end AlgebraicGeometry.Scheme.Modules
