/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.DualPullback
import ModularCurves.Picard.InvertibleSheafCocycle
import ModularCurves.WeilPairing.TensorSection
import ModularCurves.WeilPairing.UnitSheaf
import ModularCurves.Picard.InvertibleSheafBaseCechFlat

/-!
# Zariski locality of the relative Picard equivalence (`AP2-B1`, KM p. 65)

Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, p. 65, verbatim: *"if we are given `ℒ` and `ℒ'`
on `E`, an affine open covering `{U_i}` of `S`, invertible sheaves `ℒ_{0,i}` on `U_i`, and
isomorphisms `φ_i : ℒ ≅ ℒ' ⊗ f^*(ℒ_{0,i})` on `f⁻¹(U_i)`, then there exists an `ℒ₀` on `S` and an
isomorphism `φ : ℒ ≅ ℒ' ⊗ f^*(ℒ₀)`."* — the sheaf condition for `Pic_{E_T/T} = Pic(E_T)/f_T^*Pic(T)`,
in its consumable form. KM's proof (p. 65): *"Because `E/S` is proper and smooth with geometrically
connected fibers, we have `f_*(𝒪_E) = 𝒪_S`, whence `f_*f^*(ℒ_{0,i}) = ℒ_{0,i}` on `U_i`. Therefore
the existence of the isomorphism `φ_i` shows that both `f_*(ℒ⁻¹ ⊗ ℒ')`, `f_*(ℒ ⊗ (ℒ')⁻¹)` are
invertible sheaves on `𝒪_S`, inverse to each other. If we call the second one `ℒ₀`, and write
`ℒ'' = ℒ' ⊗ f^*(ℒ₀)`, we find canonical isomorphisms `f_*(ℒ⁻¹ ⊗ ℒ'') = 𝒪_S = f_*(ℒ ⊗ (ℒ'')⁻¹)`,
under which the unit section `1 ∈ Γ(S, 𝒪_S)` is the required isomorphism `ℒ ≅ ℒ''`."*

Hida's corresponding locality claim (p. 109, *"Since the formation of invertible sheaf is local,
`Pic_{E/S}` is local"*) is a non-sequitur — isomorphism *classes* are not a Zariski sheaf — and the
`f_*𝒪 = 𝒪` input above is exactly what repairs it (`decomposition-gme2.md`, CORRECTIONS item 3).
Round-19 architecture step `[B′]`; consumed by `AP2-B4`'s naturality and by `AP-D5`'s cocycle
refinement independence.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

/-- **(AP2-B1, KM p. 65)** The `f^*`-twist equivalence on invertible sheaves is Zariski-local on the
base: isomorphisms `M ≅ M' ⊗ f^*(N i)` over the preimages of an open cover of `T` glue to a global
`M ≅ M' ⊗ f^*N₀` — the sheaf condition for `Pic(E_T)/f_T^*Pic(T)`.

Skeleton (`:= by sorry`); proof recipe is KM p. 65's, quoted in the module docstring, with the glue
supplied by `UniversallyOConnected` and the tree's pushforward machinery. -/
theorem exists_pullback_twist_of_locally {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}}
    (g : T ⟶ S) (hp : UniversallyOConnected p)
    {M M' : (pullback p g).Modules} (hM : IsInvertible M) (hM' : IsInvertible M')
    {ι : Type u} (U : ι → T.Opens) (hU : IsOpenCover U)
    (N : ∀ i, (U i).toScheme.Modules) (hN : ∀ i, IsInvertible (N i))
    (hglue : ∀ i, Nonempty
      (M.restrict (pullback.snd p g ⁻¹ᵁ U i).ι ≅
        tensorObj (M'.restrict (pullback.snd p g ⁻¹ᵁ U i).ι)
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (pullback.snd p g ∣_ U i)).obj (N i)))) :
    ∃ N₀ : T.Modules, IsInvertible N₀ ∧
      Nonempty (M ≅ tensorObj M'
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N₀)) := by
  sorry


/-- The pushforward-slot generating section of the glue: over a trivialising open `V` of `N`, the
canonical section of `f_*f^*N` obtained from a trivialisation `e` through the pullback dictionaries
(`sheafOfModulesEquivOverUnit`, `pullbackUnitIso`, `localPullbackModuleIso`), read via `unitHomEquiv`
at the top of the over-site. -/
noncomputable def glueSectionA {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)
    (N : T.Modules) (V : T.Opens)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ unitObj V.toScheme) :
    ↑Γ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N), V) :=
  ((((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N).over
      (pullback.snd p g ⁻¹ᵁ V)).unitHomEquiv
    ((AlgebraicGeometry.Scheme.Modules.overEquiv
        (pullback.snd p g ⁻¹ᵁ V)).functor.preimage
      (((pullback.snd p g ⁻¹ᵁ V).sheafOfModulesEquivOverUnit
          (pullback p g).ringCatSheaf).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (pullback.snd p g ∣_ V)).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.snd p g ∣_ V)).map e.inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.snd p g ∣_ V)).map
          (((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv V).app N ≪≫
            (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).inv) ≫
        (AlgebraicGeometry.Scheme.Modules.localPullbackModuleIso
          (pullback.snd p g) N V).hom))).val
    (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ V))))

/-- The over-site form of a pullback trivialisation: `N.over V ≅ unit`, through the
`overEquiv`/`restrictFunctorIsoPullback`/`sheafOfModulesEquivOverUnit` dictionaries. This is the form
`trivializationTransitionUnit` (`Picard/InvertibleSheafCocycle.lean:44`) consumes. -/
noncomputable def overTrivialization {T : Scheme.{u}} (N : T.Modules) (V : T.Opens)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ unitObj V.toScheme) :
    N.over V ≅ _root_.SheafOfModules.unit (T.ringCatSheaf.over V) :=
  (AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.preimageIso
    ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv V).app N ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback V.ι).app N ≪≫
      e ≪≫ (V.sheafOfModulesEquivOverUnit T.ringCatSheaf).symm)

/-- The transition unit of two pullback trivialisations on the overlap: restrict both with
`restrictTrivialization` (`Picard/InvertibleSheaf.lean:229`), pass to over-form, and take
`trivializationTransitionUnit`. -/
noncomputable def glueTransitionUnit {T : Scheme.{u}} (N : T.Modules) {Vi Vj : T.Opens}
    (ei : (AlgebraicGeometry.Scheme.Modules.pullback Vi.ι).obj N ≅ unitObj Vi.toScheme)
    (ej : (AlgebraicGeometry.Scheme.Modules.pullback Vj.ι).obj N ≅ unitObj Vj.toScheme) :
    ↑Γ(T, Vi ⊓ Vj)ˣ :=
  AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit (Vi ⊓ Vj)
    (overTrivialization N (Vi ⊓ Vj)
      (AlgebraicGeometry.Scheme.Modules.restrictTrivialization inf_le_right ej))
    (overTrivialization N (Vi ⊓ Vj)
      (AlgebraicGeometry.Scheme.Modules.restrictTrivialization inf_le_left ei))

/-- The dual-slot generating section of the glue: the functional on `N` over `V` induced by a
trivialisation `e`, as a section of `dualObj N` (whose sections over `V` are definitionally the
Hom-type `N.over V ⟶ unit`). -/
noncomputable def glueSectionB {T : Scheme.{u}} (N : T.Modules) (V : T.Opens)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ unitObj V.toScheme) :
    ↑Γ(AlgebraicGeometry.Scheme.Modules.dualObj N, V) :=
  (fun (φ : N.over V ⟶ _root_.SheafOfModules.unit (T.ringCatSheaf.over V)) => φ)
    (overTrivialization N V e).hom


/-- **(AP2-B1a, comparison A — the pushforward slot picks up the transition unit.)** On the overlap the
two `glueSectionA`s differ by `glueTransitionUnit`. Cocycle content of KM p. 65's glue. -/
theorem glueSectionA_compat {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)
    (N : T.Modules) {Vi Vj : T.Opens}
    (ei : (AlgebraicGeometry.Scheme.Modules.pullback Vi.ι).obj N ≅ unitObj Vi.toScheme)
    (ej : (AlgebraicGeometry.Scheme.Modules.pullback Vj.ι).obj N ≅ unitObj Vj.toScheme) :
    ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N)).presheaf.map
        (Opens.infLELeft Vi Vj).op (glueSectionA g N Vi ei) =
      (glueTransitionUnit N ei ej : ↑Γ(T, Vi ⊓ Vj)) •
        ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N)).presheaf.map
          (Opens.infLERight Vi Vj).op (glueSectionA g N Vj ej) := by
  sorry

/-- **(AP2-B1a, comparison B — the dual slot picks up the INVERSE transition unit.)** -/
theorem glueSectionB_compat {T : Scheme.{u}} (N : T.Modules) {Vi Vj : T.Opens}
    (ei : (AlgebraicGeometry.Scheme.Modules.pullback Vi.ι).obj N ≅ unitObj Vi.toScheme)
    (ej : (AlgebraicGeometry.Scheme.Modules.pullback Vj.ι).obj N ≅ unitObj Vj.toScheme) :
    (AlgebraicGeometry.Scheme.Modules.dualObj N).presheaf.map
        (Opens.infLELeft Vi Vj).op (glueSectionB N Vi ei) =
      (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) •
        (AlgebraicGeometry.Scheme.Modules.dualObj N).presheaf.map
          (Opens.infLERight Vi Vj).op (glueSectionB N Vj ej) := by
  sorry

/-- **(AP2-B1a′, ⊗-self — discharged)** Invertibility pairing `N ⊗ N^∨ ≅ 𝒪`: exactly the tree's
`nonempty_eval_iso` (`Picard/PicComparison.lean`), proved. Kept as a named wrapper for the assembly. -/
theorem nonempty_tensorObj_dualObj_unitObj {T : Scheme.{u}} {N : T.Modules}
    (hN : IsInvertible N) :
    Nonempty (tensorObj N (dualObj N) ≅ unitObj T) :=
  nonempty_eval_iso hN

/-- **(AP2-B1a′, obligation glue)** The pushforward of the pullback, twisted by the dual, is trivial:
per trivialising open the generating section is (pushforward-`rfl` of `f^*e_i` via `pullbackUnitIso`)
`⊗ e_i^∨`; overlap agreement holds **on the nose** by cocycle cancellation (`f^*N` inherits `N`'s own
transition units, and the tensor with `N^∨` cancels them); bijectivity componentwise from
`hp g W` and `e_i`. Engine: `nonempty_unitObj_iso_of_glue` (`GlueTrivialization.lean:98`). -/
theorem nonempty_tensorObj_pushforwardPullback_dualObj_unitObj {X S : Scheme.{u}} {p : X ⟶ S}
    {T : Scheme.{u}} (g : T ⟶ S) (hp : UniversallyOConnected p)
    {N : T.Modules} (hN : IsInvertible N) :
    Nonempty (tensorObj
      ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N))
      (dualObj N) ≅ unitObj T) := by
  obtain ⟨κ, V, hV, htriv⟩ := hN
  refine Nonempty.map Iso.symm (nonempty_unitObj_iso_of_glue _ V hV (fun i => ?_) ?_ ?_)
  -- (m i): the generating section over V i.
  · exact tensorSection _ _ (V i)
      (glueSectionA g N (V i) (htriv i).some) (glueSectionB N (V i) (htriv i).some)
  -- (hcompat): cocycle cancellation ON THE NOSE — `f^*N` inherits `N`'s transition units,
  -- and the dual factor cancels them; both sides are the same section of the tensor.
  · sorry
  -- (hbij): componentwise — `hp g W` on the pushforward factor, `e_i` on both.
  · sorry

/-- **(AP2-B1a, KM p. 65: "`f_*f^*(ℒ_{0,i}) = ℒ_{0,i}`")** Over a universally `O`-connected family,
`f_*f^*N ≅ N` for invertible `N` — assembled by cancelling the dual twist
(`nonempty_iso_of_tensorObj_unitObj`, `PicComparison.lean:909`) between the two obligations above.
Replaces the earlier opaque-adjunction-unit form (see the AP2-B1a REPLAN note on the board): KM's
proof consumes only this identification, not the unit. -/
theorem nonempty_pushforwardPullback_iso {X S : Scheme.{u}} {p : X ⟶ S}
    {T : Scheme.{u}} (g : T ⟶ S) (hp : UniversallyOConnected p)
    {N : T.Modules} (hN : IsInvertible N) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N) ≅ N) :=
  nonempty_iso_of_tensorObj_unitObj
    (nonempty_tensorObj_pushforwardPullback_dualObj_unitObj g hp hN)
    (nonempty_tensorObj_dualObj_unitObj hN)

end ModularCurves
