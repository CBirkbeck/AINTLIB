/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.DualPullback
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
  -- (m i): the generating section over V i — `tensorSection sA sB` per the board plan.
  · have sA : ↑Γ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N), V i) := by
      -- rfl-equal to Γ(f^*N, f⁻¹(V i)): the unit-hom from `htriv i` through the pullback
      -- dictionaries, read as a section at the top of the over-site.
      have ψ : _root_.SheafOfModules.unit
            ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ V i)) ⟶
          ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N).over
            (pullback.snd p g ⁻¹ᵁ V i) :=
        (AlgebraicGeometry.Scheme.Modules.overEquiv
            (pullback.snd p g ⁻¹ᵁ V i)).functor.preimage
          (((pullback.snd p g ⁻¹ᵁ V i).sheafOfModulesEquivOverUnit
              (pullback p g).ringCatSheaf).hom ≫
            (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
              (pullback.snd p g ∣_ V i)).inv ≫
            (AlgebraicGeometry.Scheme.Modules.pullback
              (pullback.snd p g ∣_ V i)).map ((htriv i).some.inv) ≫
            (AlgebraicGeometry.Scheme.Modules.pullback
              (pullback.snd p g ∣_ V i)).map
              (((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv (V i)).app N ≪≫
                (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback
                  (V i).ι).app N).inv) ≫
            (AlgebraicGeometry.Scheme.Modules.localPullbackModuleIso
              (pullback.snd p g) N (V i)).hom)
      exact ((((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N).over
        (pullback.snd p g ⁻¹ᵁ V i)).unitHomEquiv ψ).val
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ V i))))
    have sB : ↑Γ(AlgebraicGeometry.Scheme.Modules.dualObj N, V i) := by
      -- `Γ(dualObj N, V i)` is definitionally the Hom-type `N.over (V i) ⟶ unit`; the functional is
      -- `htriv i` read through the over/pullback dictionaries.
      exact (fun (φ : N.over (V i) ⟶ _root_.SheafOfModules.unit (T.ringCatSheaf.over (V i))) => φ)
        ((AlgebraicGeometry.Scheme.Modules.overEquiv (V i)).functor.preimage
          (((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv (V i)).app N).hom ≫
            ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (V i).ι).app N).hom ≫
            (htriv i).some.hom ≫
            ((V i).sheafOfModulesEquivOverUnit T.ringCatSheaf).inv))
    exact tensorSection _ _ (V i) sA sB
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
