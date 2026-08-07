/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
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

/-- **(AP2-B1a, KM p. 65: "`f_*f^*(ℒ_{0,i}) = ℒ_{0,i}`")** Over a universally `O`-connected family,
the pullback–pushforward adjunction unit is an isomorphism on invertible modules: `N ≅ f_*f^*N`
canonically. Mathlib supplies the adjunction (`Modules.pullbackPushforwardAdjunction`,
`AlgebraicGeometry/Modules/Sheaf.lean:189`); `hp` is what makes its unit invertible — locally `N ≅ 𝒪`
and on the structure sheaf the unit is exactly `hp g U : IsIso ((pullback.snd p g).app U)`. -/
theorem isIso_pullbackPushforwardAdjunction_unit_app {X S : Scheme.{u}} {p : X ⟶ S}
    {T : Scheme.{u}} (g : T ⟶ S) (hp : UniversallyOConnected p)
    {N : T.Modules} (hN : IsInvertible N) :
    IsIso ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.snd p g)).unit.app N) := by
  sorry

end ModularCurves
