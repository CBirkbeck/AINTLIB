/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.InvertibleSheafProperCechResidueSpread
import ModularCurves.Picard.RigidDescent

/-!
# The seesaw theorem over a reduced base (`KM-SEESAW`, Stacks 0EX7 at rank 1)

An invertible sheaf on a proper flat family of finite presentation over a **reduced** base, trivial on
every fibre, is pulled back from the base.

## Source

Stacks Project, **Lemma 37.33.2, tag `0EX7`** — Chapter 37 *More on Morphisms*, §37.33 *Theorem of the
cube*:

> "Let `f : X → S` be a flat, proper morphism of finite presentation such that `f_*𝒪_X = 𝒪_S` and this
> remains true after arbitrary base change. Let `ℰ` be a finite locally free `𝒪_X`-module. Assume
> (1) `ℰ|_{X_s}` is isomorphic to `𝒪_{X_s}^{⊕ r_s}` for all `s ∈ S`, and (2) `S` is reduced. Then
> `ℰ = f^*𝒩` for some finite locally free `𝒪_S`-module `𝒩`."

`UniversallyOConnected f` (`EllipticCurve/Rigidity.lean`) unfolds to
`∀ ⦃T⦄ (g : T ⟶ S) (U : T.Opens), IsIso ((pullback.snd f g).app U)` — this **is** the source's
"`f_*𝒪_X = 𝒪_S`, and this remains true after arbitrary base change". The alignment is exact; it is also
the standing hypothesis of Stacks Lemma 37.33.1 (`0BDP`), the section's foundation.

## Generality: rank 1

Stated for `IsInvertible` (`r_s ≡ 1`), not general finite locally free. The extra work in the general
case is entirely the *non-constant* `r_s` bookkeeping, orthogonal to the argument, and every consumer in
this tree is rank 1. Generalising afterwards is a `/generalise` ticket.

## Why not the source's own proof

`0EX7` and `0BF4` both route through `0BDP`, whose proof needs *Derived Categories of Schemes* 36.31.4
(immersions representing perfect objects) and 36.30.4 (cohomology and base change). **mathlib has no
cohomology and base change** (searched 2026-08-05: `leansearch`, `local_search "cohomologyBaseChange"`,
`loogle` on `IsProper ?f → (Modules.pushforward ?f).obj ?M` — all empty).

`Picard/` supplies a derived-category-free **Čech surrogate** instead, and that is what this file
assembles:

* `IsInvertible.exists_finiteAffineBaseCech_flat` — a finite affine trivialising cover whose base-linear
  Čech complex is termwise flat;
* `IsInvertible.exists_away_orderedBaseCech_exact_of_residueField_exact` — exactness on **one residue
  fibre spreads to a principal neighbourhood** (this is the seesaw's engine);
* `nonempty_unitObj_iso_of_normalized_glue` — local-to-global, with the overlap condition *forced* by
  zero-normalisation.

## Where reducedness is used

Only in `exists_pullback_iso_of_residueField_exact` (`KM-SEESAW-2`), at the passage from "exact at every
residue fibre" to "exact over `R`". Over a non-reduced base the statement is **false**: on
`T = Spec k[ε]/(ε²)` with `X = E₀ × T`, a nonzero class of `H¹(E₀, 𝒪)` gives transition functions
`1 + ε a_{ij}` — trivial on the only fibre, rigidified along zero, still nontrivial. See the discussion
at `Picard/SelfAdjointN.lean`'s module docstring.

## Consumer

The relative theorem of the square, `exists_invertible_tensor_idealModule_add`
(`Picard/SelfAdjointN.lean:267`), which is the single classical leaf under `(★)`/`(★′)` and hence under
the Katz–Mazur construction of the relative Weil pairing (DS4).
-/

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace ModularCurves

/-- **(KM-SEESAW-1)** Fibrewise triviality supplies the residue-fibre exactness hypothesis of
`IsInvertible.exists_away_orderedBaseCech_exact_of_residueField_exact`.

On the fibre `X_p` the sheaf `M` is trivial, so the base-Čech complex base-changed to `p.ResidueField`
is the Čech complex of the structure sheaf of `X_p`; its exactness in positive degrees is the vanishing
of `H^q(X_p, 𝒪)` for `q > 0`, and in degree `0` it is `Γ(X_p, 𝒪) = κ(p)`, i.e. `UniversallyOConnected`
read on the fibre. -/
theorem orderedBaseCech_residueField_exact_of_fibre_trivial
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (p : Ideal Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))) [p.IsPrime]
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ Spec (.of R)),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (Limits.pullback.fst π x)).obj M ≅ unitObj (Limits.pullback π x))) :
    ∀ q, q < Fintype.card ι →
      let C := orderedBaseCechComplex π M U
      Function.Exact
        ((C.d q (q + 1)).hom.baseChange p.ResidueField)
        ((C.d (q + 1) (q + 2)).hom.baseChange p.ResidueField) := by
  sorry

/-- **(KM-SEESAW-2)** Residue-fibre exactness at every prime, over a **reduced** base, descends to a
global pullback: `M ≅ π^* N` for an invertible `N` on the base.

Spread each prime's exactness to a principal neighbourhood with
`exists_away_orderedBaseCech_exact_of_residueField_exact`, cover `Spec R` by finitely many of those
(quasi-compactness), read `Γ(M)` off the exact base-Čech complex as a rank-1 projective module over each
`R[1/r]` to get the local `N`, and glue with `nonempty_unitObj_iso_of_normalized_glue`. -/
theorem exists_pullback_iso_of_residueField_exact
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced (Spec (.of R))]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hres : ∀ (p : Ideal Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))) [p.IsPrime],
      ∀ q, q < Fintype.card ι →
        let C := orderedBaseCechComplex π M U
        Function.Exact
          ((C.d q (q + 1)).hom.baseChange p.ResidueField)
          ((C.d (q + 1) (q + 2)).hom.baseChange p.ResidueField)) :
    ∃ N : (Spec (.of R)).Modules, IsInvertible N ∧
      Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback π).obj N) := by
  sorry

/-- **(KM-SEESAW, Stacks 0EX7 at rank 1)** The seesaw theorem: an invertible sheaf on a proper flat
family of finite presentation over a **reduced** affine base, trivial on every fibre, is pulled back
from the base.

The composition of `orderedBaseCech_residueField_exact_of_fibre_trivial` (KM-SEESAW-1) with
`exists_pullback_iso_of_residueField_exact` (KM-SEESAW-2), over the finite affine trivialising cover
produced by `IsInvertible.exists_finiteAffineBaseCech_flat`. -/
theorem exists_pullback_iso_of_fibrewise_trivial_of_isReduced
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced (Spec (.of R))]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ Spec (.of R)),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (Limits.pullback.fst π x)).obj M ≅ unitObj (Limits.pullback π x))) :
    ∃ N : (Spec (.of R)).Modules, IsInvertible N ∧
      Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback π).obj N) := by
  obtain ⟨ι, hι, U, hU, hUaff, htriv, hflat⟩ := hM.exists_finiteAffineBaseCech_flat π
  letI : Fintype ι := Fintype.ofFinite ι
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  exact exists_pullback_iso_of_residueField_exact hπ hM U hU hUaff
    fun p _ => orderedBaseCech_residueField_exact_of_fibre_trivial hπ hM U hU hUaff p hfib

end ModularCurves
