/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.BaseChangeKerCoker
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
* `baseSectionsIsoKernelOrderedBaseCechDifferential` — `H⁰` of that complex **is** `Γ(M)` over the base
  ring, so the seesaw's `π_* M` is a *kernel*, computable degreewise;
* `LinearMap.finrank_ker_baseChange_eq` (`ForMathlib/BaseChangeKerCoker.lean:586`) — a field extension
  does not change that kernel's dimension, which reduces "every field-valued point" to "every residue
  field";
* `nonempty_unitObj_iso_of_normalized_glue` — local-to-global, with the overlap condition *forced* by
  zero-normalisation.

Note that `IsInvertible.exists_away_orderedBaseCech_exact_of_residueField_exact`
(`Picard/InvertibleSheafProperCechResidueSpread.lean`) is **not** usable here — it spreads *exactness*,
and exactness is false for a fibrewise-trivial sheaf on a genus-1 fibre. See the rejected split below.

## Where reducedness is used

Only in `exists_pullback_iso_of_kernel_finrank` (`KM-SEESAW-2′`), at the passage from "residue rank `1`
at every point" to "`ker d⁰` locally free of rank `1` over the base". Over a non-reduced base the
statement is **false**: on
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

/-!
### A rejected split, and why (read before re-deriving it)

A first attempt fed the engine
`IsInvertible.exists_away_orderedBaseCech_exact_of_residueField_exact` directly, via the sub-lemma
"fibrewise trivial ⟹ the base-Čech complex is exact after `⊗ κ(p)` in every degree `q < card ι`".
**That sub-lemma is false.** `Function.Exact` at index `q` asserts exactness at position `q + 1`, i.e.
`H^{q+1}(X_p, M_p) = 0`; fibrewise *triviality* gives `M_p ≅ 𝒪_{X_p}`, and on a genus-1 fibre
`H¹(E_p, 𝒪) ≅ κ(p) ≠ 0`. Counterexample: `R = k` a field, `X = E/k`, `M = 𝒪_E`, any affine cover with
`card ι ≥ 2`.

The tree's own results mark the boundary exactly:
`FibrewiseElliptic.sectionPoleSheafPower_residueField_orderedBaseCech_exactAt_succ`
(`EllipticCurve/PoleSheafBaseCechHigher.lean:295`) proves positive-degree exactness only for `𝒪(n[0])`
under `hn : 1 ≤ n` — ample positive twists, where `H¹` vanishes. `n = 0`, the trivial sheaf, is excluded
for precisely this reason.

Stacks `0EX7` does not need exactness either. It needs `h⁰(X_s, M_s)` to be **constant** `= 1`, i.e. the
*kernel* of `d⁰` to have constant residue rank — after which `π_* M` is invertible and the counit
`π^* π_* M → M` is an isomorphism. So the split below goes through the kernel, and the tree already has
that shape: `FibrewiseElliptic.sectionPoleSheafPower_field_orderedBaseCech_kernel_finrank`
(`…:360`) computes `finrank K (ker (d⁰ ⊗ K)) = n`, Riemann–Roch for `𝒪(n[0])`.
Logged in `.mathlib-quality/b2_log.jsonl` under `KM-SEESAW-1`.
-/

/-- The scalar tower `Γ(S,⊤) → κ(s) → K` attached to a field-valued point of an affine `S`, where `s`
is the point `K` lies over.

**Duplication, deliberately recorded.** This fact is already proved in the tree, as the `private` pair
`affineFieldFactor_isScalarTower` / `affineFieldFactor_residue_isScalarTower`
(`EllipticCurve/PoleSheafBaseCechHigher.lean:55,84`). Both are pure affine-scheme infrastructure with no
elliptic-curve content, so the right end state is one public home in `ForMathlib/` that this file and
`PoleSheafBaseCechHigher` share; being `private` there is why it cannot simply be cited here. Logged in
`.mathlib-quality/DEBT.md` as a dedup item — do **not** resolve it by copying the 60-line proof body. -/
private theorem affineFieldFactor_residue_isScalarTower
    {S : Scheme.{u}} [IsAffine S]
    (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K] :
    let t : Spec (.of K) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, (⊤ : S.Opens)) K)) ≫ S.isoSpec.inv
    let x := Scheme.SpecToEquivOfField K S t
    let s := x.1
    let ψ := x.2
    letI : Algebra Γ(S, (⊤ : S.Opens)) ↥(S.residueField s) :=
      ((S.fromSpecResidueField s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
    letI : Algebra (↥(S.residueField s)) K := ψ.hom.toAlgebra
    IsScalarTower Γ(S, (⊤ : S.Opens)) (↥(S.residueField s)) K := by
  sorry

/-- **(KM-SEESAW-1′-res)** The residue-field form: at a point `s` of the base, fibrewise triviality of
`M` makes `ker (d⁰ ⊗ κ(s))` one-dimensional.

This is the whole geometric content of `KM-SEESAW-1′`. `H⁰` of the base-Čech complex is `Γ` of the
module (`baseSectionsIsoKernelOrderedBaseCechDifferential`), base change along
`Spec κ(s) ⟶ S` turns it into `Γ(X_s, M_s)` (`orderedBaseCechComplexBaseChangeIso`), fibrewise
triviality replaces `M_s` by `𝒪_{X_s}`, and `UniversallyOConnected π` evaluates that to `κ(s)`. -/
theorem orderedBaseCech_residueField_kernel_finrank_of_fibre_trivial
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S) [Algebra Γ(S, (⊤ : S.Opens)) ↥(S.residueField s)]
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (Limits.pullback.fst π x)).obj M ≅ unitObj (Limits.pullback π x))) :
    let C := orderedBaseCechComplex π M U
    Module.finrank ↥(S.residueField s)
      (LinearMap.ker ((C.d 0 1).hom.baseChange ↥(S.residueField s))) = 1 := by
  sorry

/-- **(KM-SEESAW-1′)** Fibrewise triviality makes the residue rank of `ker d⁰` equal to `1` at every
prime.

`H⁰` of the base-Čech complex is `Γ(X_p, M_p)`, and `M_p ≅ 𝒪_{X_p}`, so this is
`Γ(X_p, 𝒪) = κ(p)` — one-dimensional. That last identification is exactly `UniversallyOConnected π`
read on the fibre `x : Spec κ(p) ⟶ Spec R`, which is why `hπ` is the hypothesis that carries it. -/
theorem orderedBaseCech_kernel_finrank_of_fibre_trivial
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K]
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (Limits.pullback.fst π x)).obj M ≅ unitObj (Limits.pullback π x))) :
    let C := orderedBaseCechComplex π M U
    Module.finrank K (LinearMap.ker ((C.d 0 1).hom.baseChange K)) = 1 := by
  dsimp only
  let R := Γ(S, (⊤ : S.Opens))
  let t : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ S.isoSpec.inv
  let x := Scheme.SpecToEquivOfField K S t
  let s := x.1
  let ψ := x.2
  letI : Algebra R ↥(S.residueField s) :=
    ((S.fromSpecResidueField s).appTop ≫
      (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
  letI : Algebra (↥(S.residueField s)) K := ψ.hom.toAlgebra
  letI : IsScalarTower R (↥(S.residueField s)) K :=
    affineFieldFactor_residue_isScalarTower K
  let C := orderedBaseCechComplex π M U
  exact (LinearMap.finrank_ker_baseChange_eq (↥(S.residueField s)) K (C.d 0 1).hom).trans
    (orderedBaseCech_residueField_kernel_finrank_of_fibre_trivial hπ hM U hU hUaff s hfib)

/-- **(KM-SEESAW-2′)** Constant residue rank `1` of `ker d⁰`, over a **reduced** base, makes
`π_* M` invertible and the counit an isomorphism: `M ≅ π^* N`.

Constant fibre rank over a reduced base is what forces `ker d⁰` — which is `Γ(M)` as a module over the
base ring — to be locally free of rank `1`; that is the only place `IsReduced` is used, and over a
non-reduced base the conclusion is false (`k[ε]/(ε²)`, see the module docstring). The counit
`π^* π_* M → M` is then a map of invertible sheaves that is nonzero on every fibre, hence an
isomorphism, which is where the local-to-global glue (`nonempty_unitObj_iso_of_normalized_glue`) enters. -/
theorem exists_pullback_iso_of_kernel_finrank
    {X S : Scheme.{u}} [IsAffine S] [IsReduced S] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hrank : ∀ (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K],
      let C := orderedBaseCechComplex π M U
      Module.finrank K (LinearMap.ker ((C.d 0 1).hom.baseChange K)) = 1) :
    ∃ N : S.Modules, IsInvertible N ∧
      Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback π).obj N) := by
  sorry

/-- **(KM-SEESAW, Stacks 0EX7 at rank 1)** The seesaw theorem: an invertible sheaf on a proper flat
family of finite presentation over a **reduced** affine base, trivial on every fibre, is pulled back
from the base.

The composition of `orderedBaseCech_residueField_exact_of_fibre_trivial` (KM-SEESAW-1) with
`exists_pullback_iso_of_residueField_exact` (KM-SEESAW-2), over the finite affine trivialising cover
produced by `IsInvertible.exists_finiteAffineBaseCech_flat`. -/
theorem exists_pullback_iso_of_fibrewise_trivial_of_isReduced
    {X S : Scheme.{u}} [IsAffine S] [IsReduced S] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (Limits.pullback.fst π x)).obj M ≅ unitObj (Limits.pullback π x))) :
    ∃ N : S.Modules, IsInvertible N ∧
      Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback π).obj N) := by
  obtain ⟨ι, hι, U, hU, hUaff, htriv, hflat⟩ := hM.exists_finiteAffineBaseCech_flat π
  letI : Fintype ι := Fintype.ofFinite ι
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  exact exists_pullback_iso_of_kernel_finrank hπ hM U hU hUaff
    fun K _ _ => orderedBaseCech_kernel_finrank_of_fibre_trivial hπ hM U hU hUaff K hfib

end ModularCurves
