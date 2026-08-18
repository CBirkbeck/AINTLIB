/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.AffineFieldPointTower
import ModularCurves.ForMathlib.BaseChangeKerCoker
import ModularCurves.ForMathlib.SeesawBaseLocallyTrivial
import ModularCurves.Picard.InvertibleSheafProperCechResidueSpread
import ModularCurves.Picard.RigidDescent
import ModularCurves.WeilPairing.RelPicLocal

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

/-- A ring extension whose structure map is bijective is free of rank one over the base. -/
theorem _root_.Module.finrank_eq_one_of_bijective_algebraMap
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Nontrivial R]
    (h : Function.Bijective (algebraMap R A)) :
    Module.finrank R A = 1 := by
  have e : R ≃ₗ[R] A := LinearEquiv.ofBijective (Algebra.linearMap R A) h
  rw [← e.finrank_eq, Module.finrank_self]

/-- Over a family whose structure map on global sections is bijective — the `⊤`-component of
`UniversallyOConnected` — the base-linear global sections of the structure sheaf are free of rank
one over the base ring. This is step 5 of the route below. -/
theorem finrank_baseSections_unitObj_eq_one {X S : Scheme.{u}} (p : X ⟶ S)
    [Nontrivial Γ(S, (⊤ : S.Opens))] (h : Function.Bijective p.appTop.hom) :
    Module.finrank Γ(S, (⊤ : S.Opens))
      (AlgebraicGeometry.Scheme.Modules.baseSections p (unitObj X)) = 1 := by
  letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(X, (⊤ : X.Opens)) := p.appTop.hom.toAlgebra
  have e : (AlgebraicGeometry.Scheme.Modules.baseSections p (unitObj X) : Type u) ≃ₗ[
      Γ(S, (⊤ : S.Opens))] Γ(X, (⊤ : X.Opens)) :=
    { __ := AddEquiv.refl (AlgebraicGeometry.Scheme.Modules.baseSections p (unitObj X) : Type u)
      map_smul' := by
        intro r x
        exact AlgebraicGeometry.Scheme.Modules.baseSections_smul p (unitObj X) r x }
  rw [e.finrank_eq]
  exact Module.finrank_eq_one_of_bijective_algebraMap _ _ h

/-- **(KM-SEESAW-1′, scheme-side)** The base-changed degree-zero Čech kernel is free of rank one
over `Γ(T, ⊤)` for *any* affine `T` over `S` on whose fibre `M` is trivial — no field hypothesis.

This is the form in which the five-step route of the residue-field corollary below actually
composes: `orderedBaseCechComplexBaseChangeIso` produces `ModuleCat.extendScalars t.appTop.hom`,
whose scalars are `Γ(T, ⊤)`, so stating the result over `Γ(T, ⊤)` makes
`algebraMap Γ(S,⊤) Γ(T,⊤) = t.appTop.hom` hold by `rfl` and the two engines match syntactically.
Transport to `κ(s)` happens once, at the end, in the corollary.

**DO NOT weaken `hfibt` to fibrewise triviality** (external review, 2026-08-08). `hfibt` asserts
`M_T ≅ 𝒪_{X_T}` for *this* `T`; the conclusion is FALSE under the weaker hypothesis "`M` is
trivial on every field-valued fibre". Counterexample: `π = 𝟙_S` with `S = Spec R`, `R` a Dedekind
domain of nontrivial class group, `M` a nonprincipal invertible ideal `N`. Then `π` is proper,
flat, of finite presentation and universally `O`-connected, and `N ⊗ K` is one-dimensional hence
trivial over every field `K`; but at `T = S` the kernel is `N` itself, which is not free. Both
call sites below are *field-valued* points, where `hfib` does supply `hfibt`. -/
theorem orderedBaseCech_appTop_kernel_finrank_of_fibre_trivial
    {X S T : Scheme.{u}} [IsAffine S] [IsAffine T] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (t : T ⟶ S) [Nontrivial Γ(T, (⊤ : T.Opens))]
    (hfibt : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (Limits.pullback.fst π t)).obj M ≅ unitObj (Limits.pullback π t))) :
    letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) := t.appTop.hom.toAlgebra
    let C := orderedBaseCechComplex π M U
    Module.finrank Γ(T, (⊤ : T.Opens))
      (LinearMap.ker ((C.d 0 1).hom.baseChange Γ(T, (⊤ : T.Opens)))) = 1 := by
  dsimp only
  letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) := t.appTop.hom.toAlgebra
  letI : M.IsQuasicoherent := hM.isQuasicoherent
  set p : Limits.pullback π t ⟶ T := Limits.pullback.snd π t with hp
  set Mt := (AlgebraicGeometry.Scheme.Modules.pullback (Limits.pullback.fst π t)).obj M with hMt
  set Ut : ι → (Limits.pullback π t).Opens :=
    fun i => Limits.pullback.fst π t ⁻¹ᵁ U i with hUtdef
  have hUtcover : IsOpenCover Ut := (Limits.pullback.fst π t).iSup_preimage_eq_top hU
  -- (1) algebraic base change of the kernel is the kernel after extension of scalars
  let e1 := ModularCurves.HomologicalComplex.baseChangeKernelZeroLinearEquiv
    (orderedBaseCechComplex π M U) Γ(T, (⊤ : T.Opens))
  -- (2)+(3) that complex is the fibre's own ordered base-Čech complex
  let eC := orderedBaseCechComplexBaseChangeIso π t M U hUaff
  let e2 := HomologicalComplex.kernelZeroLinearEquivOfHom eC.hom eC.inv
    (by rw [← HomologicalComplex.comp_f, eC.hom_inv_id, HomologicalComplex.id_f])
    (by rw [← HomologicalComplex.comp_f, eC.inv_hom_id, HomologicalComplex.id_f])
  -- (4) that kernel is the fibre's base-linear global sections
  let e3 := (AlgebraicGeometry.Scheme.Modules.baseSectionsIsoKernelOrderedBaseCechDifferential
    p Mt Ut hUtcover).toLinearEquiv
  -- (5) fibrewise triviality, then `UniversallyOConnected`
  let e4 := (AlgebraicGeometry.Scheme.Modules.baseSectionsMapIso p hfibt.some).toLinearEquiv
  have hbij : Function.Bijective p.appTop.hom := by
    haveI := hπ t (⊤ : T.Opens)
    exact (ConcreteCategory.bijective_of_isIso (p.app (⊤ : T.Opens)))
  rw [(e1.trans (e2.trans (e3.symm.trans e4))).finrank_eq]
  exact finrank_baseSections_unitObj_eq_one p hbij

/-- **(KM-SEESAW-1′-res)** The residue-field form: at a point `s` of the base, fibrewise triviality of
`M` makes `ker (d⁰ ⊗ κ(s))` one-dimensional.

This is the whole geometric content of `KM-SEESAW-1′`.

**The route, with every input located (do not re-derive; and note which tools are NOT usable).**

1. `ker ((C.d 0 1).hom.baseChange κ(s))` ≃ the degree-`0` kernel of the `extendScalars κ(s)` image of
   `C`, by `ModularCurves.HomologicalComplex.baseChangeKernelZeroLinearEquiv`
   (`ForMathlib/LowDegreeFiniteProjectiveReplacement.lean:164`). This is pure bookkeeping between
   `LinearMap.baseChange` and `ModuleCat.extendScalars`; `baseCechKernelOrderedBaseChangeLinearEquiv`
   (`ForMathlib/SchemeModuleOrderedBaseCechZero.lean:161`) uses it the same way and is the model.
2. That complex is the fibre's own ordered base-Čech complex, by
   `orderedBaseCechComplexBaseChangeIso` (`ForMathlib/AffineModuleCechBaseChange.lean:1037`), for
   `t : Spec κ(s) ⟶ S`. Needs `[IsAffine S]`, `[IsAffine (Spec κ(s))]`, `[M.IsQuasicoherent]` — the last
   from `hM.isQuasicoherent`. **No flatness or exactness is needed for this step**, which is the point.
3. Transport the kernel along that iso of complexes (`HomologicalComplex.kernelZeroLinearEquivOfHom`,
   used in the same way at `SchemeModuleOrderedBaseCechZero.lean:161`).
4. `baseSectionsIsoKernelOrderedBaseCechDifferential`
   (`ForMathlib/SchemeModuleOrderedBaseCechZero.lean:256`) applied **on the fibre** identifies that
   kernel with `baseSections π_s M_s`.
5. `hfib` replaces `M_s` by `unitObj`, and `hπ` — `UniversallyOConnected π`, i.e. Stacks 0EX7's
   "`f_*𝒪_X = 𝒪_S` after arbitrary base change" — evaluates `baseSections π_s 𝒪` to `κ(s)`. Close with
   `Module.finrank_self`.

**Not usable here, and why** — `baseSectionsBaseChangeEquiv_of_orderedBaseCech_package`
(`EllipticCurve/PoleSheafNeighborhoodHOne.lean:377`) looks like exactly this statement, but its `hexact`
hypothesis is positive-tail exactness of the complex, which is false for a fibrewise-*trivial* sheaf on a
genus-1 fibre (`H¹(E_s, 𝒪) = κ(s)`; see the rejected split above). Its inner tool
`baseSectionsBaseChangeLinearEquivOfOrderedCechKernelComparison` takes kernel-comparison bijectivity
instead of exactness and *is* usable, but steps 1–4 above already give the identification directly, so it
is not needed. -/
theorem orderedBaseCech_residueField_kernel_finrank_of_fibre_trivial
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S)
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (Limits.pullback.fst π x)).obj M ≅ unitObj (Limits.pullback π x))) :
    letI : Algebra Γ(S, (⊤ : S.Opens)) ↥(S.residueField s) :=
      ((S.fromSpecResidueField s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
    let C := orderedBaseCechComplex π M U
    Module.finrank ↥(S.residueField s)
      (LinearMap.ker ((C.d 0 1).hom.baseChange ↥(S.residueField s))) = 1 := by
  dsimp only
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ(Spec (S.residueField s), (⊤ : (Spec (S.residueField s)).Opens)) :=
    (S.fromSpecResidueField s).appTop.hom.toAlgebra
  letI : Algebra Γ(Spec (S.residueField s), (⊤ : (Spec (S.residueField s)).Opens))
      ↥(S.residueField s) :=
    (Scheme.ΓSpecIso (S.residueField s)).hom.hom.toAlgebra
  letI : Algebra Γ(S, (⊤ : S.Opens)) ↥(S.residueField s) :=
    ((S.fromSpecResidueField s).appTop ≫
      (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
  letI : IsScalarTower Γ(S, (⊤ : S.Opens))
      Γ(Spec (S.residueField s), (⊤ : (Spec (S.residueField s)).Opens)) ↥(S.residueField s) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Field Γ(Spec (S.residueField s), (⊤ : (Spec (S.residueField s)).Opens)) :=
    (MulEquiv.isField (Field.toIsField ↥(S.residueField s))
      (Scheme.ΓSpecIso (S.residueField s)).commRingCatIsoToRingEquiv.toMulEquiv).toField
  rw [LinearMap.finrank_ker_baseChange_eq
    Γ(Spec (S.residueField s), (⊤ : (Spec (S.residueField s)).Opens)) ↥(S.residueField s)
    ((orderedBaseCechComplex π M U).d 0 1).hom]
  exact orderedBaseCech_appTop_kernel_finrank_of_fibre_trivial hπ hM U hU hUaff
    (S.fromSpecResidueField s) (hfib (S.fromSpecResidueField s))

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

/-- **(KM-SEESAW-2″)** Constant residue rank `1` of `ker d⁰` **together with fibrewise triviality**,
over a **reduced** base, makes `π_* M` invertible and the counit an isomorphism: `M ≅ π^* N`.

The two hypotheses do different jobs and **neither can be dropped**:

* `hrank` — constant residue rank — is what forces `ker d⁰`, i.e. `Γ(M)` as a module over the base ring,
  to be locally free of rank `1`. This is the only place `IsReduced` is used; over a non-reduced base the
  conclusion is false (`k[ε]/(ε²)`, see the module docstring).
* `hfib` — fibrewise triviality — is what makes the counit `π^* π_* M → M` *surjective*: the generator of
  `Γ(X_s, M_s) ≅ Γ(X_s, 𝒪)` is nowhere vanishing precisely because `M_s ≅ 𝒪_{X_s}`. Without it the counit
  is only injective.

**An earlier version of this leaf had `hrank` alone and was FALSE** — logged in
`.mathlib-quality/b2_log.jsonl`. Counterexample: `S = Spec k`, `X = E` an elliptic curve, `M = 𝒪_E(P)`
for a rational `P ≠ 0`. Riemann–Roch on genus `1` with `deg = 1 > 2g-2 = 0` gives `h¹ = 0` and
`h⁰ = deg + 1 - g = 1`, stably under field extension, so `hrank` holds; but `𝒪_E(P) ≇ 𝒪_E` (degrees `1`
and `0`), and indeed the counit is the inclusion `𝒪_E → 𝒪_E(P)`, injective and not surjective — the
generator of `Γ(𝒪_E(P))` is the image of `1`, whose zero divisor is `P`. Substituting the *cohomological
dimension* `h⁰ = 1` for the *geometric* hypothesis `M_s ≅ 𝒪` loses exactly the nowhere-vanishing
information, and 0EX7's own hypothesis (1) is the geometric one.

`hhigh` — exactness of the base-Čech complex at the positions `≥ 2` — is the third hypothesis, and
it is what makes the Grauert substitute run: it supplies `Module.Flat Γ(S,⊤) (ker d¹)` and the
degree-one kernel base-change comparison (`Module.Flat.ker_of_bounded_exact_from` and
`kerBaseChangeComparison_bijective_of_bounded_exact_from`, both at `k = 1`) that Half B.1,
`baseSections_invertible_of_kernel_finrank_of_isReduced`, needs. It is strictly weaker than
positive-tail exactness: position `1`, i.e. `H¹(X, M) = 0`, is **not** demanded — that is false on a
genus-1 fibre — while `H^{≥2}` does vanish for a relative curve, so `hhigh` is expected to be
automatic in the application. See the "rejected split" in the module docstring for the boundary. -/
theorem exists_pullback_iso_of_kernel_finrank_of_fibre_trivial
    {X S : Scheme.{u}} [IsAffine S] [IsReduced S] [IsNoetherian S] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hhigh : ∀ q, 1 ≤ q → q < Fintype.card ι →
      Function.Exact ((orderedBaseCechComplex π M U).d q (q + 1)).hom
        ((orderedBaseCechComplex π M U).d (q + 1) (q + 2)).hom)
    (hrank : ∀ (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K],
      let C := orderedBaseCechComplex π M U
      Module.finrank K (LinearMap.ker ((C.d 0 1).hom.baseChange K)) = 1)
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (Limits.pullback.fst π x)).obj M ≅ unitObj (Limits.pullback π x))) :
    ∃ N : S.Modules, IsInvertible N ∧
      Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback π).obj N) := by
  -- Half B.1: the pushforward's global sections form an invertible `Γ(S, ⊤)`-module
  have hinv := baseSections_invertible_of_kernel_finrank_of_isReduced hM U hU hUaff hhigh
    (fun K _ _ ↦ hrank K)
  -- Half B.2: `M` is trivial over a Zariski open cover *of the base*
  obtain ⟨ι', V, hV, hVtriv⟩ := exists_baseCover_restrict_unitObj_iso_of_invertible_baseSections
    hπ hM U hU hUaff hhigh (fun K _ _ ↦ hrank K) hinv hfib
  -- Half A, at `M' = 𝒪_X` and `N i = 𝒪_{V i}`: the descent consumes the base-local trivialisations
  -- in twisted form, and both twists are trivial.
  have hglue : ∀ i, Nonempty (M.restrict (π ⁻¹ᵁ V i).ι ≅
      tensorObj ((unitObj X).restrict (π ⁻¹ᵁ V i).ι)
        ((AlgebraicGeometry.Scheme.Modules.pullback (π ∣_ V i)).obj (unitObj (V i).toScheme))) := by
    intro i
    letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory (π ⁻¹ᵁ V i).toScheme
    letI := AlgebraicGeometry.Scheme.Modules.symmetricCategory (π ⁻¹ᵁ V i).toScheme
    refine toSkeleton_eq_toSkeleton_iff.mp ?_
    have h1 : toSkeleton ((unitObj X).restrict (π ⁻¹ᵁ V i).ι) = 1 :=
      (toSkeleton_eq_toSkeleton_iff.mpr
        ⟨(restrictFunctorIsoPullback (π ⁻¹ᵁ V i).ι).app (unitObj X) ≪≫
          pullbackUnitIso (π ⁻¹ᵁ V i).ι⟩).trans toSkeleton_unitObj
    have h2 : toSkeleton ((AlgebraicGeometry.Scheme.Modules.pullback (π ∣_ V i)).obj
        (unitObj (V i).toScheme)) = 1 :=
      (toSkeleton_eq_toSkeleton_iff.mpr ⟨pullbackUnitIso (π ∣_ V i)⟩).trans toSkeleton_unitObj
    rw [toSkeleton_tensorObj_eq, h1, h2, one_mul]
    exact (toSkeleton_eq_toSkeleton_iff.mpr (hVtriv i)).trans toSkeleton_unitObj
  obtain ⟨N₀, hN₀, e⟩ := exists_pullback_twist_of_locally' π hπ.isIso_app hM isInvertible_unit
    V hV (fun i ↦ unitObj (V i).toScheme) (fun _ ↦ isInvertible_unit) hglue
  -- `𝒪_X ⊗ π^*N₀ ≅ π^*N₀`, so the twisted conclusion is the seesaw's
  refine ⟨N₀, hN₀, ?_⟩
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  letI := AlgebraicGeometry.Scheme.Modules.symmetricCategory X
  refine toSkeleton_eq_toSkeleton_iff.mp ?_
  have he := toSkeleton_eq_toSkeleton_iff.mpr e
  rwa [toSkeleton_tensorObj_eq, toSkeleton_unitObj, one_mul] at he

/-- **(KM-SEESAW, Stacks 0EX7 at rank 1)** The seesaw theorem: an invertible sheaf on a proper flat
family of finite presentation over a **reduced** affine base, trivial on every fibre, is pulled back
from the base.

The composition of `orderedBaseCech_kernel_finrank_of_fibre_trivial` (KM-SEESAW-1′) with
`exists_pullback_iso_of_kernel_finrank_of_fibre_trivial` (KM-SEESAW-2″), over the finite affine
trivialising cover produced by `IsInvertible.exists_finiteAffineBaseCech_flat`. Note that `hfib` is fed
to **both** — the descent step needs it in its own right, not merely through the rank.

**On `hhigh`.** KM-SEESAW-2″ needs `H^{≥2}` of the base-Čech complex to vanish (see its docstring);
here the cover is *produced inside the proof* by `exists_finiteAffineBaseCech_flat`, which gives no
control on it, so the hypothesis has to be quantified over all finite affine open covers. It is not
derived from the fibre side, and that is the one remaining obligation on the way to a
hypothesis-free `0EX7`: for a relative curve `H^{≥2}(X_s, M_s) = 0` fibrewise
(`subsingleton_H_add_two_of_two_affine_open_cover`), and
`HomologicalComplex.functionExact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology`
lifts fibrewise exactness to the base ring exactly as `kernel_data_of_hasDegreeOneFibreCohomology`
does — over `q ≥ 1` instead of `q ≥ 0`. Discharging it needs a *curve* hypothesis on `π`, which this
statement (a general proper flat family) does not carry, hence the binder. -/
theorem exists_pullback_iso_of_fibrewise_trivial_of_isReduced
    {X S : Scheme.{u}} [IsAffine S] [IsReduced S] [IsNoetherian S] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    (hhigh : ∀ {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens), IsOpenCover U →
      (∀ i, IsAffineOpen (U i)) → ∀ q, 1 ≤ q → q < Fintype.card ι →
        Function.Exact ((orderedBaseCechComplex π M U).d q (q + 1)).hom
          ((orderedBaseCechComplex π M U).d (q + 1) (q + 2)).hom)
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (Limits.pullback.fst π x)).obj M ≅ unitObj (Limits.pullback π x))) :
    ∃ N : S.Modules, IsInvertible N ∧
      Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback π).obj N) := by
  obtain ⟨ι, hι, U, hU, hUaff, htriv, hflat⟩ := hM.exists_finiteAffineBaseCech_flat π
  letI : Fintype ι := Fintype.ofFinite ι
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  exact exists_pullback_iso_of_kernel_finrank_of_fibre_trivial hπ hM U hU hUaff
    (hhigh U hU hUaff)
    (fun K _ _ => orderedBaseCech_kernel_finrank_of_fibre_trivial hπ hM U hU hUaff K hfib) hfib

end ModularCurves
