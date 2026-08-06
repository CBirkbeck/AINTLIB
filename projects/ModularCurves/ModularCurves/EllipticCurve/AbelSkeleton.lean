/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.BaseChangeKerCoker
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCech
import ModularCurves.Picard.InvertibleSheafBaseCechFlat
import ModularCurves.Picard.RigidDescent

/-!
# Skeleton for the Abel route to the relative Weil pairing (`/develop --decompose`, round 13)

Statements transcribed from Katz-Mazur's proof of **Theorem 2.1.2 (Abel)**, book pp. 63-67.
Plan: `.mathlib-quality/plan-ds4-abel-pairing.md`. Attack record: `.mathlib-quality/decomposition.md`,
rounds 1-13.

## Round 12 killed the first draft of this file; read this before re-stating anything

Draft 1 contained two statements, both **false**:

* *"field-fibre exact implies exact over the base ring"* -- false: over `Z`, the complex `Z -> Q -> 0` has
  homology `Q/Z` nonzero yet every field fibre is exact. Fields do not detect non-finitely-generated
  homology. The missing hypothesis is finiteness of the homology, i.e. exactly KM p. 66's *"coherent sheaf
  ... with all fibers zero ... by Nakayama's lemma"*.
* *"exact + fibre rank 1 implies kernel projective"* -- false: `R = k[e]/(e^2)` with `R -e-> R -e-> R` is
  exact at the middle, has `dim_K ker = 1` over every field, and `ker(e)` is not projective. What fails is
  the comparison `K (x) ker d0 -> ker(d0_K)`.

**And the correct package was already in the project all along** -- `ForMathlib/BaseChangeKerCoker.lean`
supplies `Module.Finite.ker_of_bounded_forall_field_baseChange_exact`,
`Module.Projective.ker_of_bounded_forall_field_baseChange_exact` (`:1179`),
`kerBaseChangeComparison_bijective_of_bounded_forall_field_baseChange_exact` (`:1192`) and
`Module.rankAtStalk_ker_eq_of_bounded_forall_field_baseChange_exact` (`:1204`), each carrying the
hypotheses draft 1 dropped: a **bounded** complex (`Subsingleton (M (N+1))`), `hcomp : d . d = 0`, and
field-fibre exactness **at every `n < N`**, not at one spot.

So the leaves below are *applications* of that package, not restatements of it. The only genuinely new
mathematical content on this branch is the pair of **fibre** facts for an arbitrary fibrewise-degree-one
`L`, which is `AP-A1` and is pure genus-one Riemann-Roch.

## The sheaf is an arbitrary invertible `L`

Never `O(n[0])`. `PoleSheafBaseCechHigher.lean` proves the fibre facts for the pole sheaves only;
identifying a general `L` with `O([0])` via relative Abel is circular, since Abel is what this branch
proves. See `b2_log.jsonl`, entries `KM-SEESAW-1` and `KM-SEESAW-2prime`.
-/

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace ModularCurves

variable {X S : Scheme.{u}} [IsAffine S] [IsNoetherian X] [X.IsSeparated] {pi : X ⟶ S}

/-- **(AP-A1a)** The first fibre fact: for an invertible `L` fibrewise of degree one, the ordered
base-Cech complex is exact in **every** positive degree after base change to every field over the base.

This is the genuinely new content of group A, and it is pure genus-one Riemann-Roch: `H^q(E_s, L_s) = 0`
for `q >= 1` because `deg L_s = 1 > 2g - 2 = 0`.

KM p. 66: *"over an algebraically closed field, `H^1(E, L) = 0` for `degree(L) > 2g-2 = 0`."*

`hdeg` is a placeholder for "fibrewise of degree one": the tree has no notion of the degree of an
invertible sheaf, only `RelEffCartierDiv.degree`. Supplying it is where that definition is needed, and
this is the one place it is needed. -/
theorem orderedBaseCech_field_exactAt_succ_of_fibrewise_degree_one
    [LocallyOfFinitePresentation pi] [IsProper pi] [Flat pi]
    {M : X.Modules} (hM : IsInvertible M)
    {iota : Type u} [Fintype iota] [LinearOrder iota]
    (U : iota → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hdeg : ∀ {k : Type u} [Field k], (Spec (.of k) ⟶ S) → Prop)
    (n : ℕ) (hn : n < Fintype.card iota)
    (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K] :
    let C := orderedBaseCechComplex pi M U
    Function.Exact ((C.d n (n + 1)).hom.baseChange K)
      ((C.d (n + 1) (n + 2)).hom.baseChange K) := by
  sorry

/-- **(AP-A1b)** The second fibre fact: the degree-zero kernel has dimension `1` over every residue field.

Riemann-Roch again: `h0 - h1 = deg + 1 - g = 1` and `h1 = 0` by AP-A1a. Stated over
`PrimeSpectrum` residue fields, which is the shape
`Module.rankAtStalk_ker_eq_of_bounded_forall_field_baseChange_exact` consumes. -/
theorem orderedBaseCech_residueField_kernel_finrank_of_fibrewise_degree_one
    [LocallyOfFinitePresentation pi] [IsProper pi] [Flat pi]
    {M : X.Modules} (hM : IsInvertible M)
    {iota : Type u} [Fintype iota] [LinearOrder iota]
    (U : iota → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hdeg : ∀ {k : Type u} [Field k], (Spec (.of k) ⟶ S) → Prop)
    (p : PrimeSpectrum Γ(S, (⊤ : S.Opens))) :
    let C := orderedBaseCechComplex pi M U
    Module.finrank p.asIdeal.ResidueField
      (LinearMap.ker ((C.d 0 1).hom.baseChange p.asIdeal.ResidueField)) = 1 := by
  sorry

/- **(AP-A2, AP-A3) -- deliberately NOT stated here.**

Given AP-A1a and AP-A1b, the passage to "`f_*L` is invertible over the base ring, compatibly with base
change" is **not new mathematics**: it is
`Module.rankAtStalk_ker_eq_of_bounded_forall_field_baseChange_exact` together with
`Module.Projective.ker_of_bounded_forall_field_baseChange_exact` and
`kerBaseChangeComparison_bijective_of_bounded_forall_field_baseChange_exact`
(`ForMathlib/BaseChangeKerCoker.lean:1204, :1179, :1192`), applied to `orderedBaseCechComplex pi M U`.

Its remaining obligations are the package's own hypotheses, all of which the tree can already supply for
this complex: `hcomp` (`d . d = 0`, from the complex), boundedness via
`orderedBaseCechObject_subsingleton_of_card_le`, and flatness of the terms via
`orderedBaseCechObject_flat_of_isInvertible`. `Picard/InvertibleSheafProperCechResidueSpread.lean:23`
assembles exactly this set for its own purposes and is the model to copy.

Writing these as fresh `theorem`s here is what produced draft 1's two false statements. They belong in the
ticket as "apply the package", not as new statements. -/

/- **(AP-B1) -- still not statable, and the reason is now geometric, not an API wrinkle.**

Round 12: an invertible `f_*L` **need not have a global basis**. KM chooses it Zariski-locally on `S`
(p. 66: *"Because `f_*L` is invertible on `S`, Zariski locally on `S` we may pick an `O_S`-basis `l` of
`f_*L`"*). Draft 1 quantified over a global `l`, a genuine geometric error that the elaboration failure
happened to hide.

The correct shape restricts to an open where `baseSections pi M` is free of rank one, takes a local
generator, and forms `O_E -> L` there. It must be phrased against `Scheme.Modules.baseSections pi M`,
which carries the `Gamma(S,O_S)`-structure intrinsically, and use
`baseSectionsIsoKernelOrderedBaseCechDifferential` only to transport algebraic results in. Blocked on
AP-A3's chosen presentation, and that choice belongs to AP-A3's ticket. -/

end ModularCurves
