/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCech
import ModularCurves.Picard.InvertibleSheafBaseCechFlat
import ModularCurves.Picard.RigidDescent
import ModularCurves.ForMathlib.BaseChangeKerCoker

/-!
# Skeleton for the Abel route to the relative Weil pairing (`/develop --decompose` Step 2.5)

Every declaration here is a `:= by sorry` STATEMENT, transcribed from Katz–Mazur's own proof of
**Theorem 2.1.2 (Abel)**, book pp. 63–67. Plan: `.mathlib-quality/plan-ds4-abel-pairing.md`; decomposition
and attack record: `.mathlib-quality/decomposition.md` (rounds 1–11); board group A/B.

## Why the hypotheses are cohomological rather than "degree one"

KM's steps (d)–(f) consume exactly two facts about the fibres of an invertible `L`: that `H¹` vanishes and
that `h⁰ = 1`. "Fibrewise degree one" is how KM *supplies* those, via Riemann–Roch. The tree has no notion
of the degree of an invertible sheaf (only `RelEffCartierDiv.degree`, `LevelStructure/CartierDivisor.lean:108`),
so this skeleton takes the two cohomological facts as explicit hypotheses and leaves
"degree one ⟹ those two facts" to `AP-A1`, which is where a degree notion is actually needed. That keeps
the skeleton compiling today and confines the missing definition to one leaf.

## Čech form, and the trap it avoids

The fibre facts are phrased against `orderedBaseCechComplex` — the tree's derived-functor-free surrogate,
since mathlib has no cohomology-and-base-change and no `R¹f_*`. **The sheaf is an arbitrary invertible `L`,
never `𝒪(n[0])`**: specialising to the pole sheaves and identifying a general `L` with `𝒪([0])` via relative
Abel is circular, because Abel is what this file proves. `PoleSheafBaseCechHigher.lean`'s results are the
model case only. See `.mathlib-quality/b2_log.jsonl`, entries `KM-SEESAW-1` and `KM-SEESAW-2prime`, for the
two false leaves that this note exists to prevent recurring.
-/

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace ModularCurves

variable {X S : Scheme.{u}} [IsAffine S] [IsNoetherian X] [X.IsSeparated] {π : X ⟶ S}

/-- **(AP-A2, Čech form)** For an invertible `L` whose every residue fibre has vanishing `H¹`, the
base-Čech complex is exact at position `1` over the base ring itself.

KM p. 66: *"`R¹f_*ℒ = 0` because it is of formation compatible with arbitrary change of base (being an
`R¹f_*` for `f` proper and flat) and because over an algebraically closed field, `H¹(E, ℒ) = 0` for
`degree(ℒ) > 2g−2 = 0`. As `R¹f_*ℒ` is a coherent sheaf on `S` with all fibers zero, it vanishes by
Nakayama's lemma."* -/
theorem orderedBaseCech_exactAt_one_of_residueField_exactAt_one
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hfib : ∀ (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K],
      let C := orderedBaseCechComplex π M U
      Function.Exact ((C.d 0 1).hom.baseChange K) ((C.d 1 2).hom.baseChange K)) :
    let C := orderedBaseCechComplex π M U
    Function.Exact ((C.d 0 1).hom) ((C.d 1 2).hom) := by
  sorry

/-- **(AP-A3)** …and then the degree-zero kernel — which is `Γ(M)` over the base ring — is an invertible
module.

Mumford, *Abelian Varieties*, p. 53 **Corollary 3**, whose statement carries the parenthetical *"(unlike
Corollary 2, `Y` need not be reduced)"*; local freeness comes from the `K^•`-splitting argument on p. 52.

**TRAP.** State this from the `H¹`-vanishing hypothesis, **never** from a constant-fibre-dimension
hypothesis. Constant fibre dimension gives local freeness only over a *reduced* base (Mumford Lemma 1,
p. 51), and that route is `b2_log.jsonl`'s `KM-SEESAW-2prime`, refuted by `𝒪_E(P)` of degree one. -/
theorem invertible_kernel_of_orderedBaseCech_exactAt_one
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hex : let C := orderedBaseCechComplex π M U
      Function.Exact ((C.d 0 1).hom) ((C.d 1 2).hom))
    (hrk : ∀ (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K],
      let C := orderedBaseCechComplex π M U
      Module.finrank K (LinearMap.ker ((C.d 0 1).hom.baseChange K)) = 1) :
    let C := orderedBaseCechComplex π M U
    Module.Projective Γ(S, (⊤ : S.Opens)) (LinearMap.ker ((C.d 0 1).hom)) := by
  sorry

/- **(AP-B1) — NOT YET STATABLE, and this is a finding, not an omission.**

KM pp. 66–67's step (e) is: *"the map of invertible sheaves `𝒪 --ℓ--> ℒ` on `E` is injective, and remains
so after any base change `T → S`. For this we are reduced to the case `S = Spec(k)` with `k` a field, and
`ℓ ∈ H⁰(E, ℒ)` a `k`-basis, so non-zero, in which case the assertion is obvious."*

Stating it needs "`ℓ` is a basis of `f_*M`", and `f_*M` is `AP-A3`'s output — `LinearMap.ker ((C.d 0 1).hom)`
as a `Γ(S, ⊤)`-module. Writing `r • ℓ` for `r : Γ(S, ⊤)` and `ℓ : Γ(M, ⊤)` fails to elaborate: `Γ(M, ⊤)` is a
`Γ(X, ⊤)`-module and the `Γ(S, ⊤)`-action factors through `π`, so the statement needs a scalar tower that
is not currently set up.

**So AP-B1 is blocked on an API-design decision in AP-A3**, namely which module `f_*M` is presented as and
with which scalar-tower instances. That decision belongs in AP-A3's ticket, and AP-B1 should be stated only
after it. A first attempt here used `(hbasis : ∀ K …, True)` — a vacuous hypothesis that makes the
statement false as written — and was removed rather than shipped.
-/

end ModularCurves
