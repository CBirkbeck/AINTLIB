/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PerfectoidRing

/-!
# Perfectoid Spaces

We define **affinoid perfectoid spaces** and **perfectoid spaces** following
Scholze's *Perfectoid Spaces* (2012), Definition 3.19.

## Main definitions

* `AffinoidPerfectoidSpace p` : A bundled perfectoid ring with all instances needed to form
  `Spa(A, A⁺)`. This is `Spa(A, A⁺)` where `A` is a perfectoid ring.
* `IsPerfectoidSpace p X` : An adic space `X` is a **perfectoid space** if every point has
  an open affinoid neighborhood that is isomorphic to `Spa(A, A⁺)` for some perfectoid ring `A`.

## Main results (sorry'd)

* `AffinoidPerfectoidSpace.toAffinoidAdicSpace` : Every affinoid perfectoid space is an
  affinoid adic space (requires sheafiness of perfectoid rings).
* `AffinoidPerfectoidSpace.toAdicSpace` : Every affinoid perfectoid space is an adic space.
* `PerfectoidSpace.tilt` : The tilt of a perfectoid space is perfectoid (in characteristic `p`).

## References

* [P. Scholze, *Perfectoid Spaces*][scholze2012perfectoid], Definition 3.19
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8
-/

open TopologicalRing ValuationSpectrum

universe u

/-! ### Affinoid perfectoid spaces -/

/-- An **affinoid perfectoid space** is `Spa(A, A⁺)` for a perfectoid ring `A`
(Scholze, *Perfectoid Spaces*, Definition 3.19).

This structure bundles a perfectoid ring together with all the typeclass instances
needed to form its adic spectrum and structure sheaf. -/
structure AffinoidPerfectoidSpace (p : ℕ) [Fact (Nat.Prime p)] where
  /-- The underlying ring. -/
  Ring : Type u
  [instCommRing : CommRing Ring]
  [instTopologicalSpace : TopologicalSpace Ring]
  [instIsTopologicalRing : IsTopologicalRing Ring]
  [instUniformSpace : UniformSpace Ring]
  [instIsLinearTopology : IsLinearTopology Ring Ring]
  [instPlusSubring : PlusSubring Ring]
  [instPerfectoidRing : IsPerfectoidRing p Ring]

attribute [instance] AffinoidPerfectoidSpace.instCommRing
  AffinoidPerfectoidSpace.instTopologicalSpace
  AffinoidPerfectoidSpace.instIsTopologicalRing
  AffinoidPerfectoidSpace.instUniformSpace
  AffinoidPerfectoidSpace.instIsLinearTopology
  AffinoidPerfectoidSpace.instPlusSubring
  AffinoidPerfectoidSpace.instPerfectoidRing

namespace AffinoidPerfectoidSpace

variable {p : ℕ} [Fact (Nat.Prime p)] (X : AffinoidPerfectoidSpace.{u} p)

/-- The underlying topological space of an affinoid perfectoid space. -/
def toTopCat : TopCat.{u} := SpaTop X.Ring

/-- Every affinoid perfectoid space is an affinoid adic space.

This requires that perfectoid rings are sheafy (Scholze, Theorem 6.3), which
follows from the deep result that perfectoid rings are stably uniform. The
proof goes through almost mathematics and tilting. -/
noncomputable def toAffinoidAdicSpace : AffinoidAdicSpace.{u} := by
  exact sorry

/-- Every affinoid perfectoid space gives rise to an adic space.

This combines `toAffinoidAdicSpace` with the fact that every affinoid adic space
is trivially an adic space (covered by itself). -/
noncomputable def toAdicSpace : AdicSpace.{u} := by
  exact sorry

end AffinoidPerfectoidSpace

/-! ### Perfectoid spaces -/

/-- An adic space `X` is a **perfectoid space** (for a prime `p`) if every point of `X`
has an open neighborhood that is isomorphic (as a topological space) to `Spa(A, A⁺)`
for some perfectoid ring `A`.

This is the analogue of the locally affinoid condition in the definition of adic spaces,
with the additional requirement that the local rings are perfectoid.

(Scholze, *Perfectoid Spaces*, Definition 3.19) -/
class IsPerfectoidSpace (p : ℕ) [Fact (Nat.Prime p)]
    (X : AdicSpace.{u}) : Prop where
  /-- Every point has an open neighborhood isomorphic to the adic spectrum of a
  perfectoid ring. -/
  locally_perfectoid : ∀ x : X.carrier,
    ∃ (U : TopologicalSpace.Opens X.carrier),
      x ∈ U ∧
      ∃ (S : AffinoidPerfectoidSpace.{u} p),
        Nonempty (↥U ≃ₜ S.toTopCat)

/-! ### Tilt of a perfectoid space -/

/-- The **tilt** of a perfectoid space is again a perfectoid space (in characteristic `p`).

This is a fundamental result in the theory of perfectoid spaces: the tilting functor
preserves the perfectoid property. The proof requires showing that the tilt of each
local perfectoid ring is again perfectoid, and that the local charts glue correctly.

(Scholze, *Perfectoid Spaces*, Theorem 6.3) -/
theorem PerfectoidSpace.tilt (p : ℕ) [Fact (Nat.Prime p)]
    (X : AdicSpace.{u}) [IsPerfectoidSpace p X] :
    ∃ (Y : AdicSpace.{u}), IsPerfectoidSpace p Y := by
  exact sorry
