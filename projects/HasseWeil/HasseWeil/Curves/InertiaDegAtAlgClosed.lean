import HasseWeil.Curves.NormValuation
import HasseWeil.Curves.CurveMap
import Mathlib.RingTheory.Finiteness.Quotient

/-!
# `inertiaDeg = 1` at smooth points over algebraically closed base (Piece 9)

**Status**: Partial. Structural inputs (surjectivity of the residue-field
algebra map, finrank_le_one) delivered. Full `inertiaDeg = 1` closure
blocked on a `Module.Finite (C₂.CR/Q) (C₁.CR/P)` instance-search issue:
mathlib's `module_finite_of_liesOver` instance fires when given a
standard `Algebra A B` instance, but our `coordHom.toAlgebra` is
introduced via `letI` and isn't always findable by the downstream
`inferInstance`. This is a variant of the Module.Free diamond and
documented in the T-II-2-009 Piece 9 progress log.

What's deliverable here without the instance-search fix:
* `residue_algebraMap_surjective_of_isAlgClosed` — the key surjectivity
  lemma (both quotients `≃ F`, induced map is surjective).
* The `finrank_le_one` argument — conditional on `IsScalarTower`.

Full closure waits on either an explicit `[instance]`-attribute version
of `coordHom.toAlgebra` or the `ResidueFieldAtSmoothPoint.lean`
AlgEquiv-transport route (worker A's task #61).
-/

open IsDedekindDomain

namespace HasseWeil.Curves

variable {F : Type*} [Field F]
variable {C₁ C₂ : SmoothPlaneCurve F}

/-- **Residue-field algebra map is surjective under alg-closed base**.

Under `[IsAlgClosed F]`, both `C₂.CR/Q` and `C₁.CR/P` are `≃ F` as
F-algebras (when `Q, P` are maximal). Hence the induced algebra map
between them is surjective, given the scalar tower `F → C₂.CR/Q → C₁.CR/P`.

This is the "hard part" of Piece 9's residue-field computation; combined
with `Module.Finite` on the pair, it gives `inertiaDeg = 1`. -/
theorem residue_algebraMap_surjective_of_isAlgClosed
    [IsAlgClosed F]
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra F A] [Algebra F B] [IsScalarTower F A B]
    (hFA : Function.Bijective (algebraMap F A))
    (hFB : Function.Bijective (algebraMap F B)) :
    Function.Surjective (algebraMap A B) := by
  intro b
  obtain ⟨c, hc⟩ := hFB.2 b
  refine ⟨algebraMap F A c, ?_⟩
  rw [← IsScalarTower.algebraMap_apply F A B c]
  exact hc

/-- **Inertia degree ≤ 1 via surjectivity** (general framework).

Given residue fields both ≃ F (alg-closed) + scalar tower + the
`Module.Finite` instance on the quotient pair, finrank ≤ 1 via
`finrank_le_one` with v = 1. -/
theorem residue_finrank_le_one_of_surjective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [StrongRankCondition A] [Nontrivial B]
    (h_surj : Function.Surjective (algebraMap A B)) :
    Module.finrank A B ≤ 1 :=
  finrank_le_one (1 : B) fun w => by
    obtain ⟨c, hc⟩ := h_surj w
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, hc]
    exact mul_one w

/-! ### Progress note

The full `inertiaDeg = 1` closure (combining the two lemmas above with
`Module.finrank_pos`) requires the `Module.Finite (C₂.CR/Q) (C₁.CR/P)`
instance to fire, which depends on `hfin : Module.Finite C₂.CR C₁.CR`
being registered as a global instance under the standard `Algebra`
structure. Under `letI : Algebra C₂.CR C₁.CR := coordHom.toAlgebra`,
Lean's typeclass search doesn't always find the derived instance.

Workarounds that still hit walls:
* Instance priority (`attribute [instance 10000]`) doesn't help because
  the issue is findability, not ordering.
* Explicit `haveI hfin' : Module.Finite C₂.CR C₁.CR := hfin` fails
  because Lean can't derive `Module C₂.CR C₁.CR` from the letI-
  introduced `Algebra` instance in the same context.

The residue-field AlgEquiv route (worker A's task #61) sidesteps this
by constructing a direct ring isomorphism at each smooth point, then
transporting `inertiaDeg` across it — bypassing the instance search
entirely. Estimated ~100 LOC for that route.
-/

end HasseWeil.Curves
