import Mathlib.RingTheory.Grassmannian
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Affine charts of the Grassmannian functor ([NISOG-GRASS], wave 1)

The chart algebra for representing `Module.Grassmannian.functor` by a scheme, following
mathlib's own TODO ladder in `RingTheory/Grassmannian.lean` (*"Define `chart x` indexed
by `x : Fin k → M` … the composition `R^k → M → M⧸N` is an isomorphism"*) and Stacks
089T (Lemma 27.22.1, the chart-subfunctor route):

* `Module.Grassmannian.IsChartAt x N` — the chart predicate at a tuple `x : Fin k → M`;
* `chartEquivRetraction` — chart members are exactly the retractions `φ` of `x`
  (`N = ker φ`), the coordinate-free form of Stacks' "F_i ≅ S ↦ Γ(S, O_S^{k(n−k)})";
* `isChartAt_map` — base change (mathlib's `Grassmannian.map`) preserves charts;
* `retractionEquivMatrix` — over `M = Fin n → R` with `x` a coordinate sub-basis, the
  retraction space is the matrix space of the complementary block.

Consumer: KM 6.5.1's ambient space for `[N-Isog]` (`exists_nIsogSpace`,
`GroupScheme/NIsogeny.lean`, gate [NISOG-GRASS]).

Decomposition artifact: `.mathlib-quality/decomposition-nisog-grass.md` ([STREAM-FP],
fable-FP). Waves 2–3 (chart functors, covering, gluing, T-points) are boarded there.
-/

universe u v

namespace Module.Grassmannian

open Module

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

/-- The linear map `(Fin k → R) →ₗ[R] M` sending coordinates to their combination along
a tuple `x` — the "matrix whose columns are `x`". Private-ish seam isolating the
`Fintype.linearCombination` spelling ([GR-A0] attack 3). -/
noncomputable def coordMap (x : Fin k → M) : (Fin k → R) →ₗ[R] M :=
  Fintype.linearCombination R x

@[simp] lemma coordMap_single (x : Fin k → M) (i : Fin k) :
    coordMap x (Pi.single i (1 : R)) = x i := by
  simp [coordMap]

/-- **[GR-A0]** The chart predicate: `N` lies in the chart at `x : Fin k → M` when the
composite `(Fin k → R) → M → M ⧸ N` is bijective — the images of `x` form a basis of the
quotient (mathlib TODO: *"the composition `R^k → M → M⧸N` is an isomorphism"*). -/
def IsChartAt (x : Fin k → M) (N : G(k, M; R)) : Prop :=
  Function.Bijective (N.toSubmodule.mkQ ∘ₗ coordMap x)

/-- **[GR-A1]** A chart member at `x` is the same data as a retraction of `x`: a linear
`φ : M → (Fin k → R)` with `φ (x i) = eᵢ`, via `N = ker φ` (Stacks 089T step (3), the
coordinate-free form). -/
noncomputable def chartEquivRetraction (x : Fin k → M) :
    {N : G(k, M; R) // IsChartAt x N} ≃
      {φ : M →ₗ[R] (Fin k → R) // ∀ i, φ (x i) = Pi.single i 1} := by
  sorry

/-- **[GR-B]** Over `M = Fin n → R` with chart tuple a coordinate sub-basis (an
embedding `ι : Fin k ↪ Fin n`), a retraction is freely determined by its values on the
complementary coordinates — the chart is a matrix space (Stacks 089T step (3)). -/
noncomputable def retractionEquivMatrix (n : ℕ) (ι : Fin k ↪ Fin n) :
    {φ : (Fin n → R) →ₗ[R] (Fin k → R) //
        ∀ i, φ (Pi.single (ι i) 1) = Pi.single i 1} ≃
      ({j : Fin n // j ∉ Set.range ι} → (Fin k → R)) := by
  sorry

section BaseChange

open TensorProduct

universe w

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- **[GR-A2]** Base change preserves charts: if `N` lies in the chart at
`1 ⊗ₜ x` over `A`, then `Grassmannian.map f` of `N` lies in the chart at `1 ⊗ₜ x` over
`B` (Stacks 089T step (4), base-change stability of the subfunctors). -/
theorem isChartAt_map (x : Fin k → M) (f : A →ₐ[R] B)
    (N : G(k, A ⊗[R] M; A)) (h : IsChartAt (fun i => (1 : A) ⊗ₜ[R] x i) N) :
    IsChartAt (fun i => (1 : B) ⊗ₜ[R] x i) (N.map f) := by
  sorry

end BaseChange

end Module.Grassmannian
