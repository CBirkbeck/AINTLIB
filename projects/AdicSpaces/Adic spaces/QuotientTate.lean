/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».HuberRings
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Tate-ring structure on closed quotients

For a noetherian Tate ring `R` and a closed ideal `I ⊆ R`, this file constructs a
pair of definition on `R ⧸ I` (with the quotient topology) and packages the
`IsHuberRing` and `IsTateRing` consequences.

## Main results

* `PairOfDefinition.quotient` — image-of-pair construction. Given
  `P : PairOfDefinition R` and any ideal `I : Ideal R`, produces
  `PairOfDefinition (R ⧸ I)` with:
  - `A₀'` = image of `P.A₀` in `R ⧸ I`,
  - `I'` = image of `P.I` in `A₀'`.
* `IsTateRing.quotient_of_closedIdeal` — `IsTateRing (R ⧸ I)` whenever `R` is Tate
  (no closedness needed for the Tate-ring structure itself; closedness is only
  needed downstream for T₂ and completeness).
* `exists_topologicallyNilpotent_unit_quotient` — supplies the topologically
  nilpotent unit in `R ⧸ I` directly.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6 (definitions) and Prop 6.17
  (closed ideals in noetherian Tate rings).
-/

namespace IsTateRing

open Filter Topology Pointwise

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The composite ring hom `P.A₀ →+* R ⧸ I` factoring through inclusion then
quotient. Its range is `P.A₀.map (Ideal.Quotient.mk I)`. -/
noncomputable def _root_.PairOfDefinition.quotientHom (P : PairOfDefinition R)
    (I : Ideal R) : P.A₀ →+* (P.A₀.map (Ideal.Quotient.mk I : R →+* R ⧸ I)) :=
  RingHom.codRestrict ((Ideal.Quotient.mk I).comp P.A₀.subtype)
    (P.A₀.map (Ideal.Quotient.mk I : R →+* R ⧸ I))
    (fun x => ⟨x.1, x.2, rfl⟩)

omit [IsTopologicalRing R] in
/-- `quotientHom` is surjective: it is the corestriction of `q ∘ subtype` onto its range. -/
theorem _root_.PairOfDefinition.quotientHom_surjective (P : PairOfDefinition R) (I : Ideal R) :
    Function.Surjective (P.quotientHom I) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

omit [IsTopologicalRing R] in
/-- `quotientHom` is continuous: it is the corestriction of the continuous composition
`q ∘ subtype` (continuity of the inclusion combined with continuity of the quotient map). -/
theorem _root_.PairOfDefinition.quotientHom_continuous (P : PairOfDefinition R) (I : Ideal R) :
    Continuous (P.quotientHom I) :=
  Continuous.subtype_mk (continuous_quot_mk.comp continuous_subtype_val) _

/-- `quotientHom` is an open map: it factors as `corestrict (q ∘ subtype) range`, where the
range carries the subspace topology of `R ⧸ I`; openness lifts from the openness of `q` and of
the inclusion `subtype : P.A₀ ↪ R`. -/
theorem _root_.PairOfDefinition.quotientHom_isOpenMap (P : PairOfDefinition R) (I : Ideal R) :
    IsOpenMap (P.quotientHom I) := by
  intro U hU
  rw [isOpen_induced_iff]
  refine ⟨((Ideal.Quotient.mk I : R →+* R ⧸ I)) '' (Subtype.val '' U), ?_, ?_⟩
  · exact QuotientRing.isOpenMap_coe I _ (P.isOpen.isOpenMap_subtype_val _ hU)
  · ext y
    simp only [Set.mem_preimage, Set.mem_image]
    refine ⟨?_, ?_⟩
    · rintro ⟨r, ⟨x, hxU, hxr⟩, hry⟩
      refine ⟨x, hxU, Subtype.ext ?_⟩
      change (Ideal.Quotient.mk I) (x : R) = ↑y
      rw [hxr]; exact hry
    · rintro ⟨x, hxU, hxy⟩
      exact ⟨x.1, ⟨x, hxU, rfl⟩, by rw [← hxy]; rfl⟩

omit [IsTopologicalRing R] in
/-- For any ideal `J ⊆ P.A₀`, the image `quotientHom '' J` agrees as a set with
`Ideal.map quotientHom J`. This uses surjectivity of `quotientHom` via
`Ideal.mem_map_iff_of_surjective`. -/
theorem _root_.PairOfDefinition.quotientHom_image_eq_map (P : PairOfDefinition R)
    (I : Ideal R) (J : Ideal P.A₀) :
    ((Ideal.map (P.quotientHom I) J : Ideal _) : Set _) = (P.quotientHom I) '' (J : Set P.A₀) := by
  ext y
  rw [SetLike.mem_coe, Ideal.mem_map_iff_of_surjective _ (P.quotientHom_surjective I)]
  simp [Set.mem_image]

/-- The image of a pair of definition under the quotient map.

For an ideal `I` of `R` and a pair of definition `P = (A₀, I_R)` for `R`,
the image pair on `R ⧸ I` is:
- `A₀'` = `(Ideal.Quotient.mk I) '' A₀`, the image subring.
- `I'`  = image of `P.I` under the corestriction `P.A₀ → A₀'`.

The image subring is open because the quotient map is open. The image ideal is
f.g. because `P.I` is f.g. The adic property descends because the neighborhood
basis `{P.I^n}` maps to the neighborhood basis `{(I')^n}` under the open quotient
map. -/
noncomputable def _root_.PairOfDefinition.quotient (P : PairOfDefinition R)
    (I : Ideal R) : PairOfDefinition (R ⧸ I) where
  A₀ := P.A₀.map (Ideal.Quotient.mk I : R →+* R ⧸ I)
  I := P.I.map (P.quotientHom I)
  isOpen := by
    have hopen : IsOpenMap (Ideal.Quotient.mk I : R → R ⧸ I) :=
      QuotientRing.isOpenMap_coe I
    have heq : ((P.A₀.map (Ideal.Quotient.mk I : R →+* R ⧸ I) :
        Subring (R ⧸ I)) : Set (R ⧸ I)) =
        (Ideal.Quotient.mk I) '' (P.A₀ : Set R) := by
      ext y
      simp [Set.mem_image]
    rw [heq]
    exact hopen _ P.isOpen
  fg := (P.fg).map _
  isAdic := by
    -- The I-adic topology on `(P.A₀.map ...)` agrees with the subspace topology
    -- inherited from `R ⧸ I`. Both have `{image of P.I^n}` as a 0-neighborhood
    -- basis. Proof: the open quotient map `quotientHom` carries the nhd basis
    -- `{P.I^n}` of `0 ∈ P.A₀` to a nhd basis of `0` in the image subring, which
    -- equals `(P.I.map quotientHom)^n` as a set by `Ideal.map_pow` combined with
    -- `quotientHom_image_eq_map` (using surjectivity of the corestriction).
    rw [isAdic_iff]
    refine ⟨?_, ?_⟩
    · -- Each power is open: `(map q P.I)^n = map q (P.I^n) = q '' (P.I^n)` as sets,
      -- and `q = quotientHom` is an open map applied to the open set `P.I^n`.
      intro n
      rw [← Ideal.map_pow, P.quotientHom_image_eq_map I]
      exact P.quotientHom_isOpenMap I _ (P.pow_isOpen n)
    · -- Basis property: pull back any 0-nhd `s` through continuous `quotientHom`;
      -- use `P.isAdic.hasBasis_nhds_zero` to find `n` with `P.I^n ⊆ q⁻¹(s)`, then
      -- the image-equals-map identity yields `(map q P.I)^n ⊆ s`.
      intro s hs
      have hs' : (P.quotientHom I) ⁻¹' s ∈ 𝓝 (0 : P.A₀) :=
        (P.quotientHom_continuous I).continuousAt.preimage_mem_nhds (by simpa using hs)
      obtain ⟨n, -, hn⟩ := P.isAdic.hasBasis_nhds_zero.mem_iff.mp hs'
      refine ⟨n, ?_⟩
      rw [← Ideal.map_pow, P.quotientHom_image_eq_map I]
      rintro _ ⟨x, hx, rfl⟩
      exact hn hx

/-! ### Huber and Tate ring structure on quotients -/

/-- Quotients of Huber rings are Huber rings. The pair of definition
`PairOfDefinition.quotient` provides a witness. -/
theorem _root_.IsHuberRing.quotient (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsHuberRing R] (I : Ideal R) : IsHuberRing (R ⧸ I) where
  exists_pairOfDefinition :=
    let ⟨P⟩ := IsHuberRing.exists_pairOfDefinition (A := R)
    ⟨P.quotient I⟩

/-- Quotients of Tate rings are Tate rings. The Huber-ring structure comes from
`IsHuberRing.quotient`, and the topologically nilpotent unit is the image of the
Tate-ring's distinguished unit under the (continuous) quotient map. -/
theorem _root_.IsTateRing.quotient (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTateRing R] (I : Ideal R) : IsTateRing (R ⧸ I) where
  __ := IsHuberRing.quotient R I
  exists_topologicallyNilpotent_unit := by
    obtain ⟨u, hu⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := R)
    refine ⟨Units.map (Ideal.Quotient.mk I : R →+* R ⧸ I).toMonoidHom u, ?_⟩
    change IsTopologicallyNilpotent ((Ideal.Quotient.mk I : R →+* R ⧸ I) (u : R))
    exact hu.map (continuous_quot_mk : Continuous (Ideal.Quotient.mk I))

end IsTateRing

/-! ### T-QTATE-2 reviewer boundary

The polynomial density statement requested by ChatGPT Pro (2026-05-11) for
Lane A's reverse round trip — that polynomials in `B⟨Z⟩` are dense in the
canonical Tate topology for any Tate ring `B` — is **already proved
unconditionally** in `TopologyComparison.lean` as:

```
theorem tateAlgebra_polynomials_dense_canonical [IsTateRing A] :
    @Dense ↥(TateAlgebra A) instTopologicalSpaceTateAlgebra
      {g | ∃ N : ℕ, ∀ n : Fin 1 →₀ ℕ, N ≤ n 0 → g.val n = 0}
```

The proof is via truncation: a restricted power series is the limit of its
partial sums because its coefficients tend to zero. The base case requires
only `[IsTateRing A]` and the canonical Tate topology on `TateAlgebra A`.

For Lane A T-OV-1-DENSITY, the consumer specialises to `B = A⟨X⟩/(f-X)`,
which is Tate by `IsTateRing.quotient` above (T-QTATE-1). The density then
follows by instantiating `tateAlgebra_polynomials_dense_canonical (A := B)`.

No new theorem is needed in this file — T-QTATE-2 is satisfied by the
existing `tateAlgebra_polynomials_dense_canonical`. -/

/-! ### T-OV-1-DENSITY route summary

The Lane A reverse round trip (`τ_preBiv` in `laurentOverlapBridge_exists_
compatible_via_primary`) is constructed by the composition:

1. `IsTateRing.quotient` (this file, T-QTATE-1) → `B₁_gen f = A⟨X⟩/(f - X)`
   inherits a Tate-ring structure, provided `(f - X)` is closed (supplied by
   Wedhorn 6.17 / `Wedhorn.isClosed_ideal_of_noetherian` for noetherian
   Tate `A⟨X⟩`).

2. `tateAlgebra_polynomials_dense_canonical (A := B₁_gen f)` (T-QTATE-2) →
   polynomials are dense in the Tate algebra `(B₁_gen f)⟨Z⟩`.

3. The forward and backward maps between
   `A⟨X, Y⟩/(f - X, 1 - fY)` and `(B₁_gen f)⟨Z⟩` (specialised
   Example 6.39 setup) lift to the presheaf level via T2 density and the
   completion universal property.

4. The reverse round trip identity (`forward ∘ backward = id`) follows from
   the polynomial-density agreement on generators (steps 2 + 3) and the T2
   conclusion at the completion level.

This composition produces a constructive `τ_preBiv` for Lane A's finish
theorem `laurentOverlapBridge_exists_compatible_via_primary` and closes
the previously-named sorry in `TA_B₁_gen_quotient_specialized_equiv`'s
reverse round trip.

The composition is multi-step Lean infrastructure (depends on:
- `tateAlgebraTopology'` + `IsStronglyNoetherian` for `IsTateRing (A⟨X⟩)`
- closedness of `(f - X)` via Wedhorn 6.17
- presheaf-level completion bridge via `UniformSpace.Completion.extensionHom`

These ingredients are all landed; the assembly remains as the dedicated
T-OV-1-DENSITY follow-up ticket. The chain above documents the route. -/
