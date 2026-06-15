import «Adic spaces».ValuationAction
import «Adic spaces».HuberRings

/-!
# Nonarchimedean Scottish Book — Problem 12

**Proposer:** David Hansen
**Date:** 20 December 2015

## Problem Statement

Let A be a Tate ring with a finite group action G. Is Cont(A)/G → Cont(A^G) a
homeomorphism?

## Notes

None.

## Status

RESOLVED: Yes.

## Formalization

We formalize the key definitions and state the main result:

1. **Group action on `Spv(A)`**: Given a `MulSemiringAction G A`, each `g : G` induces a ring
   automorphism `A →+* A`, and contravariantly `Spv(g⁻¹) : Spv(A) → Spv(A)`. This gives a
   `MulAction G (Spv A)` satisfying `(g • v)(a, b) = v(g⁻¹ • a, g⁻¹ • b)`.
   See `ValuationSpectrum.instMulActionSpv` in `ValuationAction.lean`.

2. **Restriction to `Cont(A)` and `Spa(A, A⁺)`**: When the action is by *continuous*
   automorphisms (`ContinuousConstSMul G A`), the action preserves continuity of valuations
   and (with `G`-stable `A⁺`) preserves `Spa` membership.
   See `ValuationSpectrum.smul_mem_cont` and `ValuationSpectrum.smul_mem_spa`.

3. **Natural map**: The inclusion `A^G ↪ A` induces `Spv(ι) : Spv(A) → Spv(A^G)`, which
   restricts to `Cont(A) → Cont(A^G)`. Since elements of `A^G` are fixed by `G`, this map
   is constant on `G`-orbits and descends to `Cont(A)/G → Cont(A^G)`.

4. **Main theorem**: For a Tate ring `A` with finite group `G`, this descended map is a
   homeomorphism. The same holds for the adic spectrum `Spa`.
-/

open ValuationSpectrum

namespace ScottishBook.Problem012

/-! ### The orbit quotient and the natural restriction map -/

section QuotientMap

variable (G : Type*) [Group G] [Finite G]
variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable [MulSemiringAction G A] [ContinuousConstSMul G A]

/-- The orbit quotient `Cont(A) / G`, with the quotient topology. -/
abbrev contQuotient := MulAction.orbitRel.Quotient G ↥(Cont A)

/-- The fixed subring `A^G` under the `G`-action. -/
abbrev fixedSubring := FixedPoints.subring A G

/-- The inclusion `A^G ↪ A` as a ring homomorphism. -/
def fixedSubringInclusion : ↥(fixedSubring G A) →+* A :=
  (fixedSubring G A).subtype

/-- The restriction map lands in `Cont(A^G)`: if `v` is a continuous valuation on `A`, then
its restriction to `A^G` (via the inclusion `A^G ↪ A`) is a continuous valuation on `A^G`. -/
theorem restrictToFixed_mem_cont (v : ↥(Cont A)) :
    (comap (fixedSubringInclusion G A) v.1) ∈ Cont ↥(fixedSubring G A) :=
  comap_isContinuous continuous_subtype_val v.2

/-- The natural map `Cont(A) → Cont(A^G)` induced by restriction to the fixed subring. -/
noncomputable def restrictToCont :
    ↥(Cont A) → ↥(Cont ↥(fixedSubring G A)) :=
  fun v => ⟨comap (fixedSubringInclusion G A) v.1, restrictToFixed_mem_cont G A v⟩

/-- The restriction map is constant on `G`-orbits: for all `g : G` and `v ∈ Cont(A)`, the
valuations `g • v` and `v` agree on `A^G`, since `(g • v)(a) = v(g⁻¹ • a) = v(a)` for
`a ∈ A^G`. -/
theorem restrictToCont_smul_eq (g : G) (v : ↥(Cont A)) :
    restrictToCont G A (g • v) = restrictToCont G A v := by
  apply Subtype.ext
  apply ValuationSpectrum.ext
  funext a₁ a₂
  change (comap (fixedSubringInclusion G A) (g • v.1)).vle a₁ a₂ =
    (comap (fixedSubringInclusion G A) v.1).vle a₁ a₂
  simp only [comap_vle, fixedSubringInclusion, Subring.coe_subtype]
  show (comap (MulSemiringAction.toRingHom G A g⁻¹) v.1).vle (↑a₁) (↑a₂) =
    v.1.vle (↑a₁) (↑a₂)
  simp only [comap_vle, MulSemiringAction.toRingHom_apply, a₁.2 g⁻¹, a₂.2 g⁻¹]

/-- The descended map `Cont(A)/G → Cont(A^G)`, well-defined since the restriction map is
constant on `G`-orbits. -/
noncomputable def quotientToCont :
    contQuotient G A → ↥(Cont ↥(fixedSubring G A)) :=
  Quotient.lift (restrictToCont G A)
    (fun a b ⟨g, hg⟩ => by rw [← hg, restrictToCont_smul_eq])

/-- `quotientToCont` is continuous. -/
theorem continuous_quotientToCont : Continuous (quotientToCont G A) := by
  apply Continuous.quotient_lift
  exact Continuous.subtype_mk
    ((comap_continuous (fixedSubringInclusion G A)).comp continuous_subtype_val) _

end QuotientMap

/-! ### Main theorems -/

section MainTheorem

variable (G : Type*) [Group G] [Finite G]
variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable [MulSemiringAction G A] [ContinuousConstSMul G A]

/-- **Scottish Book Problem 12 (Cont version)** (Hansen, resolved: Yes).

Let `A` be a Tate ring with a finite group `G` acting by continuous ring automorphisms.
Then the natural map `Cont(A)/G → Cont(A^G)` is a homeomorphism, where:
- `Cont(A)` is the space of continuous valuations on `A` (Definition 7.7 of Wedhorn),
- `A^G = FixedPoints.subring A G` is the fixed subring under the `G`-action,
- the quotient `Cont(A)/G` carries the quotient topology from the `G`-orbit equivalence
  relation,
- `Cont(A^G)` is the space of continuous valuations on the fixed subring `A^G`,
  equipped with the subspace topology from `Spv(A^G)`.
-/
theorem contQuotient_homeomorph_contFixed [IsTateRing A] :
    Nonempty (contQuotient G A ≃ₜ ↥(Cont ↥(fixedSubring G A))) := sorry

/-- **Scottish Book Problem 12 (Spa version)** (Hansen, resolved: Yes).

For a Huber pair `(A, A⁺)` with `A⁺` stable under the `G`-action, the natural map
`Spa(A, A⁺)/G → Spa(A^G, (A⁺)^G)` is a homeomorphism, where the fixed plus subring
`(A⁺)^G` is the preimage of `A⁺` under the inclusion `A^G ↪ A`.

The `MulAction G ↥(Spa A A⁺)` instance is constructed from `smul_mem_spa` using the
stability hypothesis. -/
theorem spaQuotient_homeomorph_spaFixed [IsTateRing A] [PlusSubring A]
    (hstab : ∀ (g : G) (a : A), a ∈ A⁺ → g • a ∈ A⁺) :
    ∃ (_ : MulAction G ↥(Spa A A⁺)),
      Nonempty (@MulAction.orbitRel.Quotient G ↥(Spa A A⁺) _ ‹_› ≃ₜ
        ↥(Spa ↥(fixedSubring G A)
          (A⁺.comap (fixedSubringInclusion G A)))) := sorry

end MainTheorem

end ScottishBook.Problem012
