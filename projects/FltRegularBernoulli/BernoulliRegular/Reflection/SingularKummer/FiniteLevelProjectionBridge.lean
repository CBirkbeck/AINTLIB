module

public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionIdempotent
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.Torsion

/-!
# Singular Kummer: finite-level bridge from `V_i` to `A[p]_i`

This file isolates the exact finite-level input needed for Lemma 2.1 of
`kummer_reflection.tex`.

Let `B` be a finite additive subgroup of `A`.  If the natural map

```text
  B / pB -> A / pA
```

contains the projected component `V_i`, and if `B[p]` maps into the projected
component of `A[p]`, then nontriviality of `V_i` implies nontriviality of the
matching component of `A[p]`.

The remaining mathematical construction is to take `B` to be the exact
finite-level character component, obtained from the `p`-adic idempotent acting
on the finite group `A`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelProjectionBridge

open ElementaryQuotientComponent
open ProjectedSubgroupComparison
open TorsionComponent

variable {p : ℕ}
variable {A : Type*} [AddCommGroup A]

/-- The inclusion `B <= A` induces a map `B / pB -> A / pA`. -/
def subgroupElementaryQuotientMap (B : AddSubgroup A) (p : ℕ) :
    ElementaryQuotient B p →+ ElementaryQuotient A p :=
  QuotientAddGroup.map (multiplesSubgroup B p) (multiplesSubgroup A p)
    B.subtype (by
      rintro x ⟨y, rfl⟩
      change (p • (y : B) : A) ∈ multiplesSubgroup A p
      exact ⟨(y : A), rfl⟩)

@[simp]
theorem subgroupElementaryQuotientMap_mk
    (B : AddSubgroup A) (p : ℕ) (x : B) :
    subgroupElementaryQuotientMap B p
        (QuotientAddGroup.mk x : ElementaryQuotient B p) =
      (QuotientAddGroup.mk (x : A) : ElementaryQuotient A p) :=
  rfl

/-- The inclusion `B <= A` induces a `ZMod p`-linear map `B / pB -> A / pA`. -/
def subgroupElementaryQuotientLinearMap [NeZero p]
    (B : AddSubgroup A) :
    ElementaryQuotient B p →ₗ[ZMod p] ElementaryQuotient A p :=
  (subgroupElementaryQuotientMap B p).toZModLinearMap p

@[simp]
theorem subgroupElementaryQuotientLinearMap_mk [NeZero p]
    (B : AddSubgroup A) (x : B) :
    subgroupElementaryQuotientLinearMap (p := p) B
        (QuotientAddGroup.mk x : ElementaryQuotient B p) =
      (QuotientAddGroup.mk (x : A) : ElementaryQuotient A p) :=
  rfl

theorem nsmul_elementaryQuotient_eq_zmod_smul [NeZero p]
    (n : ℕ) (x : ElementaryQuotient A p) :
    n • x = (n : ZMod p) • x := by
  rw [ElementaryQuotientComponent.zmod_smul_eq_val_nsmul, ZMod.val_natCast]
  have hpx : p • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x]
    simp
  exact nsmul_eq_mod_nsmul n hpx

theorem quotientMap_nsmul_eq_zmod_smul [NeZero p]
    (n : ℕ) (x : A) :
    quotientMap A p (n • x) = (n : ZMod p) • quotientMap A p x := by
  rw [map_nsmul]
  exact nsmul_elementaryQuotient_eq_zmod_smul (p := p) n
    (quotientMap A p x)

theorem nsmul_ordCompl_mem_primaryComponent
    [Fact p.Prime] [Finite A] (x : A) :
    (ordCompl[p] (addOrderOf x)) • x ∈ AddCommGroup.primaryComponent A p := by
  rw [AddCommGroup.mem_primaryComponent]
  refine ⟨(addOrderOf x).factorization p, ?_⟩
  calc
    p ^ (addOrderOf x).factorization p •
        ((ordCompl[p] (addOrderOf x)) • x)
        = (p ^ (addOrderOf x).factorization p *
            (ordCompl[p] (addOrderOf x))) • x := by
          simpa [Nat.mul_comm] using
            (mul_nsmul x (ordCompl[p] (addOrderOf x))
              (p ^ (addOrderOf x).factorization p)).symm
    _ = addOrderOf x • x := by
          rw [Nat.ordProj_mul_ordCompl_eq_self]
    _ = 0 := addOrderOf_nsmul_eq_zero x

/-- The `p`-primary component of a finite additive group maps onto the
elementary quotient `A / pA`.

For `x : A`, write `q` for the prime-to-`p` part of `addOrderOf x`. Then
`q • x` lies in the `p`-primary component, while `q` is a unit modulo `p`, so
the class of `x` in `A/pA` is a `ZMod p`-multiple of the image of `q • x`. -/
theorem primaryComponent_elementaryQuotientLinearMap_surjective
    [Fact p.Prime] [Finite A] [NeZero p] :
    Function.Surjective
      (subgroupElementaryQuotientLinearMap (p := p)
        (AddCommGroup.primaryComponent A p)) := by
  intro y
  obtain ⟨x, rfl⟩ := quotientMap_surjective (A := A) p y
  let q : ℕ := ordCompl[p] (addOrderOf x)
  have hq_mem :
      q • x ∈ AddCommGroup.primaryComponent A p := by
    simpa [q] using nsmul_ordCompl_mem_primaryComponent (p := p) x
  let z : AddCommGroup.primaryComponent A p := ⟨q • x, hq_mem⟩
  have hx_order_ne : addOrderOf x ≠ 0 :=
    ne_of_gt (addOrderOf_pos x)
  have hq_coprime : q.Coprime p := by
    simpa [q] using (Nat.coprime_ordCompl (Fact.out : Nat.Prime p) hx_order_ne).symm
  have hq_unit : IsUnit (q : ZMod p) :=
    (ZMod.isUnit_iff_coprime q p).2 hq_coprime
  obtain ⟨u, hu⟩ := hq_unit
  refine ⟨(↑u⁻¹ : ZMod p) •
      (QuotientAddGroup.mk z :
        ElementaryQuotient (AddCommGroup.primaryComponent A p) p), ?_⟩
  calc
    subgroupElementaryQuotientLinearMap (p := p)
        (AddCommGroup.primaryComponent A p)
        ((↑u⁻¹ : ZMod p) •
          (QuotientAddGroup.mk z :
            ElementaryQuotient (AddCommGroup.primaryComponent A p) p))
        = (↑u⁻¹ : ZMod p) •
            subgroupElementaryQuotientLinearMap (p := p)
              (AddCommGroup.primaryComponent A p)
              (QuotientAddGroup.mk z :
                ElementaryQuotient (AddCommGroup.primaryComponent A p) p) := by
          rw [map_smul]
    _ = (↑u⁻¹ : ZMod p) • quotientMap A p (q • x) := by
          rfl
    _ = (↑u⁻¹ : ZMod p) • ((q : ZMod p) • quotientMap A p x) := by
          rw [quotientMap_nsmul_eq_zmod_smul]
    _ = ((↑u⁻¹ : ZMod p) * (q : ZMod p)) • quotientMap A p x := by
          rw [mul_smul]
    _ = quotientMap A p x := by
          have huq : (q : ZMod p) = u := hu.symm
          rw [huq]
          simp

/-- If the image of `B / pB` contains the projected component `V_i`, then
nontriviality of `V_i` forces `B / pB` to be nontrivial. -/
theorem elementaryQuotient_nontrivial_of_component_le_subgroup_image
    [NeZero p] (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (B : AddSubgroup A)
    (hV : ElementaryComponentNontrivial (p := p) i ρ)
    (hcover :
      elementaryComponent (p := p) i ρ ≤
        LinearMap.range (subgroupElementaryQuotientLinearMap (p := p) B)) :
    Nontrivial (ElementaryQuotient B p) := by
  obtain ⟨x, hxne, hxmem⟩ :=
    exists_ne_zero_mem_elementaryComponent (p := p) (A := A) hV
  obtain ⟨y, hy⟩ := hcover hxmem
  exact ⟨⟨y, 0, fun hyzero => hxne (by simpa [hyzero] using hy.symm)⟩⟩

/-- Finite-level component comparison.  The hypotheses are precisely the two
facts supplied by an exact finite-level character component `B`: it covers
`V_i` modulo `p`, and its `p`-torsion lies in the corresponding projected
component of `A[p]`. -/
theorem torsionComponentNontrivial_of_finiteLevelSubgroup
    [NeZero p] (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (B : AddSubgroup A) [Finite B]
    (hV : ElementaryComponentNontrivial (p := p) i ρ)
    (hcover :
      elementaryComponent (p := p) i ρ ≤
        LinearMap.range (subgroupElementaryQuotientLinearMap (p := p) B))
    (htorsion :
      ∀ x : torsionBySubgroup B p,
        subgroupTorsionToTorsion B p x ∈ torsionComponent (p := p) i ρ) :
    TorsionComponentNontrivial (p := p) i ρ :=
  torsionComponentNontrivial_of_projectedSubgroup
    (p := p) i ρ B
    (elementaryQuotient_nontrivial_of_component_le_subgroup_image
      (p := p) i ρ B hV hcover)
    htorsion

end FiniteLevelProjectionBridge

end SingularKummer
end Reflection
end BernoulliRegular

end

end
