module

public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionEigen
public import BernoulliRegular.Reflection.SingularKummer.FiniteGroupComparison

/-!
# Singular Kummer: elementary quotient components

This file defines the elementary quotient

```text
  V = A / pA
```

for an additive abelian group `A`, equips it with its natural `ZMod p`-module
structure, and transports a `Delta = (ZMod p)ˣ` action on `A` to a linear
action on `V`.

The `i`-th component of `V` is the range of the same character projection used
elsewhere in the singular-Kummer argument.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace ElementaryQuotientComponent

variable {p : ℕ}
variable {A : Type*} [AddCommGroup A]

/-- The elementary quotient `V = A / pA`. -/
abbrev ElementaryQuotient (A : Type*) [AddCommGroup A] (p : ℕ) : Type _ :=
  elementaryQuotient A p

/-- The quotient map `A -> A / pA`. -/
def quotientMap (A : Type*) [AddCommGroup A] (p : ℕ) :
    A →+ ElementaryQuotient A p :=
  QuotientAddGroup.mk' (multiplesSubgroup A p)

@[simp]
theorem quotientMap_apply (p : ℕ) (x : A) :
    quotientMap A p x = (QuotientAddGroup.mk x : ElementaryQuotient A p) :=
  rfl

/-- The quotient map `A -> A / pA` is surjective. -/
theorem quotientMap_surjective (p : ℕ) :
    Function.Surjective (quotientMap A p) := by
  simpa [quotientMap, ElementaryQuotient] using
    QuotientAddGroup.mk'_surjective (multiplesSubgroup A p)

/-- The quotient `A / pA` is naturally a `ZMod p`-module. -/
instance instModuleZModElementaryQuotient :
    Module (ZMod p) (ElementaryQuotient A p) :=
  QuotientAddGroup.zmodModule (n := p) (H := multiplesSubgroup A p) (by
    intro x
    exact ⟨x, rfl⟩)

/-- An additive equivalence of `A` preserves the subgroup `pA`. -/
theorem multiplesSubgroup_le_comap_addEquiv
    (p : ℕ) (e : A ≃+ A) :
    multiplesSubgroup A p ≤
      (multiplesSubgroup A p).comap e.toAddMonoidHom := by
  rintro x ⟨y, rfl⟩
  change e (p • y) ∈ multiplesSubgroup A p
  rw [map_nsmul]
  exact ⟨e y, rfl⟩

/-- An additive equivalence of `A` induces an additive equivalence of
`A / pA`. -/
def quotientAddEquiv (p : ℕ) (e : A ≃+ A) :
    ElementaryQuotient A p ≃+
      ElementaryQuotient A p where
  toFun :=
    QuotientAddGroup.map (multiplesSubgroup A p) (multiplesSubgroup A p)
      e.toAddMonoidHom (multiplesSubgroup_le_comap_addEquiv p e)
  invFun :=
    QuotientAddGroup.map (multiplesSubgroup A p) (multiplesSubgroup A p)
      e.symm.toAddMonoidHom (multiplesSubgroup_le_comap_addEquiv p e.symm)
  left_inv := by
    intro x
    induction x using QuotientAddGroup.induction_on
    simp [QuotientAddGroup.map_mk]
  right_inv := by
    intro x
    induction x using QuotientAddGroup.induction_on
    simp [QuotientAddGroup.map_mk]
  map_add' := fun x y =>
    map_add _ x y

@[simp]
theorem quotientAddEquiv_mk (p : ℕ) (e : A ≃+ A) (x : A) :
    quotientAddEquiv p e
        (QuotientAddGroup.mk x : ElementaryQuotient A p) =
      QuotientAddGroup.mk (e x) :=
  rfl

/-- An additive equivalence of `A` induces a `ZMod p`-linear equivalence of
`A / pA`. -/
def quotientLinearEquiv (p : ℕ) (e : A ≃+ A) :
    ElementaryQuotient A p ≃ₗ[ZMod p]
      ElementaryQuotient A p :=
  { (quotientAddEquiv p e).toAddMonoidHom.toZModLinearMap p with
    invFun := quotientAddEquiv p e.symm
    left_inv := (quotientAddEquiv p e).left_inv
    right_inv := (quotientAddEquiv p e).right_inv }

@[simp]
theorem quotientLinearEquiv_mk (p : ℕ) (e : A ≃+ A) (x : A) :
    quotientLinearEquiv p e
        (QuotientAddGroup.mk x : ElementaryQuotient A p) =
      QuotientAddGroup.mk (e x) :=
  rfl

@[simp]
theorem quotientLinearEquiv_quotientMap (p : ℕ) (e : A ≃+ A) (x : A) :
    quotientLinearEquiv p e (quotientMap A p x) =
      quotientMap A p (e x) :=
  rfl

@[simp]
theorem zmod_smul_eq_val_nsmul [NeZero p]
    (a : ZMod p) (x : ElementaryQuotient A p) :
    a • x = a.val • x := by
  calc
    a • x = (a.val : ZMod p) • x := by
      rw [ZMod.natCast_zmod_val a]
    _ = a.val • x := Nat.cast_smul_eq_nsmul (ZMod p) a.val x

/-- A `Delta` action on `A` induces a linear `Delta` action on `V = A / pA`. -/
def elementaryQuotientAction [NeZero p]
    (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    CharacterProjection.Delta p →*
      ElementaryQuotient A p ≃ₗ[ZMod p] ElementaryQuotient A p where
  toFun d := quotientLinearEquiv p (Multiplicative.toAdd (ρ d))
  map_one' := by
    ext x
    induction x using QuotientAddGroup.induction_on
    simp [quotientLinearEquiv]
  map_mul' a b := by
    ext x
    induction x using QuotientAddGroup.induction_on
    simp [quotientLinearEquiv, map_mul]

/-- The induced `Delta` action on `A / pA` is the quotient of the action on
`A`. -/
@[simp]
theorem elementaryQuotientAction_quotientMap [NeZero p]
    (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (d : CharacterProjection.Delta p) (x : A) :
    elementaryQuotientAction (p := p) ρ d (quotientMap A p x) =
      quotientMap A p ((Multiplicative.toAdd (ρ d)) x) :=
  rfl

@[simp]
theorem elementaryQuotientAction_mk [NeZero p]
    (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (d : CharacterProjection.Delta p) (x : A) :
    elementaryQuotientAction (p := p) ρ d
        (QuotientAddGroup.mk x : ElementaryQuotient A p) =
      QuotientAddGroup.mk ((Multiplicative.toAdd (ρ d)) x) :=
  rfl

/-- The character projection acting on the elementary quotient `V = A / pA`. -/
abbrev elementaryProjection [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    ElementaryQuotient A p →ₗ[ZMod p] ElementaryQuotient A p :=
  CharacterProjection.characterProjection (p := p) i
    (elementaryQuotientAction (p := p) ρ)

/-- The `i`-th component of `V = A / pA`. -/
abbrev elementaryComponent [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    Submodule (ZMod p) (ElementaryQuotient A p) :=
  LinearMap.range (elementaryProjection (p := p) i ρ)

theorem elementaryComponent_eq_range_projection [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    elementaryComponent (p := p) i ρ =
      LinearMap.range (elementaryProjection (p := p) i ρ) :=
  rfl

theorem mem_elementaryComponent_iff_exists [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    {x : ElementaryQuotient A p} :
    x ∈ elementaryComponent (p := p) i ρ ↔
      ∃ y : ElementaryQuotient A p,
        elementaryProjection (p := p) i ρ y = x :=
  Iff.rfl

/-- Nontriviality of the `i`-th component of `V = A / pA`. -/
def ElementaryComponentNontrivial [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) : Prop :=
  elementaryComponent (p := p) i ρ ≠ ⊥

theorem exists_ne_zero_mem_elementaryComponent [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    (h : ElementaryComponentNontrivial (p := p) i ρ) :
    ∃ x : ElementaryQuotient A p,
      x ≠ 0 ∧ x ∈ elementaryComponent (p := p) i ρ := by
  obtain ⟨x, hxmem, hxne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨x, hxne, hxmem⟩

theorem elementaryComponentNontrivial_of_exists_ne_zero_mem [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    (h : ∃ x : ElementaryQuotient A p,
      x ≠ 0 ∧ x ∈ elementaryComponent (p := p) i ρ) :
    ElementaryComponentNontrivial (p := p) i ρ := by
  obtain ⟨x, hxne, hxmem⟩ := h
  rw [ElementaryComponentNontrivial]
  exact (Submodule.ne_bot_iff _).2 ⟨x, hxmem, hxne⟩

theorem elementaryComponentNontrivial_iff_exists_ne_zero_mem [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    ElementaryComponentNontrivial (p := p) i ρ ↔
      ∃ x : ElementaryQuotient A p,
        x ≠ 0 ∧ x ∈ elementaryComponent (p := p) i ρ :=
  ⟨exists_ne_zero_mem_elementaryComponent,
    elementaryComponentNontrivial_of_exists_ne_zero_mem⟩

end ElementaryQuotientComponent

end SingularKummer
end Reflection
end BernoulliRegular

end

end
