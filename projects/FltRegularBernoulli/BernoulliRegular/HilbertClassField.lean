module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Sylow
public import FltRegular.NumberTheory.Unramified

/-!
# Component-refined unramified degree-`p` extensions

For a number field `L` and a prime `p`, `HilbertPClassField L p` is the data
of the maximal unramified elementary abelian `p`-extension `H_p(L) / L`. Its
central property is the class-field-theory isomorphism

  `Gal(H_p(L) / L) ≃* ClassGroup(𝒪_L) / ClassGroup(𝒪_L)^p`,

where the right-hand side is `Cl(𝒪_L) ⊗_ℤ 𝔽_p`, the quotient of the ideal
class group by its `p`-th powers.

The structures in this file are ordinary explicit data. They do not assert
existence of a Hilbert class field or of component-refined cyclic extensions.

This keeps Kummer generators, pseudo-unit conditions, and Kummer quotient
classes out of the axiom statement; those are downstream consequences to prove
from the extension.

## Main definitions

* `ClassGroupModP L p`: the quotient `Cl(𝒪_L) / Cl(𝒪_L)^p`, i.e.
  `ClassGroup (𝓞 L) ⧸ (powMonoidHom p).range`.
* `HilbertPClassField L p`: the data of the Hilbert `p`-class field of `L`:
  a Galois extension `Hp / L` together with a group isomorphism
  `Gal(Hp / L) ≃* ClassGroupModP L p`.
* `CyclotomicFieldClassGroupPSylowComponent`: the current data-driven stand-in
  for a `Δ`-character component of the `p`-Sylow of `Cl(𝒪_{ℚ(ζ_p)})`.
* `ComponentUnramifiedCyclicDegreePExtension`: the narrow extension package
  produced by the axiom.
This file only contains the component-level data structures.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.
* Diekmann, *FLT for regular primes*, §6.
* Ciurca, §6.4.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open NumberField

/-- The `p`-rank quotient of the class group: `Cl(𝒪_L) / Cl(𝒪_L)^p`,
canonically isomorphic to `Cl(𝒪_L) ⊗_ℤ 𝔽_p` for finite abelian class groups.

This is the target group of the class-field-theory isomorphism for the
Hilbert `p`-class field. -/
abbrev ClassGroupModP (L : Type*) [Field L] [NumberField L] (p : ℕ) : Type _ :=
  ClassGroup (𝓞 L) ⧸ (powMonoidHom p : ClassGroup (𝓞 L) →* _).range

/-- Hilbert `p`-class field data.

The data of an unramified abelian extension `Hp / L` of exponent dividing `p`
whose Galois group realises `ClassGroup(𝒪_L) / ClassGroup(𝒪_L)^p`. This
is stated only as a data-bearing structure; the project axiom no longer
postulates the existence of this full package.

The Galois-equivariance for Galois extensions `L / K` is encoded downstream
by transporting along this isomorphism: pulling back a `Gal(L / K)`-action
along `galEquiv` gives a `Gal(L / K)`-action on `ClassGroupModP L p` that
matches the natural one coming from ideal-class functoriality. We do not
build the equivariance witness here because the downstream callers consume
`galEquiv` directly and do the transport locally. -/
structure HilbertPClassField (L : Type*) [Field L] [NumberField L]
    (p : ℕ) [Fact p.Prime] where
  /-- The Hilbert `p`-class field `H_p(L)` of `L`. -/
  Hp : Type*
  /-- Field structure on `H_p(L)`. -/
  [field : Field Hp]
  /-- `L`-algebra structure on `H_p(L)`. -/
  [algebra : Algebra L Hp]
  /-- `H_p(L) / L` is a Galois extension. -/
  [isGalois : IsGalois L Hp]
  /-- `H_p(L) / L` is finite. -/
  [finiteDimensional : FiniteDimensional L Hp]
  /-- The class-field-theoretic isomorphism
  `Gal(H_p(L) / L) ≃* Cl(𝒪_L) / Cl(𝒪_L)^p`. -/
  galEquiv : (Hp ≃ₐ[L] Hp) ≃* ClassGroupModP L p

namespace HilbertPClassField

variable {L : Type*} [Field L] [NumberField L] {p : ℕ} [Fact p.Prime]

attribute [instance] field algebra isGalois finiteDimensional

end HilbertPClassField

/-- A fixed Sylow `p`-subgroup of the class group of a `p`-th cyclotomic
field model.

This is a data-driven stand-in until the project builds the intrinsic
`ℤ_p[Δ]`-module decomposition of the class group. -/
noncomputable def cyclotomicFieldClassGroupPSylow
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    Sylow p (ClassGroup (𝓞 K)) :=
  default

/-- A character-tagged component of the `p`-Sylow of the class group of
`ℚ(ζ_p)`.

The subgroup is supplied as data because the intrinsic idempotent component
`e_χ A` is not built yet. The axiom below uses this component object only to
record the precise `Δ`-line that must be preserved by the extension. -/
structure CyclotomicFieldClassGroupPSylowComponent
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] where
  character : MulChar (ZMod p)ˣ ℚ
  subgroup : Subgroup (cyclotomicFieldClassGroupPSylow (p := p) K)

namespace CyclotomicFieldClassGroupPSylowComponent

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The underlying type of a declared cyclotomic class-group component. -/
abbrev Carrier (C : CyclotomicFieldClassGroupPSylowComponent (p := p) K) : Type _ :=
  C.subgroup

/-- Nontriviality of a declared cyclotomic class-group component. -/
def Nontrivial (C : CyclotomicFieldClassGroupPSylowComponent (p := p) K) : Prop :=
  ∃ x : C.Carrier, x ≠ 1

end CyclotomicFieldClassGroupPSylowComponent

/-- A narrow component-refined unramified cyclic degree-`p` extension package.

This is intentionally weaker than a full Hilbert `p`-class-field datum. It
contains exactly the extension data needed before the downstream Kummer and
reflection steps:

* an unramified finite Galois extension `E/K`,
* degree `p`,
* cyclic Galois group,
* and explicit bookkeeping that its Galois line corresponds to the requested
  `Δ`-character and class-group component.

The `galLineCharacter` and `artinComponentLine` fields are data placeholders
for the future Artin-reciprocity/naturality construction. They keep the axiom
component-refined without asserting any Kummer generator or pseudo-unit
condition. -/
structure ComponentUnramifiedCyclicDegreePExtension
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (χ : MulChar (ZMod p)ˣ ℚ)
    (C : CyclotomicFieldClassGroupPSylowComponent (p := p) K) where
  E : Type*
  [field : Field E]
  [numberField : NumberField E]
  [algebra : Algebra K E]
  [finiteDimensional : FiniteDimensional K E]
  [isGalois : IsGalois K E]
  [isUnramified : Algebra.Unramified (𝓞 K) (𝓞 E)]
  degree_eq_p : Module.finrank K E = p
  cyclic : IsCyclic (E ≃ₐ[K] E)
  /-- The `Δ`-character of the one-dimensional Galois line. -/
  galLineCharacter : MulChar (ZMod p)ˣ ℚ
  /-- The Galois line has the requested character. -/
  galLineCharacter_eq : galLineCharacter = χ
  /-- The class-group component line selected by Artin reciprocity. -/
  artinComponentLine : Subgroup (cyclotomicFieldClassGroupPSylow (p := p) K)
  /-- The selected Artin line is the requested component. -/
  artinComponentLine_eq : artinComponentLine = C.subgroup

namespace ComponentUnramifiedCyclicDegreePExtension

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {χ : MulChar (ZMod p)ˣ ℚ}
variable {C : CyclotomicFieldClassGroupPSylowComponent (p := p) K}

attribute [instance] field numberField algebra finiteDimensional isGalois isUnramified

end ComponentUnramifiedCyclicDegreePExtension

end BernoulliRegular

end
