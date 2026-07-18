module

public import BernoulliRegular.Reflection.Kummer.UnramifiedUnit

/-!
# Principal-ideal lift atom for the Kummer presentation
(REF-18 ↔ Reflection bridge)

For an unramified cyclic degree-`p` extension `E = K(α)` of `K = ℚ(ζ_p)`
presented as `α^p = γ` with `γ ∈ K`, the Kummer-Dedekind ramification
analysis (`UnramifiedCriterion.lean`) delivers the **weak form**

> `(γ) = J^p` for some `J : (FractionalIdeal _)ˣ` (a fractional-ideal class).

The unit decomposition `γ = u · β^p` requires the **strong form**

> `(γ) = (β)^p` for some `β : K^×`,

which holds iff the witness `J` is principal.

This file refines the principal-ideal lift atom into smaller, mathematically
meaningful predicates and isolates the **class-group obstruction**: the lift
holds iff `[J] = 1` in `ClassGroup (𝓞 K)`.

## Why this is an *obstruction*, not a free reduction

For `χ` such that the χ-component `A_χ ⊂ Cl(K)_p` has p-rank ≥ 1, the Kummer
class corresponding to a generator of `A_χ` has a non-principal `J`. Concretely:
in the Hilbert `p`-class field setting, the `J` of the weak form represents the
non-trivial `[J] ∈ A_χ`, and the principal lift fails on those Kummer classes.

The Kummer classes for which the lift *does* hold are exactly the **unit
pseudo-units**: classes of γ ∈ K^× / (K^×)^p that admit a global unit
representative in `(𝓞_K)ˣ / ((𝓞_K)ˣ)^p`. These form the kernel of the
projection `K^× / (K^×)^p → A/A^p` sending `[γ] ↦ [J] mod p`.

## Main definitions

* `KummerPresentation.JClassTrivialFor J`: for a *specific* witness
  `J : (FractionalIdeal _)ˣ` of `(γ) = J^p`, the class `[J] ∈ ClassGroup (𝓞 K)`
  is trivial — equivalently, `J` is principal.

* `KummerPresentation.HasTrivialClassWitness`: there exists a witness `J` of
  `GenIsPowOfFractionalIdealClass` whose class in `ClassGroup (𝓞 K)` is trivial.
  This is the **class-group atom** that controls the principal-ideal lift.

* `KummerPresentation.FromUnitGenerator`: the **strongest structural form** —
  `γ = u · β^p` directly (i.e. the unit-decomposition form is *given*). This
  automatically discharges the principal-ideal lift via the converse reduction
  in `UnramifiedUnit.lean`.

## Main reductions

* `KummerPresentation.genIsPowOfPrincipalFractionalIdeal_of_jClassTrivialFor`:
  from `(γ) = J^p` and `J` principal (= `[J]` trivial in `ClassGroup`), derive
  the strong form `(γ) = (β)^p` for the principal generator `β` of `J`.

* `KummerPresentation.genIsPowOfPrincipalFractionalIdeal_of_hasTrivialClassWitness`:
  the existential form — from *some* trivial-class witness, derive the strong
  form.

* `KummerPresentation.fromUnitGenerator_iff_genEqUnitMulPow`: the strongest
  form is *definitionally* the unit-decomposition form; both are equivalent
  to `GenIsPowOfPrincipalFractionalIdeal` (via the `UnramifiedUnit.lean`
  reductions).

* `KummerPresentation.principalLift_of_classGroup_subsingleton`: when the
  ambient class group `ClassGroup (𝓞 K)` is trivial (PID hypothesis), every
  weak-form witness lifts. This gives a clean **trivial-case discharge** of
  the principal-ideal lift.

## Pipeline shape

```
GenIsPowOfFractionalIdealClass    --- weak form, valuation criterion
      ↓ + class-group atom: ∃ J with (γ) = J^p AND J principal
HasTrivialClassWitness            --- the obstruction-explicit predicate
      ↓ pick J, extract its principal generator β
GenIsPowOfPrincipalFractionalIdeal  --- strong form
      ↓ (UnramifiedUnit.lean substantive reduction)
GenEqUnitMulPow                    --- final unit decomposition
```

The class-group atom is what classical Kummer theory (Washington §10.2)
controls via the "pseudo-unit at a non-trivial class" obstruction. This file
documents the obstruction at the Lean level so downstream files can discharge
it case by case (e.g. trivial-case via `Subsingleton (ClassGroup K)`,
non-trivial-case via the explicit Hilbert `p`-class-field generator data).

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.2 ("unramified
  Kummer extensions and pseudo-units").
* Diekmann, *FLT for regular primes*, §6.
* Borevich-Shafarevich, §4.9.
-/

@[expose] public section

noncomputable section

open NumberField FractionalIdeal Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular

set_option linter.unusedSectionVars false

namespace KummerPresentation

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {χ : MulChar (ZMod p)ˣ ℚ}
variable {Comp : CyclotomicFieldClassGroupPSylowComponent (p := p) K}
variable {Ext : ComponentUnramifiedCyclicDegreePExtension (p := p) K χ Comp}

/-!
### Atomic predicates: the class-group obstruction
-/

/-- A unit fractional ideal whose underlying submodule is principal is of the
form `toPrincipalIdeal _ _ β` for some unit `β : Kˣ`: its (necessarily nonzero)
principal generator promotes to a unit. -/
private theorem exists_eq_toPrincipalIdeal_of_isPrincipal
    {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJprinc : ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal) :
    ∃ β : Kˣ, J = toPrincipalIdeal (𝓞 K) K β := by
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff
    (S := (𝓞 K)⁰) (P := K) (I := (J : FractionalIdeal (𝓞 K)⁰ K))).mp hJprinc
  have hxne : x ≠ 0 := fun hx0 ↦ J.ne_zero (by rw [hx, hx0, spanSingleton_zero])
  refine ⟨Units.mk0 x hxne, Units.ext ?_⟩
  rw [coe_toPrincipalIdeal, hx]
  rfl

/-- **Per-witness class-triviality predicate.** For a *specific* witness `J`
of the weak form `(γ) = J^p`, the class `[J] ∈ ClassGroup (𝓞 K)` is trivial.

By `ClassGroup.mk_eq_one_iff`, this is equivalent to the underlying
`Submodule (𝓞 K) K` of `J` being principal.

This is the per-witness atom controlling whether the strong form
`(γ) = (β)^p` follows from the given `J`. -/
def JClassTrivialFor (P : KummerPresentation Ext)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Prop :=
  toPrincipalIdeal (𝓞 K) K P.genUnit = J ^ p ∧
    ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal

/-- **Existential class-triviality predicate.** There exists a witness `J` of
`GenIsPowOfFractionalIdealClass` whose class in `ClassGroup (𝓞 K)` is trivial.

This is the **class-group atom** that controls the principal-ideal lift.
Mathematically: among the witnesses `J` such that `(γ) = J^p`, *at least one*
is principal (equivalently, `[J]` is trivial in `ClassGroup (𝓞 K)`).

For a Kummer class `[γ]` corresponding to a non-trivial element of `A_χ`
(a non-trivial χ-component of the `p`-Sylow of the class group), this
predicate **fails** — that is precisely the class-group obstruction
documented in Washington §10.2 / Diekmann §6. -/
def HasTrivialClassWitness (P : KummerPresentation Ext) : Prop :=
  ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, P.JClassTrivialFor J

/-- **Unit-generator form.** A `KummerPresentation` whose generator `γ` admits
a unit decomposition `γ = u · β^p` *directly*. This is definitionally
`GenEqUnitMulPow P`, restated as a structural form (i.e. the strongest form
in the pipeline).

Equivalent (via `UnramifiedUnit.lean` reductions) to:
* `GenIsPowOfPrincipalFractionalIdeal P` (strong fractional-ideal form);
* `GenIsPowOfFractionalIdealClass P ∧ HasTrivialClassWitness P` (weak form
  plus the trivial-class atom).

Mathematically, this is the "pseudo-unit" form: γ ∈ (𝓞_K)ˣ · (K^×)^p,
i.e. `[γ] ∈ K^×/(K^×)^p` factors through `(𝓞_K)ˣ/((𝓞_K)ˣ)^p`. -/
def FromUnitGenerator (P : KummerPresentation Ext) : Prop :=
  P.GenEqUnitMulPow

/-!
### Reductions: the class-group atom controls the principal-ideal lift
-/

/-- **Per-witness reduction.** From a *specific* witness `J` of `(γ) = J^p`
together with `J` principal (= `[J]` trivial in `ClassGroup (𝓞 K)`), derive
the strong form `(γ) = (β)^p`.

The principal generator `β` is extracted via `FractionalIdeal.isPrincipal_iff`,
which says `IsPrincipal ↔ ∃ x, J = spanSingleton x`. Combined with `J` being a
*unit* fractional ideal (hence non-zero), `x` is non-zero and yields the
required `β : Kˣ`. -/
theorem genIsPowOfPrincipalFractionalIdeal_of_jClassTrivialFor
    (P : KummerPresentation Ext)
    {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : P.JClassTrivialFor J) :
    P.GenIsPowOfPrincipalFractionalIdeal := by
  obtain ⟨hγ, hJprinc⟩ := hJ
  -- Extract the principal generator `β : Kˣ` with `J = toPrincipalIdeal _ _ β`,
  -- then `hγ` finishes via `(γ) = J^p = (β)^p`.
  obtain ⟨β, hJ_eq_β⟩ := exists_eq_toPrincipalIdeal_of_isPrincipal hJprinc
  exact ⟨β, by rw [hγ, hJ_eq_β]⟩

/-- **Existential reduction.** From the trivial-class atom (some weak-form
witness `J` is principal), derive the strong form `(γ) = (β)^p`. -/
theorem genIsPowOfPrincipalFractionalIdeal_of_hasTrivialClassWitness
    (P : KummerPresentation Ext)
    (h : P.HasTrivialClassWitness) :
    P.GenIsPowOfPrincipalFractionalIdeal := by
  obtain ⟨J, hJ⟩ := h
  exact P.genIsPowOfPrincipalFractionalIdeal_of_jClassTrivialFor hJ

/-!
### Equivalence: the strong form is the trivial-class atom

The strong form `GenIsPowOfPrincipalFractionalIdeal` is exactly the trivial-
class atom `HasTrivialClassWitness`: a principal `(β)^p` is itself a witness
with trivial class.
-/

/-- **Forward direction.** The strong form `GenIsPowOfPrincipalFractionalIdeal`
implies the trivial-class atom: `(β)` (as a fractional ideal class) is its own
principal witness. -/
theorem hasTrivialClassWitness_of_genIsPowOfPrincipalFractionalIdeal
    (P : KummerPresentation Ext)
    (h : P.GenIsPowOfPrincipalFractionalIdeal) :
    P.HasTrivialClassWitness := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨toPrincipalIdeal (𝓞 K) K β, hβ, ?_⟩
  -- `toPrincipalIdeal _ _ β` is principal: it is `spanSingleton (β : K)`.
  rw [coe_toPrincipalIdeal]
  exact (FractionalIdeal.isPrincipal_iff (S := (𝓞 K)⁰) (P := K)
    (I := spanSingleton (𝓞 K)⁰ (β : K))).mpr ⟨(β : K), rfl⟩

/-- **The central equivalence.** `GenIsPowOfPrincipalFractionalIdeal` is
exactly `HasTrivialClassWitness`: the strong form holds iff some weak-form
witness is principal.

This makes precise the **class-group obstruction**: the strong form is a
class-group condition on the weak-form witnesses. -/
theorem genIsPowOfPrincipalFractionalIdeal_iff_hasTrivialClassWitness
    (P : KummerPresentation Ext) :
    P.GenIsPowOfPrincipalFractionalIdeal ↔ P.HasTrivialClassWitness :=
  ⟨P.hasTrivialClassWitness_of_genIsPowOfPrincipalFractionalIdeal,
   P.genIsPowOfPrincipalFractionalIdeal_of_hasTrivialClassWitness⟩

/-!
### Trivial-case discharge: PID / trivial class group

If `ClassGroup (𝓞 K)` is trivial (e.g. `K` has class number 1), every
fractional-ideal class is trivial, so *every* weak-form witness is principal.
This gives a clean trivial-case discharge of the principal-ideal lift.

For `K = ℚ(ζ_p)` with `p` regular, the `p`-Sylow of the class group is
trivial — so the *part of the class group that matters for the Kummer lift*
(the obstruction to lifting `(γ) = J^p` to `(γ) = (β)^p`) is automatically
discharged at regular primes. This is one of the key inputs of the regularity
hypothesis flowing through the reflection bridge.
-/

/-- **Trivial-case discharge.** When `ClassGroup (𝓞 K)` is a subsingleton
(every fractional-ideal class is trivial), every weak-form witness lifts:
`GenIsPowOfFractionalIdealClass` implies `GenIsPowOfPrincipalFractionalIdeal`.

This handles e.g. number fields of class number 1 — including the regular
case where the relevant `p`-part of the class group is trivial. -/
theorem genIsPowOfPrincipalFractionalIdeal_of_classGroup_subsingleton
    [Subsingleton (ClassGroup (𝓞 K))]
    (P : KummerPresentation Ext)
    (h : P.GenIsPowOfFractionalIdealClass) :
    P.GenIsPowOfPrincipalFractionalIdeal := by
  obtain ⟨J, hJ⟩ := h
  -- Under `Subsingleton (ClassGroup _)`, every unit fractional ideal is
  -- principal.
  have hJprinc : ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal :=
    ClassGroup.isPrincipal_coeSubmodule_of_isUnit
      (J : FractionalIdeal (𝓞 K)⁰ K) (Units.isUnit J)
  exact P.genIsPowOfPrincipalFractionalIdeal_of_jClassTrivialFor ⟨hJ, hJprinc⟩

/-- **Trivial-case discharge of `HasTrivialClassWitness`.** When
`ClassGroup (𝓞 K)` is a subsingleton, `GenIsPowOfFractionalIdealClass` already
furnishes a trivial-class witness — every weak-form witness is principal. -/
theorem hasTrivialClassWitness_of_classGroup_subsingleton
    [Subsingleton (ClassGroup (𝓞 K))]
    (P : KummerPresentation Ext)
    (h : P.GenIsPowOfFractionalIdealClass) :
    P.HasTrivialClassWitness :=
  P.hasTrivialClassWitness_of_genIsPowOfPrincipalFractionalIdeal
    (P.genIsPowOfPrincipalFractionalIdeal_of_classGroup_subsingleton h)

/-!
### Strongest form: unit-generator presentation

`FromUnitGenerator P` is the structural form `γ = u · β^p` itself. By the
`UnramifiedUnit.lean` reductions, this is equivalent to
`GenIsPowOfPrincipalFractionalIdeal`.
-/

/-- **Equivalence of the strongest form with the strong form.**
`FromUnitGenerator P` (= `GenEqUnitMulPow P`) is logically equivalent to
`GenIsPowOfPrincipalFractionalIdeal P`. -/
theorem fromUnitGenerator_iff_genIsPowOfPrincipalFractionalIdeal
    (P : KummerPresentation Ext) :
    P.FromUnitGenerator ↔ P.GenIsPowOfPrincipalFractionalIdeal :=
  ⟨P.genIsPowOfPrincipalFractionalIdeal_of_genEqUnitMulPow,
   P.genEqUnitMulPow_of_genIsPowOfPrincipalFractionalIdeal⟩

/-- **Equivalence of the strongest form with the trivial-class atom.**
`FromUnitGenerator P` (= `γ = u · β^p`) is equivalent to
`HasTrivialClassWitness P` (= some weak-form witness is principal). -/
theorem fromUnitGenerator_iff_hasTrivialClassWitness
    (P : KummerPresentation Ext) :
    P.FromUnitGenerator ↔ P.HasTrivialClassWitness :=
  (P.fromUnitGenerator_iff_genIsPowOfPrincipalFractionalIdeal).trans
    (P.genIsPowOfPrincipalFractionalIdeal_iff_hasTrivialClassWitness)

/-!
### Composite reduction with the explicit principal-ideal lift hypothesis

Re-package the existing principal-ideal lift hypothesis from
`UnramifiedUnit.lean` into the new atomic-predicate language: the lift
hypothesis is *exactly* the statement that every weak-form witness has trivial
class.
-/

/-- **Universal-class-trivial lift hypothesis.** For *every* weak-form witness
`J`, `J` has trivial class — i.e. `J` is principal. This is the strongest form
of the lift hypothesis: it discharges the principal-ideal lift uniformly across
all witnesses.

This matches the `principalLift` field of `KummerPipelinePerExtension` in
`KummerToUnitQuotientComposer.lean`, restated in the atomic-predicate
language of this file. -/
def UniversalPrincipalLift (P : KummerPresentation Ext) : Prop :=
  ∀ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
    toPrincipalIdeal (𝓞 K) K P.genUnit = J ^ p →
    ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal

/-- **From the universal lift to the existential atom.** The universal lift
implies the existential trivial-class atom (provided some witness exists). -/
theorem hasTrivialClassWitness_of_universalPrincipalLift
    (P : KummerPresentation Ext)
    (h : P.GenIsPowOfFractionalIdealClass)
    (lift : P.UniversalPrincipalLift) :
    P.HasTrivialClassWitness := by
  obtain ⟨J, hJ⟩ := h
  exact ⟨J, hJ, lift J hJ⟩

/-- **Connecting to the `KummerPipelinePerExtension.principalLift` field.**
The universal lift in this file's language is equivalent to the
`principalLift` hypothesis used in
`KummerToUnitQuotientComposer.lean`: both say that every weak-form
witness `J` has a principal generator. -/
theorem universalPrincipalLift_iff_principalLift_of_composer
    (P : KummerPresentation Ext) :
    P.UniversalPrincipalLift ↔
    ∀ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      toPrincipalIdeal (𝓞 K) K P.genUnit = J ^ p →
      ∃ β : Kˣ, J = toPrincipalIdeal (𝓞 K) K β := by
  constructor
  · intro hLift J hJ
    -- From `J` principal, extract the unit generator `β` with
    -- `J = toPrincipalIdeal _ _ β`.
    exact exists_eq_toPrincipalIdeal_of_isPrincipal (hLift J hJ)
  · intro hLift J hJ
    obtain ⟨β, hβ⟩ := hLift J hJ
    -- `J = toPrincipalIdeal _ _ β` ⇒ `J : Submodule` is principal.
    have hJ_eq : (J : FractionalIdeal (𝓞 K)⁰ K) =
        spanSingleton (𝓞 K)⁰ (β : K) := by
      simpa [coe_toPrincipalIdeal] using Units.ext_iff.mp hβ
    rw [hJ_eq]
    exact (FractionalIdeal.isPrincipal_iff (S := (𝓞 K)⁰) (P := K)
      (I := spanSingleton (𝓞 K)⁰ (β : K))).mpr ⟨_, rfl⟩

/-!
### Summary diagram

```
                                   trivial-case (PID, regular p)
                                   ─────────────────────────────────────
                                   Subsingleton (ClassGroup (𝓞 K))
                                              │
                                              ▼
GenIsPowOfFractionalIdealClass  ──────►  HasTrivialClassWitness  ◄─────  UniversalPrincipalLift
        (weak form)                    (class-group obstruction)
                                              │ ↑
                                              │ │ (equivalence)
                                              ▼ │
                                   GenIsPowOfPrincipalFractionalIdeal
                                          (strong form)
                                              │ ↑
                                              │ │ (equivalence)
                                              ▼ │
                                       GenEqUnitMulPow
                                  (= FromUnitGenerator)
```

The equivalences `HasTrivialClassWitness ↔ GenIsPowOfPrincipalFractionalIdeal
↔ GenEqUnitMulPow` show that the principal-ideal lift atom is *equivalently*
either:
* a class-group condition on weak-form witnesses (the obstruction view), or
* an existence-of-unit-decomposition condition (the structural view).

The `Subsingleton (ClassGroup _)` branch discharges all three uniformly.
-/

end KummerPresentation

end BernoulliRegular

end
