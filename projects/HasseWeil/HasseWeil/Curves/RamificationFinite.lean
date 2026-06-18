/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

/-!
# Finiteness of the ramified locus of a separable extension of Dedekind domains

**ROUTE-W, ticket W-2** (the III.4.10c wall): a finite separable extension of Dedekind
domains is unramified outside finitely many primes.  The tool is the **different ideal**
`differentIdeal A B` of `Mathlib/RingTheory/DedekindDomain/Different.lean`:

* the different is nonzero for a separable extension (`differentIdeal_ne_bot`);
* a ramified prime divides the different (`dvd_differentIdeal_iff`, via
  `Algebra.IsUnramifiedAt` and `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`);
* a nonzero ideal of a Dedekind domain has finitely many divisors
  (`UniqueFactorizationMonoid.fintypeSubtypeDvd`).

## Setting (AKLB)

`A` is a Dedekind domain with fraction field `K`, `L / K` is a finite separable field
extension and `B` is (a ring isomorphic to) the integral closure of `A` in `L`, packaged
as `[IsIntegralClosure B A L]`.  The concrete choice `B := integralClosure A L` satisfies
all the hypotheses.

## Main statements

* `RamificationFinite.isDedekindDomain`, `RamificationFinite.module_finite`,
  `RamificationFinite.isFractionRing`, `RamificationFinite.isTorsionFree`: the standard
  AKLB instances, cited from mathlib (Krull–Akizuki in the separable case).
* `RamificationFinite.isSeparable_fractionRing`: transport of separability of `L / K` to
  the canonical fraction fields `FractionRing B / FractionRing A`.
* `RamificationFinite.differentIdeal_ne_bot`: the different ideal is nonzero.
* `RamificationFinite.dvd_differentIdeal_of_ramificationIdx_ne_one`: a ramified prime
  divides the different.
* `RamificationFinite.ramifiedUnderLocus`: the named finite "bad locus" in `A` —
  `⊥` together with the contractions of the divisors of the different ideal.
* `RamificationFinite.ramificationIdx_eq_one_of_notMem`: away from the bad locus every
  prime of `B` is unramified over `A` (**the W-3-facing statement**).
* `RamificationFinite.exists_finite_ramification_locus`: existential packaging needing
  only the AKLB typeclasses.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2 (used for III.4.10c)
* [J. Neukirch, *Algebraic Number Theory*], III.2
-/

namespace HasseWeil.Curves.RamificationFinite

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A K L B : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Field L] [CommRing B]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [Algebra A B] [Algebra B L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [IsIntegralClosure B A L]

/-! ### The standard AKLB instances (deliverable (a))

All of these are cited from mathlib; nothing is rebuilt. -/

section InstanceLemmas

omit [IsDedekindDomain A] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsIntegralClosure B A L] in
include K L in
/-- `A → B` is injective, since `A → K → L` is and it factors through `B`. -/
theorem faithfulSMul : FaithfulSMul A B := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have h : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  rw [IsScalarTower.algebraMap_eq A B L] at h
  exact .of_comp h

omit [IsDedekindDomain A] [Algebra A B] [IsScalarTower A B L] in
include A L in
/-- `B` is a domain, being a subring of the field `L`. -/
theorem isDomain : IsDomain B :=
  Function.Injective.isDomain (algebraMap B L) (IsIntegralClosure.algebraMap_injective B A L)

include A K L in
/-- Krull–Akizuki, separable case: the integral closure of a Dedekind domain in a finite
separable extension of its fraction field is Dedekind
(mathlib's `IsIntegralClosure.isDedekindDomain`). -/
theorem isDedekindDomain : IsDedekindDomain B := by
  haveI := isDomain A L B
  exact IsIntegralClosure.isDedekindDomain A K L B

include K L in
/-- In the separable case the integral closure is module-finite over the base
(mathlib's `IsIntegralClosure.finite`, via the trace pairing). -/
theorem module_finite : Module.Finite A B :=
  IsIntegralClosure.finite A K L B

omit [Algebra.IsSeparable K L] in
include A K in
/-- `L` is the fraction field of `B`
(mathlib's `IsIntegralClosure.isFractionRing_of_finite_extension`). -/
theorem isFractionRing : IsFractionRing B L := by
  haveI := isDomain A L B
  exact IsIntegralClosure.isFractionRing_of_finite_extension A K L B

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
include K L in
/-- `B` is a torsion-free `A`-module (both are domains and `A → B` is injective). -/
theorem isTorsionFree : Module.IsTorsionFree A B := by
  haveI := isDomain A L B
  haveI := faithfulSMul A K L B
  exact Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance

end InstanceLemmas

/-! ### The different ideal of the extension (deliverables (b) and (c))

From here on we carry `[IsDedekindDomain B]` and `[Module.IsTorsionFree A B]` as
typeclass hypotheses so that `differentIdeal A B` elaborates; both are derivable from
the AKLB setup by `RamificationFinite.isDedekindDomain` and
`RamificationFinite.isTorsionFree` above. -/

section Different

variable [IsDedekindDomain B] [Module.IsTorsionFree A B]

include K L

/-- Separability of `L / K` transports to the canonical fraction fields: the extension
`FractionRing B / FractionRing A` (with mathlib's `FractionRing.liftAlgebra` structure)
is separable.  This is the form in which mathlib's different-ideal lemmas consume
separability. -/
theorem isSeparable_fractionRing :
    Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
  haveI := isFractionRing A K L B
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H

/-- **(b)** The different ideal of a separable extension is nonzero
(mathlib's `differentIdeal_ne_bot`). -/
theorem differentIdeal_ne_bot : differentIdeal A B ≠ ⊥ := by
  haveI := module_finite A K L B
  haveI := isSeparable_fractionRing A K L B
  exact _root_.differentIdeal_ne_bot

/-- **(c)** A ramified prime divides the different ideal: if `P` is a nonzero prime of
`B` with `e(P | P ∩ A) ≠ 1`, then `P ∣ 𝔇_{B/A}`.  This is mathlib's
`dvd_differentIdeal_iff` (a prime divides the different iff it is not unramified)
combined with `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`. -/
theorem dvd_differentIdeal_of_ramificationIdx_ne_one {P : Ideal B} (hP : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (he : Ideal.ramificationIdx (P.under A) P ≠ 1) :
    P ∣ differentIdeal A B := by
  haveI := hP
  haveI := module_finite A K L B
  haveI := isSeparable_fractionRing A K L B
  rw [dvd_differentIdeal_iff]
  intro H
  exact he (Ideal.ramificationIdx_eq_one_of_isUnramifiedAt hPbot)

end Different

/-! ### Finiteness of the ramified locus (deliverables (d) and (e)) -/

section BadLocus

variable [IsDedekindDomain B] [Module.IsTorsionFree A B]

/-- The "bad locus" of the extension `B / A`: the zero ideal together with the
contractions to `A` of the primes of `B` dividing the different ideal.  Away from this
finite set every prime of `B` is unramified over `A`
(`RamificationFinite.ramificationIdx_eq_one_of_notMem`). -/
def ramifiedUnderLocus : Set (Ideal A) :=
  insert ⊥ (Ideal.under A '' {P : Ideal B | P ∣ differentIdeal A B})

include K L

/-- **(d)** A nonzero ideal of the Dedekind domain `B` has finitely many divisors, so
only finitely many ideals of `B` divide the different ideal. -/
theorem finite_setOf_dvd_differentIdeal :
    {P : Ideal B | P ∣ differentIdeal A B}.Finite := by
  haveI : Fintype {P : Ideal B // P ∣ differentIdeal A B} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd _ (differentIdeal_ne_bot A K L B)
  exact Set.finite_coe_iff.mp
    (Finite.of_fintype {P : Ideal B // P ∣ differentIdeal A B})

/-- **(d)** The bad locus is finite. -/
theorem finite_ramifiedUnderLocus : (ramifiedUnderLocus A B).Finite :=
  ((finite_setOf_dvd_differentIdeal A K L B).image _).insert _

/-- **(d)** The set of ramified primes of `B` (nonzero primes with ramification index
over their contraction different from `1`) is finite. -/
theorem finite_setOf_ramificationIdx_ne_one :
    {P : Ideal B | P.IsPrime ∧ P ≠ ⊥ ∧
      Ideal.ramificationIdx (P.under A) P ≠ 1}.Finite :=
  (finite_setOf_dvd_differentIdeal A K L B).subset fun _ ⟨hP, hPbot, he⟩ ↦
    dvd_differentIdeal_of_ramificationIdx_ne_one A K L B hP hPbot he

/-- **(d)** The set of primes of `A` over which some prime of `B` ramifies is finite
(it is contained in the image of the finite set of ramified primes of `B` under
contraction). -/
theorem finite_setOf_under_ramified :
    {q : Ideal A | ∃ P : Ideal B, P.IsPrime ∧ P ≠ ⊥ ∧ P.under A = q ∧
      Ideal.ramificationIdx q P ≠ 1}.Finite := by
  refine ((finite_setOf_ramificationIdx_ne_one A K L B).image (Ideal.under A)).subset ?_
  rintro q ⟨P, hP, hPbot, rfl, he⟩
  exact ⟨P, ⟨hP, hPbot, he⟩, rfl⟩

/-- **(e), the W-3-facing statement**: away from the finite bad locus
`ramifiedUnderLocus A B`, every prime of `B` lying over a given prime of `A` is
unramified: `e(P | q) = 1`. -/
theorem ramificationIdx_eq_one_of_notMem {q : Ideal A}
    (hq : q ∉ ramifiedUnderLocus A B) {P : Ideal B} (hP : P.IsPrime)
    (hPq : P.under A = q) :
    Ideal.ramificationIdx q P = 1 := by
  haveI := hP
  haveI := module_finite A K L B
  haveI := isSeparable_fractionRing A K L B
  have hqbot : q ≠ ⊥ := fun h ↦ hq (h ▸ Set.mem_insert _ _)
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    exact hqbot (hPq.symm.trans
      (Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective A B)))
  have hdvd : ¬P ∣ differentIdeal A B := fun hdvd ↦
    hq (Set.mem_insert_iff.mpr (Or.inr ⟨P, hdvd, hPq⟩))
  haveI : Algebra.IsUnramifiedAt A P := not_dvd_differentIdeal_iff.mp hdvd
  have h1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := A) hPbot
  rwa [hPq] at h1

end BadLocus

include K L in
/-- Existential form of the main result, requiring nothing beyond the AKLB setup:
**all but finitely many primes of `A` are unramified in `B`** — there is a finite set
`S` of ideals of `A` such that for every `q ∉ S`, every prime `P` of `B` lying over `q`
has ramification index `1`. -/
theorem exists_finite_ramification_locus :
    ∃ S : Set (Ideal A), S.Finite ∧
      ∀ q : Ideal A, q ∉ S → ∀ P : Ideal B, P.IsPrime → P.under A = q →
        Ideal.ramificationIdx q P = 1 := by
  haveI := isDedekindDomain A K L B
  haveI := isTorsionFree A K L B
  exact ⟨ramifiedUnderLocus A B, finite_ramifiedUnderLocus A K L B,
    fun _ hq _ hP hPq ↦ ramificationIdx_eq_one_of_notMem A K L B hq hP hPq⟩

end HasseWeil.Curves.RamificationFinite
