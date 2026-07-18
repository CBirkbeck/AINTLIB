/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Frobenius

public import CebotarevDensity.Density

/-!
# Frobenius element of a Galois extension of number fields

For a Galois extension `L/K` of number fields and a prime `𝔓` of `𝓞 L` that
is unramified over its image `𝔭 = 𝔓 ∩ 𝓞 K`, the Frobenius automorphism
`Frob 𝔓 ∈ Gal(L/K)` is the unique element of the decomposition group whose
action on `𝓞 L / 𝔓` is the `N𝔭`-th power. As `𝔓` ranges over the primes of
`𝓞 L` above a fixed `𝔭`, the Frobenius elements form a single conjugacy
class in `Gal(L/K)`. This conjugacy class is the *Frobenius substitution* of
`𝔭` and is the object whose distribution Chebotarev describes.

The mathlib counterpart `ValuationSubring.decompositionSubgroup`
(`Mathlib.RingTheory.Valuation.RamificationGroup`) is defined for valuation
subrings of `L`, not for prime ideals of `𝓞 L`; we restate using ideals,
exploiting the `Pointwise` action `Ideal.pointwiseDistribMulAction`.

## Main definitions and results

* `Chebotarev.UnramifiedIn` states that `𝔭` is unramified in `L`.
* `Chebotarev.frobeniusClass` is the conjugacy class of
  Frobenius elements above a prime `𝔭` of `K`.
* `Chebotarev.finite_badPrimes` proves finiteness of the primes whose norm is not coprime to a
  fixed natural number.

The Frobenius automorphism itself is mathlib's `arithFrobAt (𝓞 K) Gal(L/K) 𝔓`,
characterised among elements of `Gal(L/K)` by `IsArithFrobAt (𝓞 K) · 𝔓`; this
file does not wrap it.

## References

* Sharifi, *Algebraic Number Theory*, §2.6 (decomposition groups) and §7.2
  (`docs/algnum.pdf`).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, §3 (the
  Frobenius substitution) (`docs/cheb.pdf`).
-/

@[expose] public section

noncomputable section

open NumberField
open scoped Pointwise

namespace Chebotarev

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- A prime of `𝓞 K` is unramified in `L` if it is nonzero and every maximal prime above it
is unramified over `𝓞 K`. -/
@[nolint unusedArguments]
def UnramifiedIn [IsGalois K L] (𝔭 : Ideal (𝓞 K)) : Prop :=
  𝔭 ≠ ⊥ ∧
    ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
      𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓

/-- A prime of `𝓞 L` with ramification index `1` over its image in `𝓞 K` is nonzero. -/
theorem ne_bot_of_ramificationIdx_eq_one
    {𝔓 : Ideal (𝓞 L)}
    (hunr : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1) : 𝔓 ≠ ⊥ := by
  rintro rfl
  simp only [Ideal.under_bot, Ideal.ramificationIdx'_bot, zero_ne_one] at hunr

/-- An unramified prime is nonzero. -/
theorem UnramifiedIn.ne_bot [IsGalois K L]
    {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) : 𝔭 ≠ ⊥ :=
  hunr.1

/-- A nonzero prime `𝔭` of `𝓞 K` has at least one prime `𝔓` of `𝓞 L` lying
over it, and any such `𝔓` is nonzero. -/
theorem exists_prime_liesOver
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hnz : 𝔭 ≠ ⊥) :
    ∃ 𝔓 : Ideal (𝓞 L), 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥ := by
  obtain ⟨𝔓, hp, hcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
      exact bot_le)
  have : 𝔓.LiesOver 𝔭 := ⟨hcomap.symm⟩
  exact ⟨𝔓, hp, ⟨hcomap.symm⟩, Ideal.ne_bot_of_liesOver_of_ne_bot hnz 𝔓⟩

variable [NumberField K] [NumberField L]

/-- For a prime `𝔓` of `𝓞 L` lying over an unramified prime `𝔭` of `𝓞 K`,
the ramification index `e(𝔓 ∣ 𝔭)` equals `1`. -/
theorem UnramifiedIn.ramificationIdx_eq_one [IsGalois K L]
    {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hP : 𝔓.LiesOver 𝔭) : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := by
  have := hP
  have h𝔓 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) h𝔓
  have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 := hunr.2 𝔓 (‹𝔓.IsPrime›.isMaximal h𝔓) hP
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

/-- The residue ring at a prime above an unramified prime is finite. -/
theorem UnramifiedIn.finite_quotient [IsGalois K L]
    {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hP : 𝔓.LiesOver 𝔭) : Finite (𝓞 L ⧸ 𝔓) :=
  Ideal.finiteQuotientOfFreeOfNeBot 𝔓
    (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hP))

/-- The inertia group at a prime of ramification index one is trivial. -/
theorem inertiaGroup_trivial_of_unramified [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunr : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1) :
    Ideal.inertia Gal(L/K) 𝔓 = ⊥ := by
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hunr
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
  have : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  have : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    let : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
    let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    exact IsGalois.to_isSeparable
  haveI : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpbot
  have hcard :
      Nat.card (Ideal.inertia Gal(L/K) 𝔓) =
        Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (𝔓.under (𝓞 K)) 𝔓,
      Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K),
      ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
  rw [Subgroup.eq_bot_iff_card, hcard, hunr]

/-- The Galois group acts faithfully on `𝓞 L`. -/
private instance faithfulSMul_galois [IsGalois K L] : FaithfulSMul Gal(L/K) (𝓞 L) :=
  IsGaloisGroup.faithful (𝓞 K)

/-- Any arithmetic Frobenius element at an unramified prime equals the canonical one. -/
theorem eq_arithFrobAt_of_isArithFrobAt [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] [Finite (𝓞 L ⧸ 𝔓)]
    [Algebra.IsUnramifiedAt (𝓞 K) 𝔓]
    (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    σ = arithFrobAt (𝓞 K) Gal(L/K) 𝔓 :=
  MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L) <|
    AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) 𝔓.primeCompl_le_nonZeroDivisors

/-- Arithmetic Frobenius elements at primes above the same unramified prime are conjugate. -/
@[nolint unusedArguments]
theorem isConj_of_isArithFrobAt [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (σ σ' : Gal(L/K)) (𝔓 𝔓' : Ideal (𝓞 L)) [𝔓.IsPrime] [𝔓'.IsPrime]
    (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) (hσ' : IsArithFrobAt (𝓞 K) σ' 𝔓')
    (hP : 𝔓.LiesOver 𝔭) (hP' : 𝔓'.LiesOver 𝔭) :
    IsConj σ σ' := by
  have := hP
  have := hP'
  have : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 hP
  have : Finite (𝓞 L ⧸ 𝔓') := UnramifiedIn.finite_quotient K L hunr 𝔓' hP'
  have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    hunr.2 𝔓 (‹𝔓.IsPrime›.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)) hP
  have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓' :=
    hunr.2 𝔓'
      (‹𝔓'.IsPrime›.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓')) hP'
  rw [eq_arithFrobAt_of_isArithFrobAt K L 𝔓 σ hσ,
    eq_arithFrobAt_of_isArithFrobAt K L 𝔓' σ' hσ']
  exact isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔓 𝔓' (hP.over.symm.trans hP'.over)

/-- The arithmetic Frobenius elements above an unramified prime define one conjugacy class. -/
theorem exists_frobeniusClass [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) :
    ∃ C : ConjClasses Gal(L/K),
      ∀ (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
        (_ : IsArithFrobAt (𝓞 K) σ 𝔓) (_ : 𝔓.LiesOver 𝔭),
        C = ConjClasses.mk σ := by
  obtain ⟨𝔓₀, hp₀, hlo₀, _⟩ :=
    exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  have := hp₀
  have : Finite (𝓞 L ⧸ 𝔓₀) := UnramifiedIn.finite_quotient K L hunr 𝔓₀ hlo₀
  refine ⟨ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀), fun σ 𝔓 _ hσ hP ↦ ?_⟩
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
    isConj_of_isArithFrobAt K L 𝔭 hunr (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) σ 𝔓₀ 𝔓
      (hσ := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) (hσ' := hσ)
      (hP := hlo₀) (hP' := hP)

/-- The Frobenius conjugacy class of a prime, with the trivial class as a default value. -/
def frobeniusClass [IsGalois K L] (𝔭 : Ideal (𝓞 K)) : ConjClasses Gal(L/K) :=
  open Classical in
  if h : 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 then
    have := h.1
    (exists_frobeniusClass K L 𝔭 h.2).choose
  else
    ConjClasses.mk 1

/-- `frobeniusClass K L 𝔭` is the conjugacy class of any arithmetic Frobenius `σ`
(`IsArithFrobAt (𝓞 K) σ 𝔓`) at any prime `𝔓` of `𝓞 L` above `𝔭`. -/
theorem frobeniusClass_eq_mk_of_isArithFrobAt [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hσ : IsArithFrobAt (𝓞 K) σ 𝔓)
    (hP : 𝔓.LiesOver 𝔭) :
    frobeniusClass K L 𝔭 = ConjClasses.mk σ := by
  rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, hunr⟩]
  exact (exists_frobeniusClass K L 𝔭 hunr).choose_spec σ 𝔓 hσ hP

/-- The order of an arithmetic Frobenius at an unramified prime is its residue degree. -/
theorem orderOf_eq_finrank_of_isArithFrobAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (h : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1)
    (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    orderOf σ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L h
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
  have : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  have : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    Ideal.ramificationIdx_eq_one_iff.mp
      ((Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot).symm.trans h)
  rw [eq_arithFrobAt_of_isArithFrobAt K L 𝔓 σ hσ]
  let : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
  let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) :=
    Ideal.finiteQuotientOfFreeOfNeBot (𝔓.under (𝓞 K)) hpbot
  have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
    IsGalois.to_isSeparable
  have : Algebra.IsAlgebraic (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
    Algebra.IsAlgebraic.of_finite _ _
  let : Fintype (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Fintype.ofFinite _
  set g₀ : MulAction.stabilizer Gal(L/K) 𝔓 :=
    ⟨arithFrobAt (𝓞 K) Gal(L/K) 𝔓,
      IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) 𝔓⟩ with hg₀
  have hres :
      Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀ =
        FiniteField.frobeniusAlgEquivOfAlgebraic
          (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    ext x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hg₀, Ideal.Quotient.stabilizerHom_apply,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← Nat.card_eq_fintype_card]
    exact (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).mk_apply b
  have hinj :
      Function.Injective (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom]
    show (Ideal.inertia Gal(L/K) 𝔓).subgroupOf (MulAction.stabilizer Gal(L/K) 𝔓) = ⊥
    rw [inertiaGroup_trivial_of_unramified K L 𝔓 h, Subgroup.bot_subgroupOf]
  calc
    orderOf (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) = orderOf g₀ := by
      rw [hg₀, Subgroup.orderOf_mk]
    _ = orderOf (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀) :=
        (orderOf_injective _ hinj g₀).symm
    _ = orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic
          (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓)) := by rw [hres]
    _ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
        FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic _ _

/-- The number of primes above `𝔭` times their residue degree equals `|Gal(L/K)|`. -/
@[nolint unusedArguments]
theorem card_primesAbove_mul_finrank_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (𝔓₀ : Ideal (𝓞 L)) [𝔓₀.IsPrime] (hlo : 𝔓₀.LiesOver 𝔭) :
    Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}
        * Module.finrank (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) =
      Nat.card Gal(L/K) := by
  have hpbot : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L hunr
  have he : Ideal.ramificationIdx' (𝔓₀.under (𝓞 K)) 𝔓₀ = 1 :=
    UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓₀ hlo
  have hP0bot : 𝔓₀ ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L he
  have hunder : 𝔓₀.under (𝓞 K) = 𝔭 := hlo.over.symm
  have hp_under_bot : 𝔓₀.under (𝓞 K) ≠ ⊥ := hunder ▸ hpbot
  have : 𝔓₀.IsMaximal := ‹𝔓₀.IsPrime›.isMaximal hP0bot
  have : (𝔓₀.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓₀.under (𝓞 K)).IsPrime).isMaximal hp_under_bot
  have : Finite (𝓞 L ⧸ 𝔓₀) := UnramifiedIn.finite_quotient K L hunr 𝔓₀ hlo
  have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) := by
    let : Field (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) := Ideal.Quotient.field _
    let : Field (𝓞 L ⧸ 𝔓₀) := Ideal.Quotient.field _
    exact IsGalois.to_isSeparable
  haveI : Finite (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hp_under_bot
  have H :=
    Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
      (G := Gal(L/K)) (𝔓₀.under (𝓞 K)) 𝔓₀
  rw [inertiaGroup_trivial_of_unramified K L 𝔓₀ he, Subgroup.card_bot, mul_one,
      ← Ideal.inertiaDeg'_eq_inertiaDeg (𝔓₀.under (𝓞 K)) 𝔓₀,
      Ideal.inertiaDeg'_algebraMap (𝔓₀.under (𝓞 K)) 𝔓₀] at H
  have hset : (𝔓₀.under (𝓞 K)).primesOver (𝓞 L)
      = {𝔓 : Ideal (𝓞 L) | 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} := by
    ext 𝔓
    refine ⟨fun ⟨hp, hlo'⟩ ↦ ?_, fun ⟨hp, hlo', _⟩ ↦ ?_⟩
    · have := hlo'
      exact ⟨hp, hunder ▸ hlo', Ideal.ne_bot_of_liesOver_of_ne_bot hp_under_bot 𝔓⟩
    · exact ⟨hp, hunder ▸ hlo'⟩
  rwa [hset, ← Nat.card_coe_set_eq] at H

/-- The residue degree at an unramified prime with Frobenius class `[σ]` equals `orderOf σ`. -/
theorem finrank_residue_eq_orderOf
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]
    (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (hCfrob : frobeniusClass K L 𝔭 = C)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hlo : 𝔓.LiesOver 𝔭) :
    Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) = orderOf σ := by
  have hra := UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hlo
  have : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 hlo
  obtain ⟨c, hc⟩ : IsConj (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) σ := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj,
      ← frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr _ 𝔓
        (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) hlo, hCfrob, hσ]
  rw [← hc.orderOf_eq, orderOf_eq_finrank_of_isArithFrobAt K L _ 𝔓 hra
    (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)]

/-- The number of primes above `𝔭` times the order of its Frobenius equals `|Gal(L/K)|`. -/
theorem card_primesAbove_mul_orderOf_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]
    (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (_hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (_hCfrob : frobeniusClass K L 𝔭 = C) :
    Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}
        * orderOf σ =
      Nat.card Gal(L/K) := by
  obtain ⟨𝔓₀, hp₀, hlo₀, _⟩ :=
    exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  rw [← finrank_residue_eq_orderOf K L σ C _hσ 𝔭 hunr _hCfrob 𝔓₀ hlo₀]
  exact card_primesAbove_mul_finrank_eq K L 𝔭 hunr 𝔓₀ hlo₀

/-- Only finitely many nonzero primes of `K` ramify in `L`. -/
theorem finite_ramifiedIn [IsGalois K L] :
    {𝔭 : Ideal (𝓞 K) |
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}.Finite := by
  let : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    FractionRing.liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
  have : IsScalarTower (𝓞 K) (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    FractionRing.isScalarTower_liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
  have hbot : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact differentIdeal_ne_bot
  apply Set.Finite.subset
    ((Ideal.finite_factors hbot).image (fun v ↦ (v.asIdeal).under (𝓞 K)))
  rintro 𝔭 ⟨-, h𝔭bot, hnunr⟩
  simp only [UnramifiedIn, not_and, not_forall] at hnunr
  obtain ⟨𝔓, h𝔓max, h𝔓lo, h𝔓nu⟩ := hnunr h𝔭bot
  have := h𝔓max.isPrime
  have := h𝔓lo
  have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭bot 𝔓
  have hdvd : 𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    by_contra h
    exact h𝔓nu (not_dvd_differentIdeal_iff.mp h)
  exact ⟨⟨𝔓, h𝔓max.isPrime, h𝔓bot⟩, hdvd, h𝔓lo.over.symm⟩

section BadPrimesFinite

variable (m : ℕ)

omit [NumberField K] in
/-- A prime ideal containing `(n : 𝓞 K)` for `1 < n` contains a prime factor of `n`. -/
theorem exists_prime_dvd_natCast_mem
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (n : ℕ) (hn1 : 1 < n) (hmem : (n : 𝓞 K) ∈ 𝔭) :
    ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ (r : 𝓞 K) ∈ 𝔭 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨r, hr, k, rfl⟩ := Nat.exists_prime_and_dvd (by lia : n ≠ 1)
    have hkpos : 0 < k := Nat.pos_of_ne_zero fun hk => by
      subst k
      simp only [mul_zero, Nat.not_lt_zero] at hn1
    have hcast : ((r * k : ℕ) : 𝓞 K) = (r : 𝓞 K) * (k : 𝓞 K) := by
      push_cast
      ring
    rw [hcast] at hmem
    rcases ‹𝔭.IsPrime›.mem_or_mem hmem with hrm | hkm
    · exact ⟨r, hr, ⟨k, rfl⟩, hrm⟩
    · by_cases hk1 : k = 1
      · subst hk1
        simp only [Nat.cast_one] at hkm
        exact absurd (Ideal.eq_top_of_isUnit_mem _ hkm isUnit_one) ‹𝔭.IsPrime›.ne_top
      · have hklt : k < r * k := (Nat.lt_mul_iff_one_lt_left hkpos).mpr hr.one_lt
        obtain ⟨s, hs, hsdvd, hsm⟩ := ih k hklt (by lia) hkm
        exact ⟨s, hs, hsdvd.trans ⟨r, by ring⟩, hsm⟩

/-- A nonzero prime whose norm is not coprime to `m` contains a prime factor of `m`. -/
theorem exists_primeFactor_natCast_mem_of_not_coprime
    [NeZero m] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥)
    (hncop : ¬ (Ideal.absNorm 𝔭).Coprime m) :
    ∃ p ∈ m.primeFactors, (p : 𝓞 K) ∈ 𝔭 := by
  have hN0 : Ideal.absNorm 𝔭 ≠ 0 :=
    fun h ↦ h𝔭 (Ideal.absNorm_eq_zero_iff.mp h)
  have hN1' : Ideal.absNorm 𝔭 ≠ 1 :=
    fun h ↦ ‹𝔭.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  obtain ⟨r, hr, hrdvd, hrm⟩ :=
    exists_prime_dvd_natCast_mem K 𝔭 _ (by lia) (Ideal.absNorm_mem 𝔭)
  have hNdvd : Ideal.absNorm 𝔭 ∣ r ^ Module.finrank ℤ (𝓞 K) := by
    have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hrm)
    rw [Ideal.absNorm_span_singleton,
      show ((r : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (r : ℤ) by
        push_cast
        rfl,
      Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
    exact hd
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (hncop : Nat.gcd (Ideal.absNorm 𝔭) m ≠ 1)
  have hpr : p ∣ r ^ Module.finrank ℤ (𝓞 K) :=
    (hpdvd.trans (Nat.gcd_dvd_left _ _)).trans hNdvd
  have hpeqr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpr)
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), NeZero.ne m⟩,
    hpeqr ▸ hrm⟩

/-- The nonzero primes containing a fixed nonzero integer cast form a finite set. -/
theorem finite_primes_natCast_mem (p : ℕ) (hp : p ≠ 0) :
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (p : 𝓞 K) ∈ 𝔭}.Finite := by
  classical
  have hspan : (Ideal.span {(p : 𝓞 K)}) ≠ 0 := by
    simp only [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  have hfin := Ideal.finite_factors (R := 𝓞 K) hspan
  apply Set.Finite.ofFinset (hfin.toFinset.image (·.asIdeal))
  intro 𝔭
  simp only [Set.Finite.mem_toFinset, Finset.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact
      ⟨v.isPrime, v.ne_bot, (Ideal.dvd_iff_le.mp hv) (Ideal.mem_span_singleton_self _)⟩
  · rintro ⟨hprime, hne, hmem⟩
    exact
      ⟨⟨𝔭, hprime, hne⟩,
        Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem), rfl⟩

/-- The nonzero primes whose norm is not coprime to `m` form a finite set. -/
theorem finite_badPrimes [NeZero m] :
    {𝔭 : Ideal (𝓞 K) |
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Ideal.absNorm 𝔭).Coprime m}.Finite := by
  classical
  refine Set.Finite.subset
    (Set.Finite.biUnion (s := (↑m.primeFactors : Set ℕ)) (Set.toFinite _) fun p _ ↦
      finite_primes_natCast_mem K p ?_)
    ?_
  · exact Nat.pos_of_mem_primeFactors (by assumption) |>.ne'
  · rintro 𝔭 ⟨hprime, hne, hncop⟩
    have := hprime
    obtain ⟨p, hp, hpmem⟩ := exists_primeFactor_natCast_mem_of_not_coprime K m 𝔭 hne hncop
    exact Set.mem_biUnion hp ⟨hprime, hne, hpmem⟩

end BadPrimesFinite

end Chebotarev
