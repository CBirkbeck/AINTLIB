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

## Main definitions

* `Chebotarev.UnramifiedIn` — `𝔭` is unramified in `L`.
* `Chebotarev.frobeniusClass` — the conjugacy class of
  Frobenius elements above a prime `𝔭` of `K`.

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

/-- A prime `𝔭` of `𝓞 K` is unramified in `L` if it is nonzero and every **maximal** prime
`𝔓` of `𝓞 L` lying over `𝔭` is unramified over `𝓞 K` (`Algebra.IsUnramifiedAt`). The `∀ 𝔓`
clause has the same shape as the unramified condition in mathlib's
`NumberField.not_dvd_discr_iff_forall_liesOver`. The `𝔭 ≠ ⊥` clause (on the base prime) is
kept because the Frobenius `arithFrobAt 𝔓` needs a finite residue field `𝓞 L ⧸ 𝔓`; for nonzero
`𝔭` the maximal primes over `𝔭` are exactly its prime divisors, so each has `e(𝔓 ∣ 𝔭) = 1`
(`Algebra.isUnramifiedAt_iff_of_isDedekindDomain`). -/
def UnramifiedIn [IsGalois K L] (𝔭 : Ideal (𝓞 K)) : Prop :=
  𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal), 𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓

/-- A prime of `𝓞 L` with ramification index `1` over its image in `𝓞 K` is nonzero. -/
theorem ne_bot_of_ramificationIdx_eq_one
    {𝔓 : Ideal (𝓞 L)} (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) : 𝔓 ≠ ⊥ := by
  rintro rfl
  simp at hunr

/-- An unramified prime is nonzero — the first clause of `UnramifiedIn`. -/
theorem UnramifiedIn.ne_bot [IsGalois K L] {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) :
    𝔭 ≠ ⊥ :=
  hunr.1

/-- A nonzero prime `𝔭` of `𝓞 K` has at least one prime `𝔓` of `𝓞 L` lying
over it, and any such `𝔓` is nonzero. -/
theorem exists_prime_liesOver
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hnz : 𝔭 ≠ ⊥) :
    ∃ 𝔓 : Ideal (𝓞 L), 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥ := by
  obtain ⟨𝔓, hp, hcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by simp)
  have : 𝔓.LiesOver 𝔭 := ⟨hcomap.symm⟩
  exact ⟨𝔓, hp, ⟨hcomap.symm⟩, Ideal.ne_bot_of_liesOver_of_ne_bot hnz 𝔓⟩

variable [NumberField K] [NumberField L]

/-- For a prime `𝔓` of `𝓞 L` lying over an unramified prime `𝔭` of `𝓞 K`,
the ramification index `e(𝔓 ∣ 𝔭)` equals `1`. -/
theorem UnramifiedIn.ramificationIdx_eq_one [IsGalois K L]
    {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hP : 𝔓.LiesOver 𝔭) : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1 := by
  have := hP
  have h𝔓 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔓).mp
    (hunr.2 𝔓 (‹𝔓.IsPrime›.isMaximal h𝔓) hP)

/-- For a prime `𝔓` of `𝓞 L` lying over an unramified prime `𝔭` of `𝓞 K`, the residue ring
`𝓞 L ⧸ 𝔓` is finite. -/
theorem UnramifiedIn.finite_quotient [IsGalois K L]
    {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hP : 𝔓.LiesOver 𝔭) : Finite (𝓞 L ⧸ 𝔓) :=
  Ideal.finiteQuotientOfFreeOfNeBot 𝔓
    (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hP))

/-- For an unramified prime `𝔓` (ramification index `e(𝔓 ∣ 𝔭) = 1`), the inertia group of
`Gal(L/K)` at `𝔓` is trivial. -/
theorem inertiaGroup_trivial_of_unramified [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
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
  rwa [Subgroup.eq_bot_iff_card,
      Ideal.card_inertia_eq_ramificationIdxIn (𝔓.under (𝓞 K)) hpbot 𝔓,
      Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K)]

/-- The Galois group acts faithfully on `𝓞 L`, via mathlib's `IsGaloisGroup` for the ring
extension `(𝓞 K, 𝓞 L)`. Pinning the base `𝓞 K` here lets instance search find this at every
call site. Needed so that the uniqueness of the Frobenius `AlgHom` (`eq_of_isUnramifiedAt`)
transfers to the group `Gal(L/K)`. -/
private instance faithfulSMul_galois [IsGalois K L] : FaithfulSMul Gal(L/K) (𝓞 L) :=
  IsGaloisGroup.faithful (𝓞 K)

/-- Any arithmetic Frobenius element at an unramified prime `𝔓` equals the canonical
`arithFrobAt 𝔓`: the residue-field characterisation pins it down uniquely. -/
theorem eq_arithFrobAt_of_isArithFrobAt [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] [Finite (𝓞 L ⧸ 𝔓)] [Algebra.IsUnramifiedAt (𝓞 K) 𝔓]
    (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    σ = arithFrobAt (𝓞 K) Gal(L/K) 𝔓 :=
  MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L) <|
    AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) 𝔓.primeCompl_le_nonZeroDivisors

/-- For a prime `𝔭` of `𝓞 K` unramified in `L`, any two elements `σ`, `σ'` of `Gal(L/K)`
that are arithmetic Frobenius elements (`IsArithFrobAt`) at primes `𝔓`, `𝔓'` above `𝔭` are
conjugate. -/
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
    hunr.2 𝔓' (‹𝔓'.IsPrime›.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓')) hP'
  rw [eq_arithFrobAt_of_isArithFrobAt K L 𝔓 σ hσ,
    eq_arithFrobAt_of_isArithFrobAt K L 𝔓' σ' hσ']
  exact isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔓 𝔓' (hP.over.symm.trans hP'.over)

/-- Existence and well-definedness of the Frobenius
conjugacy class of an unramified prime `𝔭` of `𝓞 K`: there is a single conjugacy class `C`
such that `C = ConjClasses.mk σ` for every `σ` that is an arithmetic Frobenius
(`IsArithFrobAt`) at some prime `𝔓` of `𝓞 L` above `𝔭`.
Sharifi §7.2 + SL Appendix paragraph 1. -/
theorem exists_frobeniusClass [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) :
    ∃ C : ConjClasses Gal(L/K),
      ∀ (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (_ : IsArithFrobAt (𝓞 K) σ 𝔓)
        (_ : 𝔓.LiesOver 𝔭), C = ConjClasses.mk σ := by
  obtain ⟨𝔓₀, hp₀, hlo₀, _⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  have := hp₀
  have := hlo₀
  have : Finite (𝓞 L ⧸ 𝔓₀) := UnramifiedIn.finite_quotient K L hunr 𝔓₀ hlo₀
  refine ⟨ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀), fun σ 𝔓 _ hσ hP ↦ ?_⟩
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_of_isArithFrobAt K L 𝔭 hunr
    (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) σ 𝔓₀ 𝔓
    (hσ := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) (hσ' := hσ) (hP := hlo₀) (hP' := hP))

/-- The Frobenius conjugacy class of a prime `𝔭` of `𝓞 K`. When `𝔭` is a
nonzero unramified prime, this is the conjugacy class of any arithmetic Frobenius `σ`
(`IsArithFrobAt`) at any prime `𝔓` of `𝓞 L` above `𝔭` (well-definedness from
`exists_frobeniusClass`). For other primes the value is the trivial class —
a junk value never used in the Chebotarev statement (which always restricts
to unramified nonzero primes). -/
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

open scoped Pointwise in
/-- **API gap — order of the Frobenius equals the residue degree.** For an unramified
prime `𝔓` of `𝓞 L`, the decomposition group `D_𝔓` is cyclic of order the residue degree
`f = [κ(𝔓) : κ(𝔭)]`, generated by `Frob_𝔓`; hence `orderOf Frob_𝔓 = f`. mathlib has
`Ideal.card_stabilizer_eq_card_inertia_mul_finrank` (`|D_𝔓| = |I_𝔓| · f`) but not that
`Frob_𝔓` generates `D_𝔓`, so this leaf is a genuine API gap. -/
theorem orderOf_eq_finrank_of_isArithFrobAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (h : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    orderOf σ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L h
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
  have : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  have : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot).mpr h
  rw [eq_arithFrobAt_of_isArithFrobAt K L 𝔓 σ hσ]
  let : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
  let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) :=
    Ideal.finiteQuotientOfFreeOfNeBot (𝔓.under (𝓞 K)) hpbot
  have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := IsGalois.to_isSeparable
  have : Algebra.IsAlgebraic (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := Algebra.IsAlgebraic.of_finite _ _
  let : Fintype (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Fintype.ofFinite _
  set g₀ : MulAction.stabilizer Gal(L/K) 𝔓 :=
    ⟨arithFrobAt (𝓞 K) Gal(L/K) 𝔓,
      IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) 𝔓⟩ with hg₀
  have hres : Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀
      = FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    ext x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hg₀, Ideal.Quotient.stabilizerHom_apply,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← Nat.card_eq_fintype_card]
    exact (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).mk_apply b
  have hinj : Function.Injective (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom]
    show (Ideal.inertia Gal(L/K) 𝔓).subgroupOf (MulAction.stabilizer Gal(L/K) 𝔓) = ⊥
    rw [inertiaGroup_trivial_of_unramified K L 𝔓 h, Subgroup.bot_subgroupOf]
  calc orderOf (arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
      = orderOf g₀ := by rw [hg₀, Subgroup.orderOf_mk]
    _ = orderOf (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀) :=
        (orderOf_injective _ hinj g₀).symm
    _ = orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic
          (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓)) := by rw [hres]
    _ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
        FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic _ _

/-- **Orbit–stabilizer count via the residue degree** (Sharifi 7.2.2 Step 1, p. 143).
The number of primes of `𝓞 L` above `𝔭` times the residue degree `[κ(𝔓₀) : κ(𝔭)]` of any
prime `𝔓₀` above `𝔭` equals `|Gal(L/K)|`. -/
theorem card_primesAbove_mul_finrank_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (𝔓₀ : Ideal (𝓞 L)) [𝔓₀.IsPrime] (hlo : 𝔓₀.LiesOver 𝔭) :
    Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}
        * Module.finrank (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) = Nat.card Gal(L/K) := by
  have hpbot : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L hunr
  have he : Ideal.ramificationIdx (𝔓₀.under (𝓞 K)) 𝔓₀ = 1 :=
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
  have H := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
    (G := Gal(L/K)) (𝔓₀.under (𝓞 K)) 𝔓₀
  rw [inertiaGroup_trivial_of_unramified K L 𝔓₀ he, Subgroup.card_bot, mul_one] at H
  have hset : (𝔓₀.under (𝓞 K)).primesOver (𝓞 L)
      = {𝔓 : Ideal (𝓞 L) | 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} := by
    ext 𝔓
    refine ⟨fun ⟨hp, hlo'⟩ ↦ ?_, fun ⟨hp, hlo', _⟩ ↦ ?_⟩
    · have := hlo'
      exact ⟨hp, hunder ▸ hlo', Ideal.ne_bot_of_liesOver_of_ne_bot hp_under_bot 𝔓⟩
    · exact ⟨hp, hunder ▸ hlo'⟩
  rwa [hset, ← Nat.card_coe_set_eq] at H

/-- The residue degree `[κ(𝔓) : κ(𝔭)]` at an unramified prime `𝔓` above `𝔭`, whose
Frobenius class is `C = [σ]`, equals `orderOf σ`. -/
theorem finrank_residue_eq_orderOf
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hCfrob : frobeniusClass K L 𝔭 = C)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hlo : 𝔓.LiesOver 𝔭) :
    Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) = orderOf σ := by
  have hra := UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hlo
  have : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 hlo
  obtain ⟨c, hc⟩ : IsConj (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) σ := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj,
      ← frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr _ 𝔓
        (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) hlo, hCfrob, hσ]
  rw [← hc.orderOf_eq,
    orderOf_eq_finrank_of_isArithFrobAt K L _ 𝔓 hra (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)]

/-- **Orbit–stabilizer for the primes above `𝔭`** (Sharifi 7.2.2 Step 1, p. 143). The
Galois group acts transitively on the primes of `𝓞 L` above `𝔭`, with stabiliser the
decomposition group `D_𝔓`; for an unramified prime `D_𝔓` is cyclic of order `f = ord σ`
(generated by the Frobenius). Hence the number of primes above `𝔭` times `ord σ` is
`|Gal(L/K)|`. -/
theorem card_primesAbove_mul_orderOf_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (_hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (_hCfrob : frobeniusClass K L 𝔭 = C) :
    Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} * orderOf σ
      = Nat.card Gal(L/K) := by
  obtain ⟨𝔓₀, hp₀, hlo₀, _⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  rw [← finrank_residue_eq_orderOf K L σ C _hσ 𝔭 hunr _hCfrob 𝔓₀ hlo₀]
  exact card_primesAbove_mul_finrank_eq K L 𝔭 hunr 𝔓₀ hlo₀

/-- Only finitely many nonzero primes of `K` ramify in `L`. -/
theorem finite_ramifiedIn [IsGalois K L] :
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}.Finite := by
  let : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    FractionRing.liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
  have : IsScalarTower (𝓞 K) (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    FractionRing.isScalarTower_liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
  have : Algebra.IsSeparable (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := inferInstance
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

/-! ### Finiteness of the bad-prime set

The "bad" primes are the nonzero primes `𝔭` whose norm is *not* coprime to `m`. Each such `𝔭`
contains the integer cast `(p : 𝓞 K)` of some prime factor `p ∣ m` (the rational prime below
`𝔭`), so the bad-prime set is covered by the finitely many prime divisors of the ideals
`(p)`, `p ∈ m.primeFactors` — a finite set. -/

section BadPrimesFinite

variable (m : ℕ)

omit [NumberField K] in
/-- If the integer cast `(n : 𝓞 K)` lies in a prime ideal `𝔭` and `1 < n`, then some rational
prime factor `r ∣ n` already casts into `𝔭`. -/
theorem exists_prime_dvd_natCast_mem
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (n : ℕ) (hn1 : 1 < n) (hmem : (n : 𝓞 K) ∈ 𝔭) :
    ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ (r : 𝓞 K) ∈ 𝔭 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨r, hr, k, rfl⟩ := Nat.exists_prime_and_dvd (by lia : n ≠ 1)
    have hkpos : 0 < k := Nat.pos_of_ne_zero <| by rintro rfl; simp at hn1
    have hcast : ((r * k : ℕ) : 𝓞 K) = (r : 𝓞 K) * (k : 𝓞 K) := by push_cast; ring
    rw [hcast] at hmem
    rcases ‹𝔭.IsPrime›.mem_or_mem hmem with hrm | hkm
    · exact ⟨r, hr, ⟨k, rfl⟩, hrm⟩
    · by_cases hk1 : k = 1
      · subst hk1
        simp only [Nat.cast_one] at hkm
        exact absurd (Ideal.eq_top_of_isUnit_mem _ hkm isUnit_one) ‹𝔭.IsPrime›.ne_top
      · have hklt : k < r * k := by
          have h2 : 2 ≤ r := hr.two_le
          calc k = 1 * k := (one_mul k).symm
            _ < r * k := (Nat.mul_lt_mul_right hkpos).2 (by lia)
        obtain ⟨s, hs, hsdvd, hsm⟩ := ih k hklt (by lia) hkm
        exact ⟨s, hs, hsdvd.trans ⟨r, by ring⟩, hsm⟩

/-- A nonzero prime with norm not coprime to `m` contains `(p : 𝓞 K)` for some `p ∈ m.primeFactors`:
the norm `N𝔭` is a power of a single rational prime `r` (since `r ∈ 𝔭 ⇒ N𝔭 ∣ r^d`), and the prime
`p ∣ gcd(N𝔭, m)` must equal `r`, hence `p ∣ m` and `(p : 𝓞 K) = (r : 𝓞 K) ∈ 𝔭`. -/
theorem exists_primeFactor_natCast_mem_of_not_coprime
    [NeZero m] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥)
    (hncop : ¬ (Ideal.absNorm 𝔭).Coprime m) :
    ∃ p ∈ m.primeFactors, (p : 𝓞 K) ∈ 𝔭 := by
  have hN0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ h𝔭 (Ideal.absNorm_eq_zero_iff.mp h)
  have hN1' : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ ‹𝔭.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  obtain ⟨r, hr, hrdvd, hrm⟩ :=
    exists_prime_dvd_natCast_mem K 𝔭 _ (by lia) (Ideal.absNorm_mem 𝔭)
  have hNdvd : Ideal.absNorm 𝔭 ∣ r ^ Module.finrank ℤ (𝓞 K) := by
    have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hrm)
    rwa [Ideal.absNorm_span_singleton, show ((r : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (r : ℤ) by
        push_cast; rfl, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (hncop : Nat.gcd (Ideal.absNorm 𝔭) m ≠ 1)
  have hpr : p ∣ r ^ Module.finrank ℤ (𝓞 K) := (hpdvd.trans (Nat.gcd_dvd_left _ _)).trans hNdvd
  have hpeqr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpr)
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), NeZero.ne m⟩,
    hpeqr ▸ hrm⟩

/-- The nonzero primes containing a fixed nonzero integer cast `(p : 𝓞 K)` form a finite set
(they are the prime divisors of `(p)`, and a nonzero ideal has finitely many prime divisors). -/
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
    exact ⟨v.isPrime, v.ne_bot, (Ideal.dvd_iff_le.mp hv) (Ideal.mem_span_singleton_self _)⟩
  · rintro ⟨hprime, hne, hmem⟩
    exact ⟨⟨𝔭, hprime, hne⟩, Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem),
      rfl⟩

/-- **The bad-prime set is finite.** The nonzero primes whose norm is not coprime to `m` are
covered by the finitely many primes containing `(p : 𝓞 K)` for `p ∈ m.primeFactors`. -/
theorem finite_badPrimes [NeZero m] :
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Ideal.absNorm 𝔭).Coprime m}.Finite := by
  classical
  refine Set.Finite.subset
    (Set.Finite.biUnion (s := (↑m.primeFactors : Set ℕ)) (Set.toFinite _) fun p _ ↦
      finite_primes_natCast_mem K p ?_) ?_
  · exact Nat.pos_of_mem_primeFactors (by assumption) |>.ne'
  · rintro 𝔭 ⟨hprime, hne, hncop⟩
    have := hprime
    obtain ⟨p, hp, hpmem⟩ := exists_primeFactor_natCast_mem_of_not_coprime K m 𝔭 hne hncop
    exact Set.mem_biUnion hp ⟨hprime, hne, hpmem⟩

end BadPrimesFinite

end Chebotarev
