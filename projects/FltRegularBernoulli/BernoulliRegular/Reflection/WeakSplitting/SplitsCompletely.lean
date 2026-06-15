module

public import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# A prime ideal that splits completely in an extension

This file defines `BernoulliRegular.Ideal.SplitsCompletely`, the predicate
that every prime ideal of `S` lying over a fixed prime `p` of `R` is
unramified with trivial residue extension. Concretely, every such prime
has ramification index `1` and inertia degree `1`.

In the number-field setting (`R = 𝓞 K`, `S = 𝓞 M`, `M / K` finite), this is
the standard "`p` splits completely in `M`" property: there are exactly
`[M : K]` primes above `p`, each unramified with residue degree one.

The cardinality consequence
`SplitsCompletely.card_primesOverFinset_eq_finrank` follows immediately from
`Ideal.sum_ramification_inertia` (the fundamental identity
`∑ e_P · f_P = [L : K]`). The converse, packaged as an `Iff`, characterizes
splitting completely purely by the cardinality of the prime fibre.

This is the basic local input for the polar-density / weak-splitting argument
of `BernoulliRegular/Reflection/kummer_reflection.tex`, Section 5 (REF-21).

## Main definitions

* `BernoulliRegular.Ideal.SplitsCompletely`: the predicate
  `∀ P ∈ IsDedekindDomain.primesOverFinset p S,
    ramificationIdx p P = 1 ∧ inertiaDeg p P = 1`.

## Main results

* `BernoulliRegular.Ideal.SplitsCompletely.card_primesOverFinset_eq_finrank`:
  if `p` splits completely in `S`, the number of primes of `S` lying over `p`
  equals `[Frac S : Frac R]`.
* `BernoulliRegular.Ideal.splitsCompletely_iff_card_primesOverFinset_eq_finrank`:
  conversely, the cardinality condition characterizes `SplitsCompletely`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Ideal

variable {R : Type*} [CommRing R]

/--
A nonzero prime `p` of `R` splits completely in an `R`-algebra `S` (with `S`
Dedekind) if every prime of `S` lying over `p` is unramified
(`ramificationIdx = 1`) with trivial residue extension (`inertiaDeg = 1`).

Under the standard hypotheses linking `R, K, S, L` of a finite separable
extension of fraction fields, this is equivalent to having exactly `[L : K]`
primes of `S` above `p`; see
`splitsCompletely_iff_card_primesOverFinset_eq_finrank`.
-/
def SplitsCompletely
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S] (p : Ideal R) :
  Prop :=
  ∀ P ∈ IsDedekindDomain.primesOverFinset p S,
    p.ramificationIdx P = 1 ∧ p.inertiaDeg P = 1

variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable (K L : Type*) [Field K] [Field L]
variable [IsDedekindDomain R]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra R L] [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L]
variable [Module.Finite R S] [Module.IsTorsionFree R S]

omit [Module.IsTorsionFree R S] in
/--
If `p` splits completely in `S`, then the number of primes of `S` lying over
`p` equals the field-extension degree `[L : K]`.
-/
theorem SplitsCompletely.card_primesOverFinset_eq_finrank
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) (h : SplitsCompletely S p) :
    (IsDedekindDomain.primesOverFinset p S).card = Module.finrank K L := by
  classical
  calc (IsDedekindDomain.primesOverFinset p S).card
      = ∑ _P ∈ IsDedekindDomain.primesOverFinset p S, 1 := Finset.card_eq_sum_ones _
    _ = ∑ P ∈ IsDedekindDomain.primesOverFinset p S,
          p.ramificationIdx P * p.inertiaDeg P := by
        refine Finset.sum_congr rfl fun P hP => ?_
        obtain ⟨he, hf⟩ := h P hP
        simp [he, hf]
    _ = Module.finrank K L := Ideal.sum_ramification_inertia S K L hp0

/--
A prime `p` splits completely in `S` if and only if the number of primes of
`S` lying over `p` equals the field-extension degree `[L : K]`. The forward
direction is `SplitsCompletely.card_primesOverFinset_eq_finrank`; the
converse uses the fact that in `Ideal.sum_ramification_inertia` each summand
`ramificationIdx p P * inertiaDeg p P` is at least one, and a sum of natural
numbers at least one whose total equals the cardinality is identically one.
-/
theorem splitsCompletely_iff_card_primesOverFinset_eq_finrank
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    SplitsCompletely S p ↔
      (IsDedekindDomain.primesOverFinset p S).card = Module.finrank K L := by
  classical
  refine ⟨fun h => SplitsCompletely.card_primesOverFinset_eq_finrank
    (K := K) (L := L) S hp0 h, fun hcard => ?_⟩
  intro P hP
  have hone : ∀ Q ∈ IsDedekindDomain.primesOverFinset p S,
      1 ≤ p.ramificationIdx Q * p.inertiaDeg Q := by
    intro Q hQ
    haveI : Q.IsPrime := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hQ).1
    haveI : Q.LiesOver p := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hQ).2
    refine Right.one_le_mul ?_ ?_
    · exact Nat.pos_iff_ne_zero.mpr <|
        _root_.Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _ hp0
    · exact Nat.pos_iff_ne_zero.mpr <| _root_.Ideal.inertiaDeg_ne_zero _ _
  have hsum_eq : ∑ _Q ∈ IsDedekindDomain.primesOverFinset p S, 1 =
      ∑ Q ∈ IsDedekindDomain.primesOverFinset p S,
        p.ramificationIdx Q * p.inertiaDeg Q := by
    rw [Ideal.sum_ramification_inertia S K L hp0, ← Finset.card_eq_sum_ones, hcard]
  have hone_each := (Finset.sum_eq_sum_iff_of_le hone).mp hsum_eq P hP
  exact ⟨Nat.eq_one_of_mul_eq_one_right hone_each.symm,
    Nat.eq_one_of_mul_eq_one_left hone_each.symm⟩

end Ideal

end BernoulliRegular
