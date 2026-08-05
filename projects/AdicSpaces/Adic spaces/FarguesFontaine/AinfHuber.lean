/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.PerfectoidFieldCharP
import «Adic spaces».HuberRings
import «Adic spaces».AffinoidRings
import «Adic spaces».AdicConvergence
import «Adic spaces».TateAlgebraTopology
import Mathlib.Algebra.CharP.Quotient
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.WittVector.TeichmullerSeries
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# A_inf = W(O_F) as a complete Huber ring

For a perfectoid field `F` of characteristic `p` with ring of integers `O_F` and
pseudo-uniformizer `ϖ`, this file equips `A_inf := W(O_F)` (p-typical Witt vectors) with
the `(p, [ϖ])`-adic topology and proves it is a complete Huber ring which is its own ring
of integral elements. This is the ring whose adic spectrum carries the Fargues--Fontaine
curve.

## Main definitions

* `FarguesFontaine.Ainf` : the ring `W(O_F)`.
* `FarguesFontaine.teichPi` : the Teichmüller lift `[ϖ] ∈ A_inf`.
* `FarguesFontaine.Iinf` : the ideal `(p, [ϖ]) ⊆ A_inf`.
* The `(p,[ϖ])`-adic `TopologicalSpace`/`IsTopologicalRing`/`IsHuberRing`/`PlusSubring`
  instances on `A_inf` (the `PlusSubring` is `⊤`: `A_inf⁺ = A_inf`).

## Main results

* `isAdic_Iinf` : the topology is `(p,[ϖ])`-adic for every choice of pseudo-uniformizer.
* `isHausdorff_Iinf`, `isAdicComplete_Iinf` : `A_inf` is `(p,[ϖ])`-adically separated and
  complete.
* `isAffinoidRing_Ainf` : `A_inf⁺ = A_inf` is a ring of integral elements.

## Sources

* [Kedlaya, *Sheaves, stacks, and shtukas* (AWS 2017)][kedlaya-aws], Definition 3.1.2:
  "Define the ring A_inf := W(R⁺). It is complete for the adic topology defined by the
  inverse image of some ideal of definition of R⁺."
* [Scholze–Weinstein, *Berkeley Lectures*][sw2020], §13.1: "let A_inf = W(O_{C♭}), with
  its (p, [p♭])-adic topology."
* [BFHHLWY][bfhhlwy2018], Definition 2.1.1 (the ring `W_{E°}(F°)` for `E = Q_p`).
* mathlib: `WittVector.isAdicCompleteIdealSpanP` (p-adic completeness of `W(k)` for
  perfect `k`).
-/

open TopologicalRing ValuationSpectrum WittVector

universe u


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]

/-- `A_inf = W(O_F)`, the ring of `p`-typical Witt vectors of the ring of integers of a
perfectoid field `F` of characteristic `p`.

Source: [BFHHLWY, Def 2.1.1] with `E = Q_p` (there `W_{E°}(F°) = W(F°)`);
[Kedlaya-AWS, Def 3.1.2]. -/
abbrev Ainf : Type u := WittVector p (OF F)

/-- The Teichmüller lift `[ϖ] ∈ A_inf` of the pseudo-uniformizer.

Source: [BFHHLWY, Def 2.1.1] (the element `[ϖ]`); [SW, §12.2] (the element `[p♭]`). -/
def teichPi (ϖ : PseudoUniformizer F) : Ainf p F :=
  WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ)

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- Teichmüller lifts of powers: `[ϖ]^n = [ϖ^n]`. This is what makes rational exponents
in the window inequalities (Kedlaya-AWS, Rem. 3.1.9) clearable to integer powers. -/
theorem teichPi_pow (ϖ : PseudoUniformizer F) (n : ℕ) :
    teichPi p F ϖ ^ n = WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ ^ n) :=
  (map_pow (WittVector.teichmuller p) (PseudoUniformizer.toOF F ϖ) n).symm

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- `[ϖ] ≠ 0` in `A_inf`. -/
theorem teichPi_ne_zero (ϖ : PseudoUniformizer F) : teichPi p F ϖ ≠ 0 := fun h =>
  PseudoUniformizer.toOF_ne_zero F ϖ (by
    simpa [teichPi, WittVector.teichmuller_coeff_zero] using
      congrArg (fun x : Ainf p F => x.coeff 0) h)

omit [CharP F p] in
/-- Mutual divisibility of Teichmüller lifts: for pseudo-uniformizers `ϖ, ϖ'` some power
of `[ϖ']` lies in the ideal `([ϖ])`. In `F` the set `ϖ·F°` is a neighbourhood of `0` and
`ϖ'` is topologically nilpotent, so `ϖ'^k ∈ ϖ·F°`; apply the multiplicative Teichmüller
lift.

Source: [Kedlaya-AWS, §11.2-style remark]: "for any other choice ϖ', there is some n such
that ϖ | (ϖ')^n". -/
theorem exists_teichPi_pow_mem_span_teichPi (ϖ ϖ' : PseudoUniformizer F) :
    ∃ k : ℕ, teichPi p F ϖ' ^ k ∈ Ideal.span {teichPi p F ϖ} := by
  obtain ⟨P⟩ := IsHuberRing.exists_pairOfDefinition (A := F)
  obtain ⟨k, hk⟩ := ϖ'.isTopologicallyNilpotent.exists_pow_mem_of_mem_nhds
    ((ϖ.val.isUnit.isOpenMap_smul _ P.isOpen_powerBoundedSubring).mem_nhds
      ⟨0, isPowerBounded_zero, smul_zero _⟩)
  obtain ⟨b, hb, hbeq⟩ := hk
  refine ⟨k, ?_⟩
  rw [teichPi_pow, Ideal.mem_span_singleton']
  refine ⟨WittVector.teichmuller p ⟨b, hb⟩, ?_⟩
  rw [teichPi, ← map_mul]
  congr 1
  exact Subtype.ext (by simpa [PseudoUniformizer.toOF, mul_comm] using hbeq)

/-- The ideal `I = (p, [ϖ]) ⊆ A_inf` defining the topology.

Source: [SW, §13.1] "(p, [p♭])-adic topology". -/
def Iinf (ϖ : PseudoUniformizer F) : Ideal (Ainf p F) :=
  Ideal.span {(p : Ainf p F), teichPi p F ϖ}

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- If `[ϖ']^k ∈ ([ϖ])` then the `(p,[ϖ'])`-filtration refines the `(p,[ϖ])`-filtration:
`(p,[ϖ'])^((k+1)·m) ⊆ (p,[ϖ])^m`. Monomial bookkeeping: in each monomial `p^a·[ϖ']^b`
with `a + b = (k+1)m`, either `a ≥ m` or `b ≥ km`. -/
theorem Iinf_pow_le_of_teichPi_pow_mem {ϖ ϖ' : PseudoUniformizer F} {k : ℕ}
    (h : teichPi p F ϖ' ^ k ∈ Ideal.span {teichPi p F ϖ}) (m : ℕ) :
    Iinf p F ϖ' ^ ((k + 1) * m) ≤ Iinf p F ϖ ^ m := by
  have hexp : (k + 1) * m = m + k * m := by ring
  rw [hexp, Iinf, Iinf, Ideal.span_insert, Ideal.span_insert]
  refine Ideal.sup_pow_add_le_pow_sup_pow.trans (sup_le ?_ ?_)
  · exact Ideal.pow_right_mono le_sup_left m
  · rw [Ideal.span_singleton_pow, pow_mul]
    exact ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.pow_mem_pow h m)).trans
      (Ideal.pow_right_mono le_sup_right m)

/-- The `(p,[ϖ])`-adic topology on `A_inf`, using the canonical pseudo-uniformizer of the
Tate ring `F`. By `isAdic_Iinf` below, the topology does not depend on this choice.

Source: [SW, §13.1]; [Kedlaya-AWS, Def 3.1.2]. -/
instance instTopologicalSpaceAinf : TopologicalSpace (Ainf p F) :=
  (Iinf p F (IsTateRing.pseudoUniformizer (A := F))).adicTopology

/-- `A_inf` is a nonarchimedean ring — hence in particular a topological ring — for the
`(p,[ϖ])`-adic topology: the ideal powers form a neighbourhood basis of `0` consisting of
open additive subgroups. -/
instance instNonarchimedeanRingAinf : NonarchimedeanRing (Ainf p F) :=
  Ideal.nonarchimedean _

/-- The topology on `A_inf` is `(p,[ϖ])`-adic for EVERY pseudo-uniformizer `ϖ` (not just
the canonical one used to define the instance). In particular the construction is
independent of the choice of `ϖ`.

Proof idea: for pseudo-uniformizers `ϖ, ϖ'` one has `ϖ'^n ∈ ϖ·O_F` for some `n` (both are
topologically nilpotent units), hence `[ϖ']^n = [ϖ'^n] ∈ [ϖ]·A_inf`, so the two ideals
generate mutually cofinal filtrations.

Source: [Kedlaya-AWS, §11.2-style remark]: "this is independent of the choice of ϖ, as
for any other choice ϖ', there is some n such that ϖ | (ϖ')^n and ϖ' | ϖ^n" (stated there
for the analogous locus; the same divisibility argument applies to the filtration). -/
theorem isAdic_Iinf (ϖ : PseudoUniformizer F) : IsAdic (Iinf p F ϖ) := by
  have h₀ : IsAdic (Iinf p F (IsTateRing.pseudoUniformizer (A := F))) := rfl
  obtain ⟨k, hk⟩ := exists_teichPi_pow_mem_span_teichPi p F
    (IsTateRing.pseudoUniformizer (A := F)) ϖ
  obtain ⟨l, hl⟩ := exists_teichPi_pow_mem_span_teichPi p F ϖ
    (IsTateRing.pseudoUniformizer (A := F))
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · exact AddSubgroup.isOpen_mono
      (H₁ := (Iinf p F (IsTateRing.pseudoUniformizer (A := F)) ^ ((l + 1) * n)).toAddSubgroup)
      (H₂ := (Iinf p F ϖ ^ n).toAddSubgroup)
      (fun x hx => Iinf_pow_le_of_teichPi_pow_mem p F hl n hx)
      ((isAdic_iff.mp h₀).1 ((l + 1) * n))
  · obtain ⟨n, hn⟩ := (isAdic_iff.mp h₀).2 s hs
    exact ⟨(k + 1) * n, fun x hx => hn (Iinf_pow_le_of_teichPi_pow_mem p F hk n hx)⟩

/-- `A_inf` is a Huber ring: `(A_inf, (p,[ϖ]))` is a pair of definition — the ring itself
is open, and the ideal is finitely generated (two generators) with adic topology.

Source: [Kedlaya-AWS, Def 3.1.2] (A_inf with an adic topology defined by a finitely
generated ideal); [SW, §13.1]. -/
instance instIsHuberRingAinf : IsHuberRing (Ainf p F) :=
  isHuberRing_ofAdic _ (Submodule.fg_span (Set.toFinite _))

/-- `A_inf⁺ = A_inf`: the plus-subring is the whole ring.

Source: [Kedlaya-AWS, Rem. 3.1.9 / Def 3.1.5] (the pair is `Spa(A_inf, A_inf)`);
[BFHHLWY, Def 2.1.1] writes `Spa(W_{E°}(F°))`, i.e. the self-pair. -/
instance instPlusSubringAinf : PlusSubring (Ainf p F) where
  toSubring := ⊤

omit [CharP F p] in
/-- Every element of `A_inf` is power-bounded (an adic ring is bounded in itself). -/
theorem isPowerBounded_Ainf (x : Ainf p F) : IsPowerBounded x := by
  intro U hU
  obtain ⟨n, -, hn⟩ := (Ideal.hasBasis_nhds_zero_adic
    (Iinf p F (IsTateRing.pseudoUniformizer (A := F)))).mem_iff.mp hU
  refine ⟨_, (Ideal.hasBasis_nhds_zero_adic _).mem_of_mem (i := n) trivial, ?_⟩
  rintro z ⟨s, -, v, hv, rfl⟩
  exact hn (Ideal.mul_mem_left _ s hv)

omit [CharP F p] in
/-- `A_inf⁺ = A_inf` is a ring of integral elements: open, integrally closed, and
contained in the power-bounded subring (here: equal to it).

Source: standard for adic rings; matches the pair `Spa(A_inf, A_inf)` in
[Kedlaya-AWS, Def 3.1.5]. -/
theorem isAffinoidRing_Ainf : IsAffinoidRing (Ainf p F) := by
  refine ⟨?_, fun a _ => trivial, fun x _ => isPowerBounded_Ainf p F x⟩
  show IsOpen ((⊤ : Subring (Ainf p F)) : Set (Ainf p F))
  simp

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- Elementary comparison: `(p,[ϖ])^(2n) ⊆ (p)^n ⊔ ([ϖ])^n`. Each monomial `p^a [ϖ]^b`
with `a + b = 2n` has `a ≥ n` or `b ≥ n`. Together with the reverse inclusion
`(p)^n ⊔ ([ϖ])^n ⊇ (p,[ϖ])^n`-type bounds, this lets completeness be checked against the
"product" filtration.

Source: elementary; used implicitly whenever the literature says "(p,[ϖ])-adic = weak
topology", e.g. [Kedlaya-AWS, Def 3.1.2] vs [SW, §13.1]. -/
theorem Iinf_pow_two_mul_le (ϖ : PseudoUniformizer F) (n : ℕ) :
    Iinf p F ϖ ^ (2 * n) ≤
      Ideal.span {(p : Ainf p F)} ^ n ⊔ Ideal.span {teichPi p F ϖ} ^ n := by
  rw [Iinf, Ideal.span_insert, two_mul]
  exact Ideal.sup_pow_add_le_pow_sup_pow

/-- The auxiliary ideal `(p^r, [ϖ]^s) ⊆ A_inf`. The `(p,[ϖ])`-adic filtration is mutually
cofinal with the diagonal family `(p^n, [ϖ]^n)` (see `Iinf_pow_le_jointIdeal` /
`jointIdeal_le_Iinf_pow`), and joint-ideal congruences are exactly coefficientwise
`ϖ`-power congruences (`coeff_sub_mem_of_sub_mem_jointIdeal` /
`sub_mem_jointIdeal_of_coeff_sub_mem`) — the engine for separatedness and completeness. -/
private def jointIdeal (ϖ : PseudoUniformizer F) (r s : ℕ) : Ideal (Ainf p F) :=
  Ideal.span {(p : Ainf p F) ^ r, teichPi p F ϖ ^ s}

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
private theorem Iinf_pow_le_jointIdeal (ϖ : PseudoUniformizer F) (n : ℕ) :
    Iinf p F ϖ ^ (2 * n) ≤ jointIdeal p F ϖ n n := by
  rw [jointIdeal]
  refine (Iinf_pow_two_mul_le p F ϖ n).trans (sup_le ?_ ?_)
  · rw [Ideal.span_singleton_pow]
    exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (Set.mem_insert _ _))
  · rw [Ideal.span_singleton_pow]
    exact (Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
private theorem jointIdeal_le_Iinf_pow (ϖ : PseudoUniformizer F) (n : ℕ) :
    jointIdeal p F ϖ n n ≤ Iinf p F ϖ ^ n := by
  rw [jointIdeal, Iinf, Ideal.span_le]
  rintro x (rfl | rfl)
  · refine SetLike.mem_coe.mpr (Ideal.pow_mem_pow ?_ n)
    exact Ideal.subset_span (Set.mem_insert _ _)
  · refine SetLike.mem_coe.mpr (Ideal.pow_mem_pow ?_ n)
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

private theorem charP_quotient_span_pow (ϖ : PseudoUniformizer F) {s : ℕ} (hs : s ≠ 0) :
    CharP ((OF F) ⧸ Ideal.span {PseudoUniformizer.toOF F ϖ ^ s}) p := by
  refine CharP.quotient' p _ (fun x hx => ?_)
  by_cases hpx : p ∣ x
  · exact (CharP.cast_eq_zero_iff (OF F) p x).mpr hpx
  · exfalso
    have hbezout : ((Nat.gcd p x : ℕ) : ℤ) = p * Nat.gcdA p x + x * Nat.gcdB p x :=
      Nat.gcd_eq_gcd_ab p x
    rw [(Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpx] at hbezout
    have hunit : IsUnit ((x : OF F)) := by
      have hmul : ((x : ℕ) : OF F) * ((Nat.gcdB p x : ℤ) : OF F) = 1 := by
        have := congrArg (fun z : ℤ => ((z : ℤ) : OF F)) hbezout.symm
        push_cast at this
        rwa [CharP.cast_eq_zero (OF F) p, zero_mul, zero_add] at this
      exact (Units.mkOfMulEqOne _ _ hmul).isUnit
    have htop := Ideal.eq_top_of_isUnit_mem _ hx hunit
    have hϖs : IsUnit (PseudoUniformizer.toOF F ϖ ^ s) :=
      Ideal.span_singleton_eq_top.mp htop
    exact PseudoUniformizer.not_isUnit_toOF p F ϖ ((isUnit_pow_iff hs).mp hϖs)

private theorem frobeniusEquiv_symm_pow_apply_pow_mul (a : OF F) (i t : ℕ) :
    ((_root_.frobeniusEquiv (OF F) p).symm ^ i) (a ^ (p ^ i * t)) = a ^ t := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
      have hstep : (_root_.frobeniusEquiv (OF F) p).symm (a ^ (p ^ (i + 1) * t))
          = a ^ (p ^ i * t) := by
        have : a ^ (p ^ (i + 1) * t) = frobenius (OF F) p (a ^ (p ^ i * t)) := by
          rw [frobenius_def, ← pow_mul]
          congr 1
          ring
        rw [this, frobeniusEquiv_symm_apply_frobenius]
      rw [pow_succ, RingAut.mul_apply, hstep, ih]

private theorem coeff_sub_mem_of_sub_mem_jointIdeal (ϖ : PseudoUniformizer F)
    {x y : Ainf p F} {r s : ℕ} (hs : s ≠ 0) (h : x - y ∈ jointIdeal p F ϖ r s) :
    ∀ j < r, x.coeff j - y.coeff j ∈ Ideal.span {PseudoUniformizer.toOF F ϖ ^ s} := by
  intro j hj
  have hchar := charP_quotient_span_pow p F ϖ hs
  set π := Ideal.Quotient.mk (Ideal.span {PseudoUniformizer.toOF F ϖ ^ s}) with hπ
  rw [jointIdeal] at h
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp h
  rw [teichPi_pow] at huv
  have hmap : WittVector.map π (x - y) = WittVector.map π u * (p : WittVector p _) ^ r := by
    rw [← huv, map_add, map_mul, map_mul, map_pow, map_natCast, WittVector.map_teichmuller,
      show π (PseudoUniformizer.toOF F ϖ ^ s) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
      WittVector.teichmuller_zero, mul_zero, add_zero]
  have h0 : WittVector.truncate (p := p) r (WittVector.map π (x - y)) = 0 := by
    have hker : WittVector.map π (x - y) ∈ RingHom.ker (WittVector.truncate (p := p) r) := by
      rw [WittVector.mem_ker_truncate]
      intro i hi
      rw [hmap]
      exact WittVector.mul_pow_charP_coeff_zero _ hi
    rwa [RingHom.mem_ker] at hker
  rw [map_sub, map_sub, sub_eq_zero] at h0
  have hcoeff := congrArg (fun w => w.coeff ⟨j, hj⟩) h0
  simp only [WittVector.coeff_truncate, WittVector.map_coeff] at hcoeff
  exact Ideal.Quotient.eq.mp hcoeff

private theorem mem_jointIdeal_of_coeff_mem (ϖ : PseudoUniformizer F) {x : Ainf p F}
    {r s : ℕ}
    (hx : ∀ j < r, x.coeff j ∈ Ideal.span {PseudoUniformizer.toOF F ϖ ^ (s * p ^ (r - 1))}) :
    x ∈ jointIdeal p F ϖ r s := by
  rcases r with - | r
  · have h1 : (1 : Ainf p F) ∈ jointIdeal p F ϖ 0 s := by
      rw [jointIdeal]
      exact Ideal.subset_span (by simp)
    rw [(Ideal.eq_top_iff_one _).mpr h1]
    exact Submodule.mem_top
  simp only [Nat.add_sub_cancel] at hx
  have hgen : Ideal.span {WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ ^ s)} ≤
      jointIdeal p F ϖ (r + 1) s := by
    rw [← teichPi_pow]
    exact (Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hsum : (∑ i ∈ Finset.Iic r, WittVector.teichmuller p
      (((_root_.frobeniusEquiv (OF F) p).symm ^ i) (x.coeff i)) * (p : WittVector p _) ^ i) ∈
      jointIdeal p F ϖ (r + 1) s := by
    refine Ideal.sum_mem _ (fun i hi => ?_)
    have hir : i ≤ r := Finset.mem_Iic.mp hi
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (hx i (Nat.lt_succ_of_le hir))
    have hθ : ((_root_.frobeniusEquiv (OF F) p).symm ^ i) (x.coeff i)
        = ((_root_.frobeniusEquiv (OF F) p).symm ^ i) u *
          (PseudoUniformizer.toOF F ϖ ^ s) ^ p ^ (r - i) := by
      rw [← hu, map_mul]
      congr 1
      have harith : s * p ^ r = p ^ i * (s * p ^ (r - i)) := by
        rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hir]
      rw [harith, frobeniusEquiv_symm_pow_apply_pow_mul, ← pow_mul]
    rw [hθ, map_mul, map_pow]
    refine hgen (Ideal.mem_span_singleton.mpr ?_)
    exact ((dvd_pow_self _ (pow_ne_zero (r - i) (Nat.Prime.ne_zero Fact.out))).mul_left
      _).mul_right _
  obtain ⟨w, hw⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x r
  have hx' : x = (p : WittVector p (OF F)) ^ (r + 1) * w + _ := eq_add_of_sub_eq hw
  rw [hx']
  exact Ideal.add_mem _
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))) hsum

private theorem sub_mem_jointIdeal_of_coeff_sub_mem (ϖ : PseudoUniformizer F)
    {x y : Ainf p F} {r s : ℕ} (hs : s ≠ 0)
    (h : ∀ j < r,
      x.coeff j - y.coeff j ∈ Ideal.span {PseudoUniformizer.toOF F ϖ ^ (s * p ^ (r - 1))}) :
    x - y ∈ jointIdeal p F ϖ r s := by
  have hs' : s * p ^ (r - 1) ≠ 0 :=
    Nat.mul_ne_zero hs (pow_ne_zero _ (Nat.Prime.ne_zero Fact.out))
  have hchar := charP_quotient_span_pow p F ϖ hs'
  set π := Ideal.Quotient.mk
    (Ideal.span {PseudoUniformizer.toOF F ϖ ^ (s * p ^ (r - 1))}) with hπ
  have hQ : WittVector.truncate (p := p) r (WittVector.map π x)
      = WittVector.truncate (p := p) r (WittVector.map π y) := by
    ext i
    rw [WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.map_coeff,
      WittVector.map_coeff]
    exact Ideal.Quotient.eq.mpr (h i i.2)
  refine mem_jointIdeal_of_coeff_mem p F ϖ (fun j hj => ?_)
  have h0 : WittVector.truncate (p := p) r (WittVector.map π (x - y)) = 0 := by
    rw [map_sub, map_sub, hQ, sub_self]
  have hcoeff := congrArg (fun w => w.coeff ⟨j, hj⟩) h0
  simp only [WittVector.coeff_truncate, WittVector.map_coeff,
    TruncatedWittVector.coeff_zero] at hcoeff
  exact Ideal.Quotient.eq_zero_iff_mem.mp hcoeff

/-- `A_inf` is `(p,[ϖ])`-adically separated: an element of every `(p,[ϖ])^n` has every
Witt coefficient in every `ϖ^m·O_F` (via the joint-ideal engine), hence zero coefficients
by `ϖ`-adic separatedness of `O_F` (T103).

Source: [Kedlaya-AWS, Def 3.1.2] (completeness includes separatedness in the convention
of those notes, Convention 0.0.1). -/
theorem isHausdorff_Iinf (ϖ : PseudoUniformizer F) :
    IsHausdorff (Iinf p F ϖ) (Ainf p F) := by
  constructor
  intro x hx
  refine WittVector.ext (fun n => ?_)
  rw [WittVector.zero_coeff]
  refine (isHausdorff_span_toOF p F ϖ).haus (x.coeff n) (fun m => ?_)
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have hmem : x ∈ jointIdeal p F ϖ (m + n + 1) (m + n + 1) := by
    have h2 : x ∈ Iinf p F ϖ ^ (2 * (m + n + 1)) := by
      have := SModEq.sub_mem.mp (hx (2 * (m + n + 1)))
      rwa [sub_zero, Ideal.smul_eq_mul, Ideal.mul_top] at this
    exact Iinf_pow_le_jointIdeal p F ϖ _ h2
  have hsub : x - 0 ∈ jointIdeal p F ϖ (m + n + 1) (m + n + 1) := by simpa using hmem
  have hc := coeff_sub_mem_of_sub_mem_jointIdeal p F ϖ (by omega) hsub n (by omega)
  rw [WittVector.zero_coeff, sub_zero] at hc
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (by omega)) hc

/-- **`A_inf` is `(p,[ϖ])`-adically complete.** The summit of the ring-theoretic layer.

Proof plan (ROUTE FIXED after external review — decomposition L2.7a–d; do NOT attempt
the naive "per-digit Cauchy extraction" from the product filtration, it is a
non-theorem): (1) `A/p^r A ≅ W_r(O_F)` for perfect `O_F` (`p^r·A = V^r(A)`);
(2) each `W_r(O_F)` is `[ϖ]`-adically complete, via the digit sandwich
`(ϖ^{m·p^{r-1}} O_F)^r ⊆ [ϖ]^m·W_r(O_F) ⊆ (ϖ^m O_F)^r` and `isAdicComplete_span_toOF`
per digit; (3) assemble
`A ≅ lim_r A/p^r ≅ lim_r lim_s A/(p^r + [ϖ]^s) ≅ lim_n A/(p^n + [ϖ]^n)` (diagonal
cofinality in ℕ²), using mathlib's `WittVector.isAdicCompleteIdealSpanP` for the
`p`-direction; (4) transfer along `Iinf_pow_two_mul_le` to the `I`-adic filtration.

Source: [Kedlaya-AWS, Def 3.1.2]: "It is complete for the adic topology defined by the
inverse image of some ideal of definition of R⁺"; [SW, §13.1]; route per the gpt-5.6-sol
review (`.mathlib-quality/chatgpt-reply-fargues-fontaine-2026-07-24.md`). -/
theorem isAdicComplete_Iinf (ϖ : PseudoUniformizer F) :
    IsAdicComplete (Iinf p F ϖ) (Ainf p F) := by
  refine { toIsHausdorff := isHausdorff_Iinf p F ϖ, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  have hfm : ∀ {a b : ℕ}, a ≤ b → f a - f b ∈ Iinf p F ϖ ^ a := by
    intro a b hab
    have := SModEq.sub_mem.mp (hf hab)
    rwa [Ideal.smul_eq_mul, Ideal.mul_top] at this
  have hcoeff : ∀ (j : ℕ) {m n : ℕ}, m ≤ n → j < m →
      (f (2 * m)).coeff j - (f (2 * n)).coeff j ∈
        Ideal.span {PseudoUniformizer.toOF F ϖ ^ m} := by
    intro j m n hmn hj
    exact coeff_sub_mem_of_sub_mem_jointIdeal p F ϖ (by omega)
      (Iinf_pow_le_jointIdeal p F ϖ m (hfm (by omega))) j hj
  have hlim : ∀ j : ℕ, ∃ ℓ : OF F, ∀ m : ℕ,
      (f (2 * (m + j + 1))).coeff j ≡ ℓ
        [SMOD (Ideal.span {PseudoUniformizer.toOF F ϖ} ^ m • ⊤ : Ideal (OF F))] := by
    intro j
    refine (isAdicComplete_span_toOF p F ϖ).toIsPrecomplete.prec (fun {m n} hmn => ?_)
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (by omega))
      (hcoeff j (by omega : m + j + 1 ≤ n + j + 1) (by omega))
  choose ℓ hℓ using hlim
  refine ⟨WittVector.mk p ℓ, fun n => ?_⟩
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  set N := n * p ^ (n - 1) with hN
  set M := N + n + 1 with hM
  have h1 : f n - f (2 * M) ∈ Iinf p F ϖ ^ n := hfm (by omega)
  have h2 : f (2 * M) - WittVector.mk p ℓ ∈ Iinf p F ϖ ^ n := by
    refine jointIdeal_le_Iinf_pow p F ϖ n
      (sub_mem_jointIdeal_of_coeff_sub_mem p F ϖ hn.ne' (fun j hj => ?_))
    have h3 := hℓ j (M - j - 1)
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      show M - j - 1 + j + 1 = M by omega] at h3
    have h4 : (WittVector.mk p ℓ).coeff j = ℓ j := congrFun (WittVector.coeff_mk p ℓ) j
    rw [h4]
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (by omega)) h3
  simpa [sub_add_sub_cancel] using add_mem h1 h2

omit [CharP F p] in
/-- **`A_inf` admits a two-generated pair of definition.** The `I_inf`-adic pair on
`A_inf` has ideal generated by `p` and the Teichmüller lift `[ϖ♭]`, and its ring of
definition sits inside `A_inf⁺`. This is the input to Wedhorn 7.35(2) — quasi-compactness
of rational subsets of `Spa(A_inf, A_inf)`. -/
theorem exists_pairOfDefinition_Iinf :
    ∃ P : PairOfDefinition (Ainf p F), ∃ g₁ g₂ : P.A₀,
      P.I = Ideal.span ({g₁, g₂} : Set P.A₀) ∧
      (∀ x : P.A₀, (x : Ainf p F) ∈ (ringPlus (Ainf p F) : Subring (Ainf p F))) ∧
      Iinf p F (IsTateRing.pseudoUniformizer (A := F)) =
        Ideal.span ({(g₁ : Ainf p F), (g₂ : Ainf p F)} : Set (Ainf p F)) := by
  refine ⟨pairOfDefinition_ofAdic (Iinf p F (IsTateRing.pseudoUniformizer (A := F)))
      (Submodule.fg_span (Set.toFinite _)),
    ⟨(p : Ainf p F), trivial⟩, ⟨teichPi p F (IsTateRing.pseudoUniformizer (A := F)),
      trivial⟩, ?_, fun _ => trivial, ?_⟩
  · show idealToTop (Iinf p F (IsTateRing.pseudoUniformizer (A := F))) = _
    rw [show idealToTop (Iinf p F (IsTateRing.pseudoUniformizer (A := F)))
        = Ideal.map (Subring.topEquiv (R := Ainf p F)).symm.toRingHom
          (Ideal.span {(p : Ainf p F),
            teichPi p F (IsTateRing.pseudoUniformizer (A := F))}) from rfl,
      Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rfl
  · rfl

end FarguesFontaine

end
