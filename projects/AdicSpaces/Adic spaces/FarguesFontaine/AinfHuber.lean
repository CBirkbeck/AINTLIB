/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.PerfectoidFieldCharP
import «Adic spaces».HuberRings
import «Adic spaces».AffinoidRings
import «Adic spaces».AdicConvergence
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.Teichmuller
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

attribute [local instance] IsLinearTopology.nonarchimedeanAddGroup

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [IsLinearTopology F F] [IsPerfectoidField p F] [CharP F p]

/-- `A_inf = W(O_F)`, the ring of `p`-typical Witt vectors of the ring of integers of a
perfectoid field `F` of characteristic `p`.

Source: [BFHHLWY, Def 2.1.1] with `E = Q_p` (there `W_{E°}(F°) = W(F°)`);
[Kedlaya-AWS, Def 3.1.2]. -/
abbrev Ainf : Type u := WittVector p (OF F)

/-- The Teichmüller lift `[ϖ] ∈ A_inf` of the pseudo-uniformizer.

Source: [BFHHLWY, Def 2.1.1] (the element `[ϖ]`); [SW, §12.2] (the element `[p♭]`). -/
def teichPi (ϖ : PseudoUniformizer F) : Ainf p F :=
  WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ)

/-- Teichmüller lifts of powers: `[ϖ]^n = [ϖ^n]`. This is what makes rational exponents
in the window inequalities (Kedlaya-AWS, Rem. 3.1.9) clearable to integer powers. -/
theorem teichPi_pow (ϖ : PseudoUniformizer F) (n : ℕ) :
    teichPi p F ϖ ^ n = WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ ^ n) := by
  sorry

/-- `[ϖ] ≠ 0` in `A_inf`. -/
theorem teichPi_ne_zero (ϖ : PseudoUniformizer F) : teichPi p F ϖ ≠ 0 := by sorry

/-- The ideal `I = (p, [ϖ]) ⊆ A_inf` defining the topology.

Source: [SW, §13.1] "(p, [p♭])-adic topology". -/
def Iinf (ϖ : PseudoUniformizer F) : Ideal (Ainf p F) :=
  Ideal.span {(p : Ainf p F), teichPi p F ϖ}

/-- The `(p,[ϖ])`-adic topology on `A_inf`, using the canonical pseudo-uniformizer of the
Tate ring `F`. By `isAdic_Iinf` below, the topology does not depend on this choice.

Source: [SW, §13.1]; [Kedlaya-AWS, Def 3.1.2]. -/
instance instTopologicalSpaceAinf : TopologicalSpace (Ainf p F) :=
  (Iinf p F (IsTateRing.pseudoUniformizer (A := F))).adicTopology

/-- `A_inf` is a topological ring for the `(p,[ϖ])`-adic topology. -/
instance instIsTopologicalRingAinf : IsTopologicalRing (Ainf p F) := by sorry

/-- The topology on `A_inf` is `(p,[ϖ])`-adic for EVERY pseudo-uniformizer `ϖ` (not just
the canonical one used to define the instance). In particular the construction is
independent of the choice of `ϖ`.

Proof idea: for pseudo-uniformizers `ϖ, ϖ'` one has `ϖ'^n ∈ ϖ·O_F` for some `n` (both are
topologically nilpotent units), hence `[ϖ']^n = [ϖ'^n] ∈ [ϖ]·A_inf`, so the two ideals
generate mutually cofinal filtrations.

Source: [Kedlaya-AWS, §11.2-style remark]: "this is independent of the choice of ϖ, as
for any other choice ϖ', there is some n such that ϖ | (ϖ')^n and ϖ' | ϖ^n" (stated there
for the analogous locus; the same divisibility argument applies to the filtration). -/
theorem isAdic_Iinf (ϖ : PseudoUniformizer F) : IsAdic (Iinf p F ϖ) := by sorry

/-- `A_inf` is a Huber ring: `(A_inf, (p,[ϖ]))` is a pair of definition — the ring itself
is open, and the ideal is finitely generated (two generators) with adic topology.

Source: [Kedlaya-AWS, Def 3.1.2] (A_inf with an adic topology defined by a finitely
generated ideal); [SW, §13.1]. -/
instance instIsHuberRingAinf : IsHuberRing (Ainf p F) := by sorry

/-- `A_inf⁺ = A_inf`: the plus-subring is the whole ring.

Source: [Kedlaya-AWS, Rem. 3.1.9 / Def 3.1.5] (the pair is `Spa(A_inf, A_inf)`);
[BFHHLWY, Def 2.1.1] writes `Spa(W_{E°}(F°))`, i.e. the self-pair. -/
instance instPlusSubringAinf : PlusSubring (Ainf p F) where
  toSubring := ⊤

/-- Every element of `A_inf` is power-bounded (an adic ring is bounded in itself). -/
theorem isPowerBounded_Ainf (x : Ainf p F) : IsPowerBounded x := by sorry

/-- `A_inf⁺ = A_inf` is a ring of integral elements: open, integrally closed, and
contained in the power-bounded subring (here: equal to it).

Source: standard for adic rings; matches the pair `Spa(A_inf, A_inf)` in
[Kedlaya-AWS, Def 3.1.5]. -/
theorem isAffinoidRing_Ainf : IsAffinoidRing (Ainf p F) := by sorry

/-- Elementary comparison: `(p,[ϖ])^(2n) ⊆ (p)^n ⊔ ([ϖ])^n`. Each monomial `p^a [ϖ]^b`
with `a + b = 2n` has `a ≥ n` or `b ≥ n`. Together with the reverse inclusion
`(p)^n ⊔ ([ϖ])^n ⊇ (p,[ϖ])^n`-type bounds, this lets completeness be checked against the
"product" filtration.

Source: elementary; used implicitly whenever the literature says "(p,[ϖ])-adic = weak
topology", e.g. [Kedlaya-AWS, Def 3.1.2] vs [SW, §13.1]. -/
theorem Iinf_pow_two_mul_le (ϖ : PseudoUniformizer F) (n : ℕ) :
    Iinf p F ϖ ^ (2 * n) ≤
      Ideal.span {(p : Ainf p F)} ^ n ⊔ Ideal.span {teichPi p F ϖ} ^ n := by
  sorry

/-- `A_inf` is `(p,[ϖ])`-adically separated.

Source: [Kedlaya-AWS, Def 3.1.2] (completeness includes separatedness in the convention
of those notes, Convention 0.0.1); levelwise from `ϖ`-adic separatedness of `O_F` and
`p`-adic separatedness of `W(O_F)` (mathlib `WittVector.isAdicCompleteIdealSpanP`). -/
theorem isHausdorff_Iinf (ϖ : PseudoUniformizer F) :
    IsHausdorff (Iinf p F ϖ) (Ainf p F) := by sorry

/-- **`A_inf` is `(p,[ϖ])`-adically complete.** The summit of the ring-theoretic layer.

Proof plan (to be refined in the decomposition): reduce along `Iinf_pow_two_mul_le` to
completeness for the filtration `(p)^n ⊔ ([ϖ])^n`; a Cauchy sequence for this filtration
has, in each Witt coordinate `i`, a `ϖ`-adically Cauchy sequence in `O_F` (Teichmüller
multiplication acts coordinatewise: `([ϖ]·y).coeff i = ϖ^{p^i}·y.coeff i`), which
converges by `isAdicComplete_span_toOF`; the coordinatewise limit is the `(p,[ϖ])`-adic limit,
using mathlib's `p`-adic completeness `WittVector.isAdicCompleteIdealSpanP` to control the
`p`-direction.

Source: [Kedlaya-AWS, Def 3.1.2]: "It is complete for the adic topology defined by the
inverse image of some ideal of definition of R⁺"; [SW, §13.1]. -/
theorem isAdicComplete_Iinf (ϖ : PseudoUniformizer F) :
    IsAdicComplete (Iinf p F ϖ) (Ainf p F) := by sorry

end FarguesFontaine

end
