/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PerfectoidRing
import «Adic spaces».PseudoUniformizer
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Perfect

/-!
# Perfectoid fields of characteristic p: the base field of the Fargues--Fontaine curve

Let `F` be a perfectoid field of characteristic `p` (the project's `IsPerfectoidField p F`
with `CharP F p`), with ring of integers `O_F = F°` (power-bounded elements) and a
pseudo-uniformizer `ϖ`. This file establishes the facts about `O_F` needed to build
`A_inf = W(O_F)` in `AinfHuber.lean`:

* `O_F` is an integral domain of characteristic `p`;
* `O_F` is a perfect ring (`PerfectRing (OF F) p`);
* the `ϖ`-adic filtration `ϖ^n O_F` is a basis of neighbourhoods of `0` in the subspace
  topology, and `O_F` is `ϖ`-adically separated and complete
  (`IsHausdorff`/`IsAdicComplete (Ideal.span {ϖ}) (OF F)`).

## Sources

* [BFHHLWY, *Extensions of vector bundles on the Fargues–Fontaine curve*][bfhhlwy2018],
  Definition 2.1.1 (the setting: `F/F_q` perfectoid, `F°`, pseudouniformizer `ϖ`).
* [B. Bhatt, *Lecture notes for a class on perfectoid spaces*][bhatt679], §3.1
  (Example 3.1.2(3): a nonarchimedean field of characteristic `p` is perfectoid iff it is
  perfect; Corollary 3.2.3 for the `t`-adic completeness pattern).
* [Kedlaya, *Sheaves, stacks, and shtukas* (AWS 2017)][kedlaya-aws], Hypothesis 3.1.1.
-/

open TopologicalRing ValuationSpectrum

universe u

attribute [local instance] IsLinearTopology.nonarchimedeanAddGroup

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [IsLinearTopology F F] [IsPerfectoidField p F] [CharP F p]

/-- The ring of integers `O_F = F°` of a perfectoid field, as a type.

This is the subtype of the power-bounded subring; it is a commutative ring via the
`Subring` instance. -/
abbrev OF : Type u := ↥(powerBoundedSubring.toSubring F)

/-- A pseudo-uniformizer `ϖ : Fˣ`, viewed as an element of `O_F`.

A pseudo-uniformizer is a topologically nilpotent unit; topologically nilpotent elements
are power-bounded, so `ϖ` lies in `F° = O_F`.

Source: [BFHHLWY, Def 2.1.1] ("pseudouniformizer ϖ", an element of `F°`). -/
def PseudoUniformizer.toOF (ϖ : PseudoUniformizer F) : OF F :=
  ⟨((ϖ.val : Fˣ) : F), (PseudoUniformizer.isTopologicallyNilpotent ϖ).isPowerBounded⟩

/-- `O_F` is an integral domain (a subring of a field). -/
instance : IsDomain (OF F) := by infer_instance

/-- `O_F` has characteristic `p` (a subring of a field of characteristic `p`).

Source: immediate from the setting of [BFHHLWY, Def 2.1.1]. -/
instance instCharPOF : CharP (OF F) p where
  cast_eq_zero_iff n := by
    rw [← CharP.cast_eq_zero_iff F p n]
    exact ⟨fun h => by simpa using congrArg (fun x : OF F => (x : F)) h,
      fun h => Subtype.ext (by push_cast; exact h)⟩

/-- The Frobenius `x ↦ x^p` is surjective on `O_F` (`O_F` is semiperfect): the
characteristic-`p` content of the perfectoid condition.

Source: [Bhatt, §3.1, Example 3.1.2(3)]: "Let K be a NA field of characteristic p. Then
K is perfectoid if and only if K is perfect. In this case, semiperfectness of K° implies
its perfectness". -/
theorem frobenius_surjective_OF : Function.Surjective (frobenius (OF F) p) := by
  intro x
  obtain ⟨y, hy, z, -, hxyz⟩ := IsPerfectoidRing.frobenius_surj (p := p) (x : F) x.2
  exact ⟨⟨y, hy⟩, Subtype.ext (by simp [frobenius_def, hxyz])⟩

/-- `O_F` is a perfect ring: the Frobenius is bijective.

Injectivity holds because `O_F` is a domain of characteristic `p`; surjectivity is
`frobenius_surjective_OF`.

Source: [Bhatt, §3.1, Example 3.1.2(3)], as above. -/
instance instPerfectRingOF : PerfectRing (OF F) p :=
  PerfectRing.ofSurjective _ p (frobenius_surjective_OF p F)

/-- The pseudo-uniformizer is nonzero in `O_F`. -/
theorem PseudoUniformizer.toOF_ne_zero (ϖ : PseudoUniformizer F) :
    PseudoUniformizer.toOF F ϖ ≠ 0 := by
  intro h
  exact ((ϖ.val : Fˣ)).ne_zero (by simpa [PseudoUniformizer.toOF] using congrArg Subtype.val h)

/-- Each `ϖ^n O_F` is a neighbourhood of `0` in `O_F` (subspace topology from `F`).

This is the standard fact that for a Tate ring with ring of definition `F°` and
pseudo-uniformizer `ϖ`, the sets `ϖ^n F°` form a neighbourhood basis of `0`.

Source: [Wedhorn, *Adic Spaces*, §5.30/6.11-style standard facts on Tate rings]; used
implicitly in [Kedlaya-AWS, Hyp. 3.1.1 and Rem. 3.1.9]. -/
theorem span_toOF_pow_mem_nhds_zero (ϖ : PseudoUniformizer F) (n : ℕ) :
    ((Ideal.span {PseudoUniformizer.toOF F ϖ} ^ n : Ideal (OF F)) : Set (OF F)) ∈
      nhds (0 : OF F) := by sorry

/-- Every neighbourhood of `0` in `O_F` contains some `ϖ^n O_F`.

This is topological nilpotence of `ϖ` plus boundedness of `O_F` (uniformity of `F`):
`ϖ^n · F° → 0` uniformly.

Source: standard Tate-ring fact, as for `span_toOF_pow_mem_nhds_zero`. -/
theorem exists_span_toOF_pow_subset_nhds (ϖ : PseudoUniformizer F) {U : Set (OF F)}
    (hU : U ∈ nhds (0 : OF F)) :
    ∃ n : ℕ,
      ((Ideal.span {PseudoUniformizer.toOF F ϖ} ^ n : Ideal (OF F)) : Set (OF F)) ⊆ U := by
  sorry

/-- `O_F` is `ϖ`-adically separated: `⋂ n, ϖ^n O_F = 0`.

From `exists_span_toOF_pow_subset_nhds` and the fact that `F` (hence `O_F`) is T0 as a
topological group, the intersection of the `ϖ^n O_F` is contained in every neighbourhood
of `0`, hence is `0`.

Source: [Bhatt, Cor. 3.2.3] pattern (t-adic topology on `K°` is separated and complete). -/
theorem isHausdorff_span_toOF (ϖ : PseudoUniformizer F) :
    IsHausdorff (Ideal.span {PseudoUniformizer.toOF F ϖ}) (OF F) := by sorry

/-- `O_F` is `ϖ`-adically complete.

A `ϖ`-adic Cauchy sequence is Cauchy for the subspace uniformity (by
`span_toOF_pow_mem_nhds_zero`), hence converges in `F` by completeness; the limit is
power-bounded (a limit of a bounded set in a uniform Tate ring), i.e. lies in `O_F`, and
the convergence is `ϖ`-adic by `exists_span_toOF_pow_subset_nhds`.

Source: [Bhatt, Cor. 3.2.3]: "K°♭ is t-adically complete, and the t-adic topology
coincides with the given topology" — the same statement for a char-p perfectoid field
directly. -/
theorem isAdicComplete_span_toOF (ϖ : PseudoUniformizer F) :
    IsAdicComplete (Ideal.span {PseudoUniformizer.toOF F ϖ}) (OF F) := by sorry

end FarguesFontaine

end
