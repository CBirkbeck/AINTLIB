/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.AinfHuber
import «Adic spaces».ValuationAction
import Mathlib.RingTheory.WittVector.Frobenius

/-!
# The Frobenius action on A_inf and on Spa(A_inf, A_inf)

The Witt-vector Frobenius `φ : A_inf ≃+* A_inf` (an automorphism because `O_F` is
perfect) fixes `p`, sends `[ϖ]` to `[ϖ]^p`, and is a homeomorphism for the
`(p,[ϖ])`-adic topology. We package the resulting `φ^ℤ`-action as a
`MulSemiringAction (Multiplicative ℤ) (Ainf p F)` and transport it to an action on
`Spa(A_inf, A_inf)` by the project's `ValuationSpectrum` action machinery.

## Sources

* [BFHHLWY][bfhhlwy2018], Definition 2.1.1: "let φ : 𝒴 → 𝒴 be the Frobenius automorphism
  of 𝒴 induced by the natural q-Frobenius φ_q = φ^f ⊗ 1 on W_{E°}(F°)" (here `E = Q_p`,
  `q = p`, `f = 1`).
* [Scholze–Weinstein][sw2020], §12.2: "The Frobenius automorphism of O_{C♭} induces an
  automorphism φ of Spa A_inf, which preserves 𝒴".
* mathlib: `WittVector.frobeniusEquiv`, `WittVector.frobenius_eq_map_frobenius`,
  `WittVector.map_teichmuller`.
-/

open TopologicalRing ValuationSpectrum WittVector

universe u

attribute [local instance] IsLinearTopology.nonarchimedeanAddGroup

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [IsLinearTopology F F] [IsPerfectoidField p F] [CharP F p]

/-- The Witt-vector Frobenius of `A_inf = W(O_F)`, an automorphism since `O_F` is
perfect.

Source: [BFHHLWY, Def 2.1.1] (the q-Frobenius, `q = p`); mathlib
`WittVector.frobeniusEquiv`. -/
def frob : Ainf p F ≃+* Ainf p F :=
  WittVector.frobeniusEquiv p (OF F)

/-- `φ` fixes the element `p` (it fixes every natural number cast). -/
theorem frob_natCast (n : ℕ) : frob p F (n : Ainf p F) = n := by sorry

/-- `φ([ϖ]) = [ϖ]^p`: Frobenius raises Teichmüller lifts to their `p`-th power.

Via `frobenius_eq_map_frobenius` (characteristic `p`) and `map_teichmuller`:
`φ([x]) = [x^p] = [x]^p`.

Source: [SW, §12.2] (κ∘φ = pκ is the shadow of this identity); mathlib lemmas cited in
the module docstring. -/
theorem frob_teichPi (ϖ : PseudoUniformizer F) :
    frob p F (teichPi p F ϖ) = teichPi p F ϖ ^ p := by sorry

/-- `φ` maps `I^n` into `I^n` (it fixes `p` and multiplies the `[ϖ]`-generator into a
power), hence is continuous. -/
theorem map_frob_Iinf_pow_le (ϖ : PseudoUniformizer F) (n : ℕ) :
    (Iinf p F ϖ ^ n).map (frob p F : Ainf p F →+* Ainf p F) ≤ Iinf p F ϖ ^ n := by
  sorry

/-- `I^((p+1)·n)` is contained in the image of `I^n` under `φ`, which gives continuity
of `φ⁻¹`. Exponent bookkeeping: `φ(I^n)` is the ideal `(p, [ϖ]^p)^n`, and a monomial
`p^a [ϖ]^b` with `a + b = (p+1)n` has either `a ≥ n`, or `b ≥ p·n` so that
`[ϖ]^b ∈ ([ϖ]^p)^n`. (The naive bound `2n` fails for `p ≥ 3` — caught by the
adversarial pass, see decomposition L3.3.) -/
theorem Iinf_pow_succ_mul_le_map_frob (ϖ : PseudoUniformizer F) (n : ℕ) :
    Iinf p F ϖ ^ ((p + 1) * n) ≤
      (Iinf p F ϖ ^ n).map (frob p F : Ainf p F →+* Ainf p F) := by
  sorry

/-- `φ` is continuous for the `(p,[ϖ])`-adic topology. -/
theorem continuous_frob : Continuous (frob p F) := by sorry

/-- `φ⁻¹` is continuous for the `(p,[ϖ])`-adic topology. -/
theorem continuous_frob_symm : Continuous (frob p F).symm := by sorry

/-- The `φ^ℤ`-action on `A_inf`: the group `Multiplicative ℤ` acts by ring automorphisms
through `k ↦ φ^k`.

Source: [BFHHLWY, Def 2.1.1] (the group `φ^ℤ` acting on `𝒴`). -/
instance instMulSemiringActionAinf :
    MulSemiringAction (Multiplicative ℤ) (Ainf p F) :=
  MulSemiringAction.compHom _ (zpowersHom (RingAut (Ainf p F)) (frob p F))

/-- Unfolding lemma for the action: `k • x = φ^k x`. -/
theorem ofAdd_zsmul_def (k : ℤ) (x : Ainf p F) :
    (Multiplicative.ofAdd k) • x = ((frob p F ^ k : RingAut (Ainf p F)) : _ ≃+* _) x := by
  sorry

/-- Each `φ^k` acts continuously: the action is by homeomorphisms. -/
instance instContinuousConstSMulAinf :
    ContinuousConstSMul (Multiplicative ℤ) (Ainf p F) := by sorry

/-- The `φ^ℤ`-action preserves `Spa(A_inf, A_inf)` (the plus-subring `⊤` is stable under
any ring automorphism), so `Multiplicative ℤ` acts on the adic spectrum.

Source: [SW, §12.2]: "The Frobenius automorphism of O_{C♭} induces an automorphism φ of
Spa A_inf". -/
theorem smul_mem_spa_Ainf (g : Multiplicative ℤ) {v : Spv (Ainf p F)}
    (hv : v ∈ Spa (Ainf p F) (ringPlus (Ainf p F))) :
    g • v ∈ Spa (Ainf p F) (ringPlus (Ainf p F)) := by sorry

end FarguesFontaine

end
