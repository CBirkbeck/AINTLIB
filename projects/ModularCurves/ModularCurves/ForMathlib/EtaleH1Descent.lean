/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.StandardEtaleH1
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Vanishing of `H¹` descends along étale faithfully flat maps

**[T-YR-6 (c1-D)]** If `B` is an étale faithfully flat `A`-algebra with
`H¹(L_{B/k}) = 0`, then `H¹(L_{A/k}) = 0`.

Proof: `B` is Zariski-locally standard étale over `A`
(`Algebra.IsEtaleAt.exists_isStandardEtale`), and on each such piece `C = B[1/f]`
the base-change isomorphism `C ⊗[A] H¹(L_{A/k}) ≃ H¹(L_{C/k}) = 0`
(`Algebra.tensorH1CotangentOfIsStandardEtale`) forces every element of
`B ⊗[A] H¹(L_{A/k})` to be killed by a power of `f`. As the `f`'s escape every
maximal ideal, the annihilator is the unit ideal, so `B ⊗[A] H¹(L_{A/k}) = 0`,
and faithful flatness descends the vanishing to `A`.
-/

open TensorProduct

namespace Algebra

variable (k A B : Type*) [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- (Implementation) `H¹` of a localization of `B` vanishes when `H¹` of `B` does. -/
lemma subsingleton_h1Cotangent_localization (C : Type*) [CommRing C] [Algebra B C]
    [Algebra k C] [IsScalarTower k B C] (M : Submonoid B) [IsLocalization M C]
    [Subsingleton (H1Cotangent k B)] : Subsingleton (H1Cotangent k C) := by
  rw [subsingleton_iff_forall_eq 0]
  intro x
  obtain ⟨⟨m, s⟩, rfl⟩ :=
    IsLocalizedModule.mk'_surjective M (H1Cotangent.map k k B C) x
  rw [Function.uncurry_apply_pair, Subsingleton.elim m 0,
    IsLocalizedModule.mk'_zero]

/-- **[T-YR-6 (c1-D)]** Vanishing of `H¹` of the cotangent complex descends along
étale faithfully flat extensions. -/
theorem subsingleton_h1Cotangent_of_etale_faithfullyFlat
    [Algebra.Etale A B] [Module.FaithfullyFlat A B]
    [Subsingleton (H1Cotangent k B)] :
    Subsingleton (H1Cotangent k A) := by
  rw [← Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B,
    subsingleton_iff_forall_eq 0]
  intro x
  -- the annihilator of `x` in `B`
  set J : Ideal B := LinearMap.ker
    (LinearMap.toSpanSingleton B (B ⊗[A] H1Cotangent k A) x) with hJ
  have hJtop : J = ⊤ := by
    by_contra hne
    obtain ⟨n, hn, hJn⟩ := Ideal.exists_le_maximal J hne
    haveI : n.IsPrime := hn.isPrime
    haveI : FormallyEtale A (Localization.AtPrime n) :=
      FormallyEtale.comp A B (Localization.AtPrime n)
    obtain ⟨f, hfn, hf⟩ := IsEtaleAt.exists_isStandardEtale (R := A) n
    -- the standard étale piece `C = B[1/f]`
    haveI hC : Subsingleton (Localization.Away f ⊗[A] H1Cotangent k A) := by
      haveI : Subsingleton (H1Cotangent k (Localization.Away f)) :=
        subsingleton_h1Cotangent_localization k B (Localization.Away f)
          (Submonoid.powers f)
      exact (tensorH1CotangentOfIsStandardEtale k A
        (Localization.Away f)).toEquiv.subsingleton
    -- hence `1 ⊗ x = 0` in `C ⊗[B] (B ⊗[A] H¹)`, so a power of `f` kills `x`
    haveI : Subsingleton (Localization.Away f ⊗[B] (B ⊗[A] H1Cotangent k A)) :=
      @Equiv.subsingleton _ _
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A B
          (Localization.Away f) (Localization.Away f)
          (H1Cotangent k A)).toEquiv hC
    obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
      (TensorProduct.mk B (Localization.Away f)
        (B ⊗[A] H1Cotangent k A) 1)).mp (Subsingleton.elim _ _)
    obtain ⟨j, rfl⟩ := hs
    have hmem : f ^ j ∈ J := by
      simpa [hJ, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
        Submonoid.smul_def] using hsx
    exact hfn (hn.isPrime.mem_of_pow_mem j (hJn hmem))
  have h1 : (1 : B) ∈ J := hJtop ▸ Submodule.mem_top
  simpa [hJ, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] using h1

end Algebra
