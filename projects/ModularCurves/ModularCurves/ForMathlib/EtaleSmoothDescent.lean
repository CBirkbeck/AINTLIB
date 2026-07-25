/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.EtaleH1Descent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Smoothness descends along finite étale faithfully flat covers

**[T-YR-6 (c1-E)]** If `B` is a finite étale faithfully flat `A`-algebra which is
smooth over a noetherian base `k`, then `A` is smooth over `k`.

* the `Ω`-half: `Ω[B⁄k] ≃ B ⊗[A] Ω[A⁄k]` (étale base change), so flatness of
  `Ω[A⁄k]` descends and finite presentation upgrades it to projectivity;
* the `H¹`-half is `Algebra.subsingleton_h1Cotangent_of_etale_faithfullyFlat`;
* finite presentation of `A` over `k` is the Artin–Tate lemma.
-/

open TensorProduct

namespace Algebra

variable (k A B : Type*) [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- **[T-YR-6 (c1-E), `Ω`-half]** Projectivity of the module of differentials
descends along formally étale faithfully flat extensions. -/
theorem projective_kaehlerDifferential_of_formallyEtale_faithfullyFlat
    [Algebra.FormallyEtale A B] [Module.FaithfullyFlat A B]
    [Algebra.FinitePresentation k A] [Module.Projective B Ω[B⁄k]] :
    Module.Projective A Ω[A⁄k] := by
  haveI : Module.Flat B (B ⊗[A] Ω[A⁄k]) :=
    Module.Flat.of_linearEquiv
      (KaehlerDifferential.isBaseChange_of_formallyEtale k A B).equiv
  haveI : Module.Flat A Ω[A⁄k] :=
    Module.Flat.of_flat_tensorProduct (R := A) Ω[A⁄k] B
  exact Module.Flat.projective_of_finitePresentation

/-- **[T-YR-6 (c1-E)]** Smoothness descends along finite étale faithfully flat
extensions (over a noetherian base). -/
theorem smooth_of_etale_faithfullyFlat [IsNoetherianRing k]
    [Algebra.Etale A B] [Module.Finite A B] [Module.FaithfullyFlat A B]
    [Algebra.Smooth k B] : Algebra.Smooth k A := by
  haveI : Algebra.FiniteType k A :=
    ⟨fg_of_fg_of_fg (A := k) (B := A) (C := B)
      Algebra.FiniteType.out Module.Finite.fg_top
      (FaithfulSMul.algebraMap_injective A B)⟩
  haveI : Algebra.FinitePresentation k A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨⟨projective_kaehlerDifferential_of_formallyEtale_faithfullyFlat k A B,
    subsingleton_h1Cotangent_of_etale_faithfullyFlat k A B⟩, inferInstance⟩

end Algebra
