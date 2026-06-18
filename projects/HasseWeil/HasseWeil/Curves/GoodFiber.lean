/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.GenericFiber
import HasseWeil.Curves.PushforwardDivisor
import HasseWeil.Curves.RamificationFinite

/-!
# The good fibre of a separable curve map has `deg φ` points (ROUTE-W, ticket W-3, layer 1)

For a curve map `φ : C₁ → C₂` over an algebraically closed field with a coordinate-ring
witness `cd : φ.CoordHom`, module-finiteness of the coordinate extension and separability
of the function-field extension, **all but finitely many fibres of the point map
`toPointMap cd` have exactly `φ.degree` elements** (Silverman II.2.6(b) + II.2.7):

* `CurveMap.exists_finite_ramified_locus_coordHom` — the W-1/W-2 different-ideal bound,
  instantiated at the coordinate-ring pair `(F[C₂], F[C₁])`: away from a finite set of
  primes of `F[C₂]` every ramification index is `1`.  (`F[C₁]` *is* the integral closure
  of `F[C₂]` in `K(C₁)` by `IsIntegralClosure.of_isIntegrallyClosed`, so no localization
  is needed.)
* `CurveMap.inertiaDeg_eq_one_of_mem_primesOver` — over `[IsAlgClosed F]` every residue
  degree is `1` (both residue fields are `F`).
* `CurveMap.nat_card_toPointMap_fiber_eq_card_primesOverFinset` — the point-fibre ↔
  prime-fibre dictionary at every smooth point, via `smoothPoint ↔ MaxSpec`
  (`exists_smoothPoint_of_isMaximal` / `maximalIdealAt_injective`).
* `CurveMap.exists_good_fiber_card_eq_degree` — the headline: a good fibre of
  cardinality `φ.degree` exists avoiding any prescribed finite set of points.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6(b), II.2.7 (for III.4.10c).
-/

namespace HasseWeil.Curves.CurveMap

variable {F : Type*} [Field F] {C₁ C₂ : SmoothPlaneCurve F}
  [C₁.toAffine.IsElliptic] [C₂.toAffine.IsElliptic]
  [IsIntegrallyClosed C₁.CoordinateRing] [IsIntegrallyClosed C₂.CoordinateRing]

set_option synthInstance.maxHeartbeats 100000 in
-- The OreLocalization-derived scalar tower `F[C₂] → F[C₁] → K(C₁)` and the
-- integral-closure instances are heartbeat-heavy, exactly as in
-- `PushforwardDivisor.finiteDimensional_functionField` (same bumps).
set_option maxHeartbeats 800000 in
/-- **W-2 at the coordinate-ring pair**: away from a finite set of primes of `F[C₂]`,
every prime of `F[C₁]` lying over (along `cd.toAlgebra`) is unramified.  This is
`RamificationFinite.exists_finite_ramification_locus` at `(A, K, L, B) =
(F[C₂], K(C₂), K(C₁), F[C₁])`; the `IsIntegralClosure` instance is
`IsIntegralClosure.of_isIntegrallyClosed` (the `PushforwardDivisor` pattern), so the
good-affine-locus localization of `GoodAffineLocus.lean` is not needed. -/
theorem exists_finite_ramified_locus_coordHom [IsAlgClosed F]
    (φ : CurveMap C₁ C₂) (cd : φ.CoordHom)
    (hsepAlg : @Algebra.IsSeparable C₂.FunctionField C₁.FunctionField _ _ φ.toAlgebra) :
    ∃ S : Set (Ideal C₂.CoordinateRing), S.Finite ∧
      ∀ q : Ideal C₂.CoordinateRing, q ∉ S →
        ∀ P : Ideal C₁.CoordinateRing, P.IsPrime →
          (letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra;
            P.under C₂.CoordinateRing = q) →
          letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
          Ideal.ramificationIdx q P = 1 := by
  have hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      cd.toAlgebra.toModule := by
    exact cd.module_finite
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR := hfin
  letI algFF : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
  -- the `A → B → L` tower is the OreLocalization-derived one (as in `PushforwardDivisor`)
  haveI tower2 : IsScalarTower C₂.CoordinateRing C₁.CoordinateRing C₁.FunctionField :=
    inferInstance
  -- the `A → K → L` tower, from `cd.compat` (the `tower1` dance of `PushforwardDivisor`)
  haveI tower1 : IsScalarTower C₂.CoordinateRing C₂.FunctionField C₁.FunctionField := by
    refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
    rw [Algebra.smul_def]
    change φ.pullback ((algebraMap C₂.CoordinateRing C₂.FunctionField) r) * x = r • x
    rw [cd.compat r, ← IsScalarTower.algebraMap_smul C₁.CoordinateRing r x,
      ← Algebra.smul_def]
    rfl
  haveI hint : Algebra.IsIntegral C₂.CoordinateRing C₁.CoordinateRing :=
    Algebra.IsIntegral.of_finite C₂.CoordinateRing C₁.CoordinateRing
  haveI hicl : IsIntegralClosure C₁.CoordinateRing C₂.CoordinateRing C₁.FunctionField :=
    IsIntegralClosure.of_isIntegrallyClosed C₁.CoordinateRing C₂.CoordinateRing
      C₁.FunctionField
  haveI hfd : FiniteDimensional C₂.FunctionField C₁.FunctionField :=
    finiteDimensional_functionField φ cd
  haveI := hsepAlg
  exact RamificationFinite.exists_finite_ramification_locus
    C₂.CoordinateRing C₂.FunctionField C₁.FunctionField C₁.CoordinateRing

set_option synthInstance.maxHeartbeats 100000 in
-- Whnf-reducing the `letI`/`haveI`-prefixed statement of
-- `inertiaDeg_maximalIdealAt_toPointMap` against the pinned coordinate algebra
-- exceeds the default budget; same bumps as its home file `PushforwardDivisor`.
set_option maxHeartbeats 800000 in
/-- **Residue degrees are trivial over `K̄`**: every prime of `F[C₁]` over the maximal
ideal of a smooth point of `C₂` has inertia degree `1`.  This is the inline `hinertia`
argument of `PushforwardDivisor.relNorm_maximalIdealAt_eq`, extracted: a prime over
`m_Q` is maximal, hence `maximalIdealAt P''` for a smooth point `P''`
(`exists_smoothPoint_of_isMaximal`), and `inertiaDeg_maximalIdealAt_toPointMap`
computes its residue degree. -/
theorem inertiaDeg_eq_one_of_mem_primesOver [IsAlgClosed F]
    (φ : CurveMap C₁ C₂) (cd : φ.CoordHom) (Q : C₂.SmoothPoint) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    ∀ P' ∈ (C₂.maximalIdealAt Q).primesOver C₁.CoordinateRing,
      Ideal.inertiaDeg (C₂.maximalIdealAt Q) P' = 1 := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  intro P' hP'
  obtain ⟨hP'prime, hP'lies⟩ := hP'
  haveI : P'.IsPrime := hP'prime
  haveI : P'.LiesOver (C₂.maximalIdealAt Q) := hP'lies
  have hQ0 : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  have hP'_ne_bot : P' ≠ ⊥ := by
    intro h
    apply hQ0
    rw [hP'lies.over, h, Ideal.under_bot]
  haveI hP'max : P'.IsMaximal := Ideal.IsPrime.isMaximal hP'prime hP'_ne_bot
  obtain ⟨P'', hP''⟩ := C₁.exists_smoothPoint_of_isMaximal hP'max
  have h1 : C₂.maximalIdealAt (toPointMap cd P'') =
      (C₁.maximalIdealAt P'').under C₂.CoordinateRing :=
    (maximalIdealAt_liesOver_toPointMap φ cd P'').over
  rw [hP''] at h1
  have hpeq : C₂.maximalIdealAt (toPointMap cd P'') = C₂.maximalIdealAt Q :=
    h1.trans hP'lies.over.symm
  have hid : Ideal.inertiaDeg (C₂.maximalIdealAt (toPointMap cd P''))
      (C₁.maximalIdealAt P'') = 1 := inertiaDeg_maximalIdealAt_toPointMap φ cd P''
  rw [hpeq, hP''] at hid
  exact hid

set_option synthInstance.maxHeartbeats 100000 in
-- Same instance-synthesis bumps as `exists_finite_ramified_locus_coordHom` above: the
-- `coe_primesOverFinset` conversion whnf-reduces the pinned coordinate-algebra instances.
set_option maxHeartbeats 800000 in
/-- **The point-fibre ↔ prime-fibre dictionary**: at every smooth point `Q` of `C₂`, the
fibre of the coordinate point map `toPointMap cd` over `Q` is in bijection with the
primes of `F[C₁]` over `m_Q` — forward by `P ↦ m_P` (`maximalIdealAt_liesOver_toPointMap`
+ injectivity), backward by `exists_smoothPoint_of_isMaximal`. -/
theorem nat_card_toPointMap_fiber_eq_card_primesOverFinset [IsAlgClosed F]
    (φ : CurveMap C₁ C₂) (cd : φ.CoordHom) (Q : C₂.SmoothPoint) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
    Nat.card {P : C₁.SmoothPoint // toPointMap cd P = Q} =
      (IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing).card := by
  classical
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  have hQ0 : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  haveI hQmax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  -- forward map `P ↦ m_P` lands in the set of primes over `m_Q`
  have hmem : ∀ P : {P : C₁.SmoothPoint // toPointMap cd P = Q},
      C₁.maximalIdealAt P.1 ∈
        (C₂.maximalIdealAt Q).primesOver C₁.CoordinateRing := by
    rintro ⟨P, hP⟩
    refine ⟨(C₁.maximalIdealAt_isMaximal P).isPrime, ?_⟩
    have h := maximalIdealAt_liesOver_toPointMap φ cd P
    rwa [hP] at h
  -- the bijection with the *set* of primes over `m_Q` (avoiding the `factors` Finset)
  have key : Nat.card {P : C₁.SmoothPoint // toPointMap cd P = Q} =
      Nat.card ((C₂.maximalIdealAt Q).primesOver C₁.CoordinateRing) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun P ↦ (⟨C₁.maximalIdealAt P.1, hmem P⟩ :
        (C₂.maximalIdealAt Q).primesOver C₁.CoordinateRing)) ⟨?_, ?_⟩)
    · -- injectivity: `maximalIdealAt` is injective
      intro P P' h
      exact Subtype.ext (C₁.maximalIdealAt_injective (congrArg Subtype.val h))
    · -- surjectivity: a prime over `m_Q` is maximal, hence `m_{P''}`, with `P''` in the fibre
      rintro ⟨M, hMprime, hMlies⟩
      haveI := hMprime
      haveI := hMlies
      have hM_ne_bot : M ≠ ⊥ := by
        intro h
        apply hQ0
        rw [hMlies.over, h, Ideal.under_bot]
      haveI hMmax : M.IsMaximal := Ideal.IsPrime.isMaximal hMprime hM_ne_bot
      obtain ⟨P'', hP''⟩ := C₁.exists_smoothPoint_of_isMaximal hMmax
      have h1 : C₂.maximalIdealAt (toPointMap cd P'') =
          (C₁.maximalIdealAt P'').under C₂.CoordinateRing :=
        (maximalIdealAt_liesOver_toPointMap φ cd P'').over
      rw [hP''] at h1
      exact ⟨⟨P'', C₂.maximalIdealAt_injective (h1.trans hMlies.over.symm)⟩,
        Subtype.ext hP''⟩
  -- convert the set count to the Finset count
  have hcoe : ((IsDedekindDomain.primesOverFinset (C₂.maximalIdealAt Q) C₁.CoordinateRing : Finset _) :
      Set (Ideal C₁.CoordinateRing)) =
      (C₂.maximalIdealAt Q).primesOver C₁.CoordinateRing :=
    IsDedekindDomain.coe_primesOverFinset hQ0 C₁.CoordinateRing
  rw [key, ← hcoe, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- **The good fibre (Silverman II.2.6(b) over `K̄`)**: for a curve map with a
coordinate-ring witness, module-finite coordinate extension and separable
function-field extension, there is a smooth point `Q` of `C₂` — avoiding any
prescribed finite set — whose `toPointMap cd`-fibre has exactly `φ.degree` elements. -/
theorem exists_good_fiber_card_eq_degree [IsAlgClosed F]
    (φ : CurveMap C₁ C₂) (cd : φ.CoordHom)
    (hsepAlg : @Algebra.IsSeparable C₂.FunctionField C₁.FunctionField _ _ φ.toAlgebra)
    {avoid : Set C₂.SmoothPoint} (havoid : avoid.Finite) :
    ∃ Q : C₂.SmoothPoint, Q ∉ avoid ∧
      Nat.card {P : C₁.SmoothPoint // toPointMap cd P = Q} = φ.degree := by
  classical
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := cd.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI htf : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    isTorsionFree_coordHom φ cd
  obtain ⟨S, hSfin, hS⟩ := exists_finite_ramified_locus_coordHom φ cd hsepAlg
  -- pick `Q` outside `avoid` and outside the (finitely many) points whose maximal ideal
  -- lies in the ramified locus
  have hbadQ : (avoid ∪ C₂.maximalIdealAt ⁻¹' S).Finite :=
    havoid.union (hSfin.preimage C₂.maximalIdealAt_injective.injOn)
  haveI : Infinite C₂.SmoothPoint := C₂.smoothPoint_infinite
  obtain ⟨Q, hQ⟩ := hbadQ.infinite_compl.nonempty
  rw [Set.mem_compl_iff, Set.mem_union, not_or] at hQ
  obtain ⟨hQavoid, hQS⟩ := hQ
  refine ⟨Q, hQavoid, ?_⟩
  rw [nat_card_toPointMap_fiber_eq_card_primesOverFinset φ cd Q]
  haveI hQmax : (C₂.maximalIdealAt Q).IsMaximal := C₂.maximalIdealAt_isMaximal Q
  have hQ0 : C₂.maximalIdealAt Q ≠ ⊥ := C₂.maximalIdealAt_ne_bot Q
  refine primesOverFinset_card_eq_degree_of_unramified φ cd hQmax hQ0 ?_
  intro P hP
  have hPmem : P ∈ (C₂.maximalIdealAt Q).primesOver C₁.CoordinateRing := by
    rw [← IsDedekindDomain.coe_primesOverFinset hQ0 C₁.CoordinateRing]
    exact hP
  obtain ⟨hPprime, hPlies⟩ := hPmem
  rw [hS _ hQS P hPprime hPlies.over.symm,
    inertiaDeg_eq_one_of_mem_primesOver φ cd Q P ⟨hPprime, hPlies⟩]

end HasseWeil.Curves.CurveMap
