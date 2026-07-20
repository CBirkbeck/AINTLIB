/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SemilocalUnitCocycleSplit
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Affine Čech `H⁰`: gluing ring elements over a finite basic cover

Let `R` be a commutative ring and `f : ι → R` a finite family generating the unit ideal, so
the basic opens `D(fᵢ)` cover `Spec R`.  This file provides the **degree-`0` sheaf condition**
for the structure sheaf on this cover, in the `SemilocalUnitSplit.resLoc` vocabulary:

* `exists_algebraMap_eq_of_span_eq_top` — a family `x i ∈ R[1/fᵢ]` agreeing on the pairwise
  overlap localizations `R[1/fᵢ, 1/fⱼ]` glues to a global element `y ∈ R` restricting to each
  `x i`.  (Exactness of `0 → R → ∏ᵢ R[1/fᵢ] → ∏ᵢⱼ R[1/fᵢfⱼ]` in the middle-left; the
  injectivity half is `algebraMap_eq_iff_of_span_eq_top`.)
* `isUnit_of_span_eq_top` — an element of `R` invertible in every `R[1/fᵢ]` is invertible
  (`IsUnit` is Zariski-local on a basic cover).

The gluing is obtained structurally, not by a fresh partition-of-unity computation: the
agreement family is an element of the trivial-cocycle `gluedSubmodule` of
`ForMathlib/SemilocalUnitCocycleSplit`, whose component projections are localization maps
(`isLocalizedModule_gluedProj`, the affine `H⁰` quasi-coherence theorem); the canonical
comparison `R →ₗ[R] gluedSubmodule` is then a localization-isomorphism at every `fᵢ`, hence
bijective by `bijective_of_isLocalized_span`.

The consumer is Stage 3c of the engine mouth core (`Moduli/EngineMouthCharts.lean`): the
corrected Weierstrass chart coefficients agree on overlaps and glue to a global model.
-/

open IsLocalizedModule

namespace SemilocalUnitSplit

variable {R : Type*} [CommRing R] {ι : Type*} (f : ι → R)

/-- The constant-`1` unit cocycle (the gluing datum of the trivial line bundle). -/
private def oneCocycle : ∀ i j : ι,
    (Localization (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)))ˣ :=
  fun _ _ => 1

private theorem oneCocycle_diag (i : ι) : oneCocycle f i i = 1 := rfl

private theorem oneCocycle_coc (i j k : ι) :
    resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
        le_sup_left (oneCocycle f i j).val
      * resLoc (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) (oneCocycle f j k).val
    = resLoc (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
        (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) (oneCocycle f i k).val := by
  show resLoc _ _ _ (1 : Localization _) * resLoc _ _ _ (1 : Localization _)
    = resLoc _ _ _ (1 : Localization _)
  rw [map_one, map_one, map_one, one_mul]

/-- The canonical comparison of `R` with the module of agreement families: `r` goes to the
family of its localizations, which agrees on overlaps (the trivial-cocycle matching). -/
private noncomputable def algebraMapGlued :
    R →ₗ[R] gluedSubmodule f (oneCocycle f) where
  toFun r := ⟨fun i => algebraMap R (Localization (Submonoid.powers (f i))) r, fun i j => by
    rw [resLoc_algebraMap, resLoc_algebraMap]
    exact (one_mul _).symm⟩
  map_add' a b := Subtype.ext (funext fun i => map_add _ a b)
  map_smul' r a := Subtype.ext (funext fun i => by
    simp only [RingHom.id_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, map_mul,
      Algebra.smul_def])

@[simp] private theorem algebraMapGlued_apply (r : R) (i : ι) :
    (algebraMapGlued f r).1 i = algebraMap R (Localization (Submonoid.powers (f i))) r :=
  rfl

/-- **The comparison with the glued sections is bijective** (`H⁰(Spec R, 𝒪) = R` on a finite
basic cover): localized at each member of the covering family, `algebraMapGlued` is the
identity of `R[1/fᵢ]` through the quasi-coherence identification `isLocalizedModule_gluedProj`,
so it is bijective by the local-global principle for the covering span. -/
private theorem bijective_algebraMapGlued [Fintype ι]
    (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Bijective (algebraMapGlued f) := by
  classical
  -- a chosen index for each member of the covering set
  have hsec : ∀ r : Set.range f, ∃ i, f i = r.1 := fun r => r.2
  choose idx hidx using hsec
  -- the localization witnesses on both sides, with the `powers (f (idx r)) = powers r`
  -- transport
  haveI instM : ∀ r : Set.range f, IsLocalizedModule.Away r.1
      (Algebra.linearMap R (Localization (Submonoid.powers (f (idx r))))) := fun r => by
    show IsLocalizedModule (Submonoid.powers r.1) _
    rw [← hidx r]
    exact isLocalizedModule_algebraLinearMap (Submonoid.powers (f (idx r)))
  haveI instN : ∀ r : Set.range f, IsLocalizedModule.Away r.1
      (gluedProj f (oneCocycle f) (idx r)) := fun r => by
    show IsLocalizedModule (Submonoid.powers r.1) _
    rw [← hidx r]
    exact isLocalizedModule_gluedProj f (oneCocycle f) (oneCocycle_diag f)
      (oneCocycle_coc f) (idx r)
  refine bijective_of_isLocalized_span (Set.range f) hf
    (fun r => Localization (Submonoid.powers (f (idx r))))
    (fun r => Algebra.linearMap R (Localization (Submonoid.powers (f (idx r)))))
    (fun r => Localization (Submonoid.powers (f (idx r))))
    (fun r => gluedProj f (oneCocycle f) (idx r))
    (algebraMapGlued f) (fun r => ?_)
  -- the localized comparison is the identity, by uniqueness of maps out of a localization
  have hid : IsLocalizedModule.map (Submonoid.powers r.1)
      (Algebra.linearMap R (Localization (Submonoid.powers (f (idx r)))))
      (gluedProj f (oneCocycle f) (idx r)) (algebraMapGlued f) = LinearMap.id := by
    refine linearMap_ext (Submonoid.powers r.1)
      (Algebra.linearMap R (Localization (Submonoid.powers (f (idx r)))))
      (Algebra.linearMap R (Localization (Submonoid.powers (f (idx r))))) ?_
    refine LinearMap.ext fun a => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, IsLocalizedModule.map_apply,
      LinearMap.id_comp]
    rfl
  rw [hid]
  exact Function.bijective_id

/-- **Affine Čech `H⁰` gluing on a finite basic cover.**  For a finite family `f : ι → R`
generating the unit ideal, every family `x i ∈ R[1/fᵢ]` that agrees on the pairwise overlap
localizations `R[1/fᵢ, 1/fⱼ]` is the family of localizations of a single global element
`y ∈ R`.  This is the existence half of the structure-sheaf sheaf condition on the basic
cover `{D(fᵢ)}` of `Spec R`. -/
theorem exists_algebraMap_eq_of_span_eq_top [Fintype ι]
    (hf : Ideal.span (Set.range f) = ⊤)
    (x : ∀ i, Localization (Submonoid.powers (f i)))
    (hagree : ∀ i j,
      resLoc (Submonoid.powers (f i)) (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
        le_sup_left (x i)
      = resLoc (Submonoid.powers (f j)) (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
          le_sup_right (x j)) :
    ∃ y : R, ∀ i, algebraMap R (Localization (Submonoid.powers (f i))) y = x i := by
  have hx : x ∈ gluedSubmodule f (oneCocycle f) := fun i j => by
    rw [show (oneCocycle f i j).val = 1 from rfl, one_mul]
    exact hagree i j
  obtain ⟨y, hy⟩ := (bijective_algebraMapGlued f hf).2 ⟨x, hx⟩
  exact ⟨y, fun i => congrFun (congrArg Subtype.val hy) i⟩

/-- **Separatedness half of the `H⁰` sheaf condition**: two global elements with the same
localizations at every member of a covering family are equal. -/
theorem algebraMap_eq_iff_of_span_eq_top [Fintype ι]
    (hf : Ideal.span (Set.range f) = ⊤) {y z : R}
    (h : ∀ i, algebraMap R (Localization (Submonoid.powers (f i))) y
      = algebraMap R (Localization (Submonoid.powers (f i))) z) :
    y = z := by
  refine (bijective_algebraMapGlued f hf).1 (Subtype.ext (funext fun i => ?_))
  exact h i

/-- **`IsUnit` is Zariski-local on a finite basic cover**: an element of `R` whose image in
every `R[1/fᵢ]` is a unit, for `f` a family generating the unit ideal, is itself a unit.
(No finiteness of `ι` is needed: invertibility is detected at maximal ideals, and each
maximal ideal misses some `fᵢ`.) -/
theorem isUnit_of_span_eq_top (hf : Ideal.span (Set.range f) = ⊤) (y : R)
    (hy : ∀ i, IsUnit (algebraMap R (Localization (Submonoid.powers (f i))) y)) :
    IsUnit y := by
  rw [← Ideal.span_singleton_eq_top]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hym : y ∈ m := hle (Ideal.subset_span rfl)
  -- some member of the covering family avoids `m`
  have hfi : ∃ i, f i ∉ m := by
    by_contra hall
    refine hm.ne_top (top_le_iff.mp ?_)
    rw [← hf]
    refine Ideal.span_le.mpr fun z hz => ?_
    obtain ⟨i, rfl⟩ := hz
    exact of_not_not fun hzm => hall ⟨i, hzm⟩
  obtain ⟨i, hi⟩ := hfi
  -- clear the inverse of `y` in `R[1/fᵢ]` to a power identity in `R`
  obtain ⟨b, hb⟩ := (hy i).exists_right_inv
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj (Submonoid.powers (f i)) b
  have hyc : algebraMap R (Localization (Submonoid.powers (f i))) (y * c)
      = algebraMap R (Localization (Submonoid.powers (f i))) ((s : R)) := by
    rw [map_mul, ← hcs, ← mul_assoc, hb, one_mul]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f i)) _).mp hyc
  -- the right side is a power of `fᵢ`; the left side lies in `m`
  obtain ⟨ks, hks⟩ := s.2
  obtain ⟨kt, hkt⟩ := t.2
  have hmem : (t : R) * ((s : R)) ∈ m := by
    rw [← ht]
    exact m.mul_mem_left _ (m.mul_mem_right _ hym)
  rw [← hks, ← hkt, ← pow_add] at hmem
  exact hi (hm.isPrime.mem_of_pow_mem _ hmem)

/-- **Weierstrass curves glue over a finite basic cover** (the `H⁰` sheaf condition,
coefficientwise): a family of Weierstrass curves over the localizations `R[1/fᵢ]` of a
covering family agreeing on the pairwise overlap localizations descends to a Weierstrass
curve over `R`; if the local discriminants are units, so is the glued one.

Stated (and proven) over a *variable* ring `R` on purpose: the coefficient extraction and
the discriminant rewrite are cheap here, while at the concrete localization towers of a
scheme's section rings they blow the `whnf` budget — consumers apply this lemma and never
unfold. -/
theorem exists_weierstrassCurve_map_eq_of_span_eq_top {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (V : ∀ i, WeierstrassCurve (Localization (Submonoid.powers (f i))))
    (hagree : ∀ i j, (V i).map (resLoc (Submonoid.powers (f i))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left)
      = (V j).map (resLoc (Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right)) :
    ∃ W₀ : WeierstrassCurve R,
      (∀ i, W₀.map (algebraMap R (Localization (Submonoid.powers (f i)))) = V i) ∧
      ((∀ i, IsUnit (V i).Δ) → IsUnit W₀.Δ) := by
  classical
  obtain ⟨y₁, hy₁⟩ := exists_algebraMap_eq_of_span_eq_top f hf (fun i => (V i).a₁)
    (fun i j => by
      have h := congrArg WeierstrassCurve.a₁ (hagree i j)
      simpa only [WeierstrassCurve.map_a₁] using h)
  obtain ⟨y₂, hy₂⟩ := exists_algebraMap_eq_of_span_eq_top f hf (fun i => (V i).a₂)
    (fun i j => by
      have h := congrArg WeierstrassCurve.a₂ (hagree i j)
      simpa only [WeierstrassCurve.map_a₂] using h)
  obtain ⟨y₃, hy₃⟩ := exists_algebraMap_eq_of_span_eq_top f hf (fun i => (V i).a₃)
    (fun i j => by
      have h := congrArg WeierstrassCurve.a₃ (hagree i j)
      simpa only [WeierstrassCurve.map_a₃] using h)
  obtain ⟨y₄, hy₄⟩ := exists_algebraMap_eq_of_span_eq_top f hf (fun i => (V i).a₄)
    (fun i j => by
      have h := congrArg WeierstrassCurve.a₄ (hagree i j)
      simpa only [WeierstrassCurve.map_a₄] using h)
  obtain ⟨y₆, hy₆⟩ := exists_algebraMap_eq_of_span_eq_top f hf (fun i => (V i).a₆)
    (fun i j => by
      have h := congrArg WeierstrassCurve.a₆ (hagree i j)
      simpa only [WeierstrassCurve.map_a₆] using h)
  have hglue : ∀ i, (⟨y₁, y₂, y₃, y₄, y₆⟩ : WeierstrassCurve R).map
      (algebraMap R (Localization (Submonoid.powers (f i)))) = V i := fun i =>
    WeierstrassCurve.ext (hy₁ i) (hy₂ i) (hy₃ i) (hy₄ i) (hy₆ i)
  refine ⟨⟨y₁, y₂, y₃, y₄, y₆⟩, hglue, fun hunit => ?_⟩
  refine isUnit_of_span_eq_top f hf _ (fun i => ?_)
  have h2 : algebraMap R (Localization (Submonoid.powers (f i)))
      (⟨y₁, y₂, y₃, y₄, y₆⟩ : WeierstrassCurve R).Δ = (V i).Δ := by
    have h3 := congrArg WeierstrassCurve.Δ (hglue i)
    rwa [WeierstrassCurve.map_Δ] at h3
  rw [h2]
  exact hunit i

end SemilocalUnitSplit
