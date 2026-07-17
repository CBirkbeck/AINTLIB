/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.KernelDivisibilityGlue

/-!
# Smoothness and flatness of `[N]` for `N` invertible (BB-FLAT route (G), step N6)

`[N] : E ⟶ E` is smooth when `N` is invertible on the base — hence flat, closing BB-FLAT.

The proof is the infinitesimal-lifting translation (the (LIFT) core of the route-(G)
audit): smoothness is checked on affine chart pairs `(U, V)` with `V ≤ [N]⁻¹ U` and both
inside `π`-preimages of an affine `W ⊆ S`. The ring map `Γ(U) ⟶ Γ(V)` is of finite
presentation (`MulByHom.locallyOfFinitePresentation`, the project's Stacks-01TX
cancellation), so it remains to lift `Γ(U)`-algebra maps `Γ(V) →ₐ B ⧸ I` across a
square-zero ideal `I`:

* geometrize the test data to points `x̄ ∈ E(B⧸I)`, `y ∈ E(B)` with `[N]x̄ = ȳ`;
* lift `x̄` to `x̃ ∈ E(B)` through the formal smoothness of `Γ(W) ⟶ Γ(V)` (the
  elliptic curve is smooth over `S`);
* the defect `ε := y − [N]x̃` is a square-zero point-kernel element, so
  `KernelNDivisible` (N5, `kernelNDivisibleGlue`) divides it: `ε = N•δ` with
  `δ` restricting to zero;
* `x := x̃ + δ` satisfies `[N]x = y` and reduces to `x̄`; it lands in `V` because
  square-zero thickenings are homeomorphisms, so it re-algebraizes to the desired
  lift `Γ(V) →ₐ B` by full faithfulness of `Spec` on affines.
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct

universe u

noncomputable section

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- `Spec` of a quotient by a square-zero ideal is surjective on points (square-zero
thickenings are homeomorphisms): the augmentation-kernel elements are nilpotent, hence lie
in every prime, so the comap of the quotient map hits every prime. Extracted from the
re-algebraize stage of the (LIFT) core. -/
private theorem specMap_quotientMk_base_surjective {B : Type u} [CommRing B] (I : Ideal B)
    (hI : I ^ 2 = ⊥) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base := by
  rw [← Set.range_eq_univ]
  show Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = Set.univ
  have h1 : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus ((RingHom.ker (Ideal.Quotient.mk I) : Ideal B) : Set B) :=
    range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at h1
  rw [h1, Set.eq_univ_iff_forall]
  intro p a ha
  have ha2 : a ^ 2 ∈ I ^ 2 := Ideal.pow_mem_pow ha 2
  rw [hI] at ha2
  have ha0 : a ^ 2 = 0 := by simpa using ha2
  exact p.isPrime.mem_of_pow_mem 2 (ha0 ▸ p.asIdeal.zero_mem)

/-- The chart triangle `Γ(W) ⟶ Γ(U) ⟶ Γ(V)` of `[n]` refines the structure chart map:
`π`'s comorphism `Γ(W) ⟶ Γ(V)` factors as `Γ(W) ⟶ Γ(U)` (via `π`) then `Γ(U) ⟶ Γ(V)`
(via `[n]`), because `[n] ≫ π = π`. Extracted from the geometrize/setup stage. -/
private theorem pi_appLE_eq_comp_mulByHom_appLE (n : ℤ) {W : S.Opens} {U V : E.E.Opens}
    (hVW : V ≤ E.π ⁻¹ᵁ W) (hUW : U ≤ E.π ⁻¹ᵁ W) (hVU : V ≤ (E.mulByHom n) ⁻¹ᵁ U) :
    E.π.appLE W V hVW = E.π.appLE W U hUW ≫ (E.mulByHom n).appLE U V hVU := by
  rw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (q : E.E ⟶ S) (_ : q = E.π) (e : V ≤ q ⁻¹ᵁ W),
      E.π.appLE W V hVW = q.appLE W V e := by
    rintro q rfl e
    rfl
  exact key _ (E.mulByHom_π n) _

/-- **(divide-defect + correct)** Given a lifted point `Pxt` whose `[N]`-image agrees with
the target `Py` after reduction along the square-zero quotient, the kernel-`N`-divisibility
of the point functor (N5) produces a corrected lift `Px` with `[N]Px = Py` that reduces to
the same point as `Pxt`. Extracted from the middle two stages of the (LIFT) core. -/
private theorem exists_corrected_lift (N : ℕ) (h : NIsInvertible S N) (B : CommRingCat.{u})
    (I : Ideal ↥B) (hI : I ^ 2 = ⊥) (t : Spec B ⟶ S) (Py Pxt : E.Point t)
    (hres : Point.restrict E (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) Py =
        Point.restrict E (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
          ((N : ℤ) • Pxt)) :
    ∃ Px : E.Point t, (N : ℤ) • Px = Py ∧
      Point.restrict E (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) Px =
        Point.restrict E (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) Pxt := by
  have hεres : Point.restrict E (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Py - (N : ℤ) • Pxt) = 0 := by
    rw [E.restrict_sub, hres, sub_self]
  obtain ⟨δ, hδres, hδN⟩ :=
    E.kernelNDivisible_of_nIsInvertible N h B I hI t (Py - (N : ℤ) • Pxt) hεres
  refine ⟨Pxt + δ, ?_, ?_⟩
  · rw [smul_add, hδN]
    abel
  · rw [E.restrict_add, hδres, add_zero]

/-- A map of schemes `f : Z ⟶ Y` factors through an open immersion `j : X ⟶ Y` as soon as it
does so after precomposition with a surjective-on-points map `g : W ⟶ Z`. Since square-zero
thickenings are surjective on points, the corrected lift — which lands in the affine chart only
after reduction — in fact lands in the chart itself. Extracted from the re-algebraize stage of
the (LIFT) core. -/
private theorem exists_lift_of_isOpenImmersion_of_surjective_comp {W X Y Z : Scheme.{u}}
    {g : W ⟶ Z} (hg : Function.Surjective g.base) {f : Z ⟶ Y} {j : X ⟶ Y} [IsOpenImmersion j]
    {k : W ⟶ X} (hcomm : g ≫ f = k ≫ j) : ∃ l : Z ⟶ X, l ≫ j = f := by
  have hrange : Set.range f.base ⊆ Set.range j.base := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := hg z
    have h1 : f.base (g.base w) = (g ≫ f).base w := (Scheme.Hom.comp_apply _ _ _).symm
    rw [h1, hcomm]
    exact ⟨k.base w, Scheme.Hom.comp_apply _ _ _⟩
  exact ⟨IsOpenImmersion.lift j f hrange, IsOpenImmersion.lift_fac _ _ hrange⟩

/-- **(N6 core, the (LIFT) argument)** For `N` invertible, the chart ring map of `[N]`
on a compatible affine chart triple `W, U, V` is formally smooth. -/
theorem MulByHom.formallySmooth_appLE (N : ℕ) (h : NIsInvertible S N)
    {W : S.Opens} (hW : IsAffineOpen W) {U : E.E.Opens} (hU : IsAffineOpen U)
    {V : E.E.Opens} (hV : IsAffineOpen V) (hUW : U ≤ E.π ⁻¹ᵁ W)
    (hVU : V ≤ (E.mulByHom (N : ℤ)) ⁻¹ᵁ U) :
    ((E.mulByHom (N : ℤ)).appLE U V hVU).hom.FormallySmooth := by
  have : Smooth E.π := SmoothOfRelativeDimension.smooth (n := 1) E.π
  have hVW : V ≤ E.π ⁻¹ᵁ W := fun v hv ↦ by
    have h1 : E.π.base ((E.mulByHom (N : ℤ)).base v) ∈ W := hUW (hVU hv)
    rwa [← Scheme.Hom.comp_apply, E.mulByHom_π] at h1
  -- the chart triangle `Γ(W) ⟶ Γ(U) ⟶ Γ(V)` refines the structure chart map
  have happ : E.π.appLE W V hVW =
      E.π.appLE W U hUW ≫ (E.mulByHom (N : ℤ)).appLE U V hVU :=
    E.pi_appLE_eq_comp_mulByHom_appLE (N : ℤ) hVW hUW hVU
  have hπfs : (E.π.appLE W V hVW).hom.FormallySmooth :=
    (RingHom.smooth_def.mp (E.π.smooth_appLE hW hV hVW)).1
  letI : Algebra ↑Γ(E.E, U) ↑Γ(E.E, V) :=
    ((E.mulByHom (N : ℤ)).appLE U V hVU).hom.toAlgebra
  show Algebra.FormallySmooth ↑Γ(E.E, U) ↑Γ(E.E, V)
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI ψq ↦ ?_
  -- the Γ(W)-algebra world in which the smoothness of `E/S` lifts
  letI : Algebra ↑Γ(S, W) ↑Γ(E.E, V) := (E.π.appLE W V hVW).hom.toAlgebra
  letI : Algebra ↑Γ(S, W) B :=
    ((algebraMap ↑Γ(E.E, U) B).comp (E.π.appLE W U hUW).hom).toAlgebra
  have hπfsA : Algebra.FormallySmooth ↑Γ(S, W) ↑Γ(E.E, V) := hπfs
  have hcomm : ∀ r : ↑Γ(S, W), ψq ((E.π.appLE W V hVW).hom r) =
      algebraMap ↑Γ(S, W) (B ⧸ I) r := by
    intro r
    have h1 : (E.π.appLE W V hVW).hom r =
        algebraMap ↑Γ(E.E, U) ↑Γ(E.E, V) ((E.π.appLE W U hUW).hom r) :=
      congrArg (fun m : Γ(S, W) ⟶ Γ(E.E, V) ↦ m.hom r) happ
    rw [h1, ψq.commutes]
    rfl
  obtain ⟨χ, hχ⟩ := Algebra.FormallySmooth.comp_surjective ↑Γ(S, W) ↑Γ(E.E, V) I hI
    { toRingHom := ψq.toRingHom, commutes' := hcomm }
  -- geometrize: the test points over `Spec B`
  set BC := CommRingCat.of B with hBC
  set φB : BC ⟶ CommRingCat.of (B ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I) with hφB
  set y : Spec BC ⟶ E.E :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(E.E, U) B)) ≫ hU.fromSpec with hy
  set xt : Spec BC ⟶ E.E := Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hV.fromSpec with hxt
  set t : Spec BC ⟶ S := y ≫ E.π with ht
  -- the lifted point sits over the same base point
  have hxtπ : xt ≫ E.π = t := by
    rw [hxt, ht, hy, Category.assoc, ← hW.SpecMap_appLE_fromSpec E.π hV hVW,
      Category.assoc, ← hW.SpecMap_appLE_fromSpec E.π hU hUW, ← Category.assoc,
      ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    refine congrArg (· ≫ hW.fromSpec) (congrArg Spec.map (CommRingCat.hom_ext
      (RingHom.ext fun r ↦ ?_)))
    exact χ.commutes r
  set Py : E.Point t := ⟨y, ht.symm⟩ with hPy
  set Pxt : E.Point t := ⟨xt, hxtπ⟩ with hPxt
  -- the reduction of the lifted point is the given source point
  have hxtres : Spec.map φB ≫ xt = Spec.map (CommRingCat.ofHom ψq.toRingHom) ≫
      hV.fromSpec := by
    rw [hxt, ← Category.assoc, ← Spec.map_comp]
    refine congrArg (· ≫ hV.fromSpec) (congrArg Spec.map (CommRingCat.hom_ext
      (RingHom.ext fun v ↦ ?_)))
    exact congrArg (fun m : ↑Γ(E.E, V) →ₐ[↑Γ(S, W)] B ⧸ I ↦ m v) hχ
  -- the `[N]`-compatibility of the test data, geometrized
  have hNbar : Spec.map (CommRingCat.ofHom ψq.toRingHom) ≫
      (hV.fromSpec ≫ E.mulByHom (N : ℤ)) = Spec.map φB ≫ y := by
    rw [← hU.SpecMap_appLE_fromSpec (E.mulByHom (N : ℤ)) hV hVU, hy, ← Category.assoc,
      ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    refine congrArg (· ≫ hU.fromSpec) (congrArg Spec.map (CommRingCat.hom_ext
      (RingHom.ext fun s ↦ ?_)))
    exact ψq.commutes s
  -- the defect is a square-zero point-kernel element
  have hres_eq : Point.restrict E (Spec.map φB) Py =
      Point.restrict E (Spec.map φB) ((N : ℤ) • Pxt) := by
    refine Subtype.ext ?_
    show Spec.map φB ≫ y = Spec.map φB ≫ ((N : ℤ) • Pxt : E.Point t).1
    refine (hNbar.symm).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ E.mulByHom (N : ℤ)) hxtres.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (Spec.map φB ≫ ·) (point_smul_eq_comp_mulBy E t (N : ℤ) Pxt).symm
  -- the corrected lift, via kernel `N`-divisibility (N5)
  obtain ⟨Px, hPxN, hPxres⟩ := E.exists_corrected_lift N h BC I hI t Py Pxt hres_eq
  -- the corrected lift lands in the chart: square-zero thickenings are homeomorphisms
  have hφBsurj : Function.Surjective (Spec.map φB).base :=
    specMap_quotientMk_base_surjective I hI
  have hresval : Spec.map φB ≫ Px.1 = Spec.map (CommRingCat.ofHom ψq.toRingHom) ≫
      hV.fromSpec := by
    have h1 : (Point.restrict E (Spec.map φB) Px).1 =
        (Point.restrict E (Spec.map φB) Pxt).1 := congrArg Subtype.val hPxres
    exact h1.trans hxtres
  obtain ⟨xV, hxVfac⟩ :=
    exists_lift_of_isOpenImmersion_of_surjective_comp hφBsurj hresval
  obtain ⟨σC, hσC⟩ := Spec.map_surjective xV
  -- the comorphism is `Γ(U)`-linear: `[N] ∘ x = y`
  have hUlin : (E.mulByHom (N : ℤ)).appLE U V hVU ≫ σC =
      CommRingCat.ofHom (algebraMap ↑Γ(E.E, U) B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hσC]
    refine (cancel_mono hU.fromSpec).mp ?_
    rw [Category.assoc, hU.SpecMap_appLE_fromSpec (E.mulByHom (N : ℤ)) hV hVU,
      ← Category.assoc, hxVfac]
    have h1 : Px.1 ≫ E.mulByHom (N : ℤ) = y := by
      have h2 := congrArg Subtype.val hPxN
      rwa [show (((N : ℤ) • Px : E.Point t) : Spec BC ⟶ E.E) = Px.1 ≫ E.mulByHom (N : ℤ)
        from point_smul_eq_comp_mulBy E t (N : ℤ) Px] at h2
    rw [h1, hy]
  -- the comorphism lifts the given algebra map
  have hlift : σC ≫ φB = CommRingCat.ofHom ψq.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hσC]
    refine (cancel_mono hV.fromSpec).mp ?_
    rw [Category.assoc, hxVfac]
    exact hresval
  -- package the algebra-level lift
  refine ⟨{ toRingHom := σC.hom, commutes' := fun s ↦ ?_ }, ?_⟩
  · exact congrArg (fun m : Γ(E.E, U) ⟶ BC ↦ m.hom s) hUlin
  · refine AlgHom.ext fun v ↦ ?_
    exact congrArg (fun m : Γ(E.E, V) ⟶ CommRingCat.of (B ⧸ I) ↦ m.hom v) hlift

set_option backward.isDefEq.respectTransparency false in
/-- **(N6)** `[N]` is smooth for `N` invertible on `S` — the (LIFT) translation of
kernel `N`-divisibility (N5). -/
theorem MulByHom.smooth_of_nIsInvertible (N : ℕ) (h : NIsInvertible S N) :
    Smooth (E.mulByHom (N : ℤ)) := by
  have := MulByHom.locallyOfFinitePresentation E N
  refine IsZariskiLocalAtSource.iff_exists_resLE.mpr fun x ↦ ?_
  -- an affine chart `W` around the base point
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (E.π.base x)) isOpen_univ
  -- an affine chart `U` around `[N] x` inside `π ⁻¹ W`
  have hNxW : (E.mulByHom (N : ℤ)).base x ∈ E.π ⁻¹ᵁ W := by
    show E.π.base ((E.mulByHom (N : ℤ)).base x) ∈ W
    rw [← Scheme.Hom.comp_apply, E.mulByHom_π]
    exact hxW
  obtain ⟨_, ⟨U, hU, rfl⟩, hNxU, hUW⟩ := E.E.isBasis_affineOpens.exists_subset_of_mem_open
    hNxW ((E.π ⁻¹ᵁ W).2)
  -- an affine chart `V` around `x` inside `[N] ⁻¹ U`
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := E.E.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (E.mulByHom (N : ℤ)) ⁻¹ᵁ U from hNxU) (((E.mulByHom (N : ℤ)) ⁻¹ᵁ U).2)
  refine ⟨U, V, hxV, hVU, ?_⟩
  have : IsAffine U := hU
  have : IsAffine V := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
  refine (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso (E.mulByHom (N : ℤ)) U V hVU)).mpr ?_
  rw [RingHom.smooth_def]
  exact ⟨MulByHom.formallySmooth_appLE E N h hW hU hV hUW hVU,
    (E.mulByHom (N : ℤ)).finitePresentation_appLE hU hV hVU⟩

/-- **(BB-FLAT, invertible case — route (G) closed)** `[N]` is flat for `N` invertible
on `S`. -/
theorem MulByHom.flat_of_nIsInvertible (N : ℕ) (h : NIsInvertible S N) :
    Flat (E.mulByHom (N : ℤ)) := by
  have := MulByHom.smooth_of_nIsInvertible E N h
  infer_instance

end EllipticCurve

end ModularCurves
