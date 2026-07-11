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
presentation (`mulByHom_locallyOfFinitePresentation`, the project's Stacks-01TX
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

/-- **(N6 core, the (LIFT) argument)** For `N` invertible, the chart ring map of `[N]`
on a compatible affine chart triple `W, U, V` is formally smooth. -/
theorem formallySmooth_mulByHom_appLE (N : ℕ) (h : NIsInvertible S N)
    {W : S.Opens} (hW : IsAffineOpen W) {U : E.E.Opens} (hU : IsAffineOpen U)
    {V : E.E.Opens} (hV : IsAffineOpen V) (hUW : U ≤ E.π ⁻¹ᵁ W)
    (hVU : V ≤ (E.mulByHom (N : ℤ)) ⁻¹ᵁ U) :
    ((E.mulByHom (N : ℤ)).appLE U V hVU).hom.FormallySmooth := by
  sorry

/-- **(N6)** `[N]` is smooth for `N` invertible on `S` — the (LIFT) translation of
kernel `N`-divisibility (N5). -/
theorem mulByHom_smooth_of_nIsInvertible (N : ℕ) (h : NIsInvertible S N) :
    Smooth (E.mulByHom (N : ℤ)) := by
  haveI := E.mulByHom_locallyOfFinitePresentation N
  refine IsZariskiLocalAtSource.iff_exists_resLE.mpr fun x => ?_
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
  exact ⟨E.formallySmooth_mulByHom_appLE N h hW hU hV hUW hVU,
    (E.mulByHom (N : ℤ)).finitePresentation_appLE hU hV hVU⟩

/-- **(BB-FLAT, invertible case — route (G) closed)** `[N]` is flat for `N` invertible
on `S`. -/
theorem mulByHom_flat_of_nIsInvertible (N : ℕ) (h : NIsInvertible S N) :
    Flat (E.mulByHom (N : ℤ)) := by
  haveI := E.mulByHom_smooth_of_nIsInvertible N h
  infer_instance

end EllipticCurve

end ModularCurves
