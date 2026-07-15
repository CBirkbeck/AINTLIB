/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.Subgroup

/-!
# The quotient of an elliptic curve by a finite locally free subgroup scheme

**Interface layer (T-G3d-infra).** For `G` a finite locally free subgroup scheme of `E/S`
(`FiniteLocallyFreeSubgroup E`), this file provides the categorical quotient `E/G` — the
`fppf`-sheaf quotient by the translation action — as **DS-registered data** together with its
**opaque universal-property interface**. Per the standing rule 3 / v10.24(b) (a heavy definition
ships its interface in the same increment), consumers touch only the pins below, never the raw
construction.

The construction (deferred; not gated on the `E[N]`-finite-étale linchpin, since it takes the
`finite`/`flat`/`lfp` fields of `G` as input) glues the local co-invariant affine quotients on
p2's `ForMathlib/SchemeQuotient.lean` glue-data pattern; the full plan — routes, the p2
co-action dependency, the `[N]`-iso consumer — is in `.mathlib-quality/decomposition-g3d-infra.md`.

Consumers: `T-G3d`'s `E/E[N] ≅ E` (via `[N]`), the review-Q8 `N`-Isog named block, the eventual
`Γ₀(N)` path.

## Main interface
* `FiniteLocallyFreeSubgroup.IsInvariant` — the descent condition on a morphism out of `E`.
* `FiniteLocallyFreeSubgroup.quotient` / `quotientS` / `quotientπ` — `E/G`, its structure map,
  and the quotient isogeny (DS-data).
* `quotientπ_isInvariant`, `quotient_lift` — the universal property (pins).
* `quotientπ_hom_ext` — `π` is epi (PROVED from the pins).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} {E : EllipticCurve S}

/-- A morphism `f : E ⟶ Y` is **invariant** under the translation action of the finite locally free
subgroup scheme `G ⊆ E` when `f(x + t) = f(x)` for every point `x : E.Point g` and every `G`-point
`t` (`t ∈ G.pointSubgroup g`). This is the functor-of-points form of the coequalizer condition cut
out by the two maps `G ×_S E ⇉ E` (translate `(t, x) ↦ x + t`, project `(t, x) ↦ x`); it is the
universal condition for a morphism to factor through `E/G`. -/
def FiniteLocallyFreeSubgroup.IsInvariant (G : FiniteLocallyFreeSubgroup E) {Y : Scheme.{u}}
    (f : E.E ⟶ Y) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (x t : E.Point g), t ∈ G.pointSubgroup g →
    (x + t).1 ≫ f = x.1 ≫ f

namespace FiniteLocallyFreeSubgroup

/-- Invariance is preserved by post-composition: if `f` collapses `G`-translates, so does
`f ≫ h`. -/
theorem IsInvariant.comp {G : FiniteLocallyFreeSubgroup E} {Y Z : Scheme.{u}} {f : E.E ⟶ Y}
    (hf : G.IsInvariant f) (h : Y ⟶ Z) : G.IsInvariant (f ≫ h) := fun _ g x t ht => by
  rw [← Category.assoc, hf g x t ht, Category.assoc]

/-- **DS-data (T-G3d-infra)** The quotient scheme `E/G` of `E` by the finite locally free subgroup
scheme `G`, over `S`. Construction: glue the local co-invariant affine quotients on p2's
`SchemeQuotient` glue-data pattern (`.mathlib-quality/decomposition-g3d-infra.md`). Consumers use
only the universal-property pins below. -/
noncomputable def quotient (G : FiniteLocallyFreeSubgroup E) : Scheme.{u} := sorry

/-- **DS-data (T-G3d-infra)** The structure morphism `E/G ⟶ S`. -/
noncomputable def quotientS (G : FiniteLocallyFreeSubgroup E) : G.quotient ⟶ S := sorry

/-- **DS-data (T-G3d-infra)** The quotient isogeny `E ⟶ E/G` (finite locally free of degree
`rank G`; for `G = E[N]` this is the map whose factorization of `[N]` gives `E/E[N] ≅ E`). -/
noncomputable def quotientπ (G : FiniteLocallyFreeSubgroup E) : E.E ⟶ G.quotient := sorry

/-- **(T-G3d-infra pin)** The quotient isogeny is a morphism over `S`: `π ≫ (E/G ⟶ S) = E.π`. -/
theorem quotientπ_over (G : FiniteLocallyFreeSubgroup E) :
    G.quotientπ ≫ G.quotientS = E.π := sorry

/-- **(T-G3d-infra pin)** The quotient isogeny is `G`-invariant: it collapses each `G`-translate. -/
theorem quotientπ_isInvariant (G : FiniteLocallyFreeSubgroup E) :
    G.IsInvariant G.quotientπ := sorry

/-- **(T-G3d-infra pin — universal property)** Every `G`-invariant `f : E ⟶ Y` factors **uniquely**
through the quotient: there is a unique `h : E/G ⟶ Y` with `π ≫ h = f`. This categorical-quotient
property is what the whole layer exists to supply; the `[N]`-invariance of `[N] : E ⟶ E` then yields
the factorization `E/E[N] ⟶ E` (T-G3d). -/
theorem quotient_lift (G : FiniteLocallyFreeSubgroup E) {Y : Scheme.{u}} (f : E.E ⟶ Y)
    (hf : G.IsInvariant f) : ∃! h : G.quotient ⟶ Y, G.quotientπ ≫ h = f := sorry

/-- **(T-G3d-infra — `π` is an epimorphism)** Morphisms out of `E/G` are determined by their
composition with the quotient isogeny. PROVED from `quotient_lift` + `quotientπ_isInvariant`
(the common composite `π ≫ h₁` is `G`-invariant, so both `h₁, h₂` are *the* lift of it). -/
theorem quotientπ_hom_ext (G : FiniteLocallyFreeSubgroup E) {Y : Scheme.{u}}
    (h₁ h₂ : G.quotient ⟶ Y) (H : G.quotientπ ≫ h₁ = G.quotientπ ≫ h₂) : h₁ = h₂ := by
  obtain ⟨_, _, huniq⟩ := G.quotient_lift (G.quotientπ ≫ h₁) (G.quotientπ_isInvariant.comp h₁)
  exact (huniq h₁ rfl).trans (huniq h₂ H.symm).symm

end FiniteLocallyFreeSubgroup

/-! ### The leading example: `E/E[N]` and the factored `[N]`

The quotient isogeny `π : E ⟶ E/E[N]` receives `[N] : E ⟶ E`: since `[N]` kills `E[N]`, it is
invariant under translation by `E[N]`, so it factors uniquely as `π ≫ q` with `q : E/E[N] ⟶ E`.
That `q` is an isomorphism — `E/E[N] ≅ E`, the content of KM 2.7's `[N]`-isogeny picture — is the
degree-fact half (`deg[N] = N² = rank E[N]`), tracked separately as `T-G3d-Niso`; the factored map
itself lands here against the interface. -/

variable (E) in
/-- **(T-G3d)** `[N] : E ⟶ E` is invariant under translation by the `N`-torsion subgroup scheme
`E[N]`: for a `T`-point `x` and an `N`-torsion `T`-point `t`, `[N](x + t) = [N]x + [N]t = [N]x`,
because `t ∈ E[N]` means exactly `N • t = 0`. -/
theorem mulByHom_torsionSubgroup_isInvariant (N : ℕ) [NeZero N] :
    (E.torsionSubgroup N).IsInvariant (E.mulByHom (N : ℤ)) := by
  intro T g x t ht
  rw [E.torsionSubgroup_pointSubgroup, Submodule.mem_toAddSubgroup,
    Submodule.mem_torsionBy_iff] at ht
  have h1 : ((N : ℤ) • (x + t) : E.Point g).1 = (x + t).1 ≫ E.mulByHom (N : ℤ) :=
    E.point_smul_eq_comp_mulBy g (N : ℤ) (x + t)
  have h2 : ((N : ℤ) • x : E.Point g).1 = x.1 ≫ E.mulByHom (N : ℤ) :=
    E.point_smul_eq_comp_mulBy g (N : ℤ) x
  rw [← h1, ← h2, smul_add, ht, add_zero]

variable (E) in
/-- **(T-G3d, factored map)** The map `E/E[N] ⟶ E` through which `[N] : E ⟶ E` factors: the
unique lift of the `E[N]`-invariant `[N]` across the quotient isogeny `π : E ⟶ E/E[N]`
(`quotient_lift` applied to `mulByHom_torsionSubgroup_isInvariant`). `E/E[N] ≅ E` — that this
map is an isomorphism — is `T-G3d-Niso` (degree facts). -/
noncomputable def torsionQuotientToSelf (N : ℕ) [NeZero N] :
    (E.torsionSubgroup N).quotient ⟶ E.E :=
  ((E.torsionSubgroup N).quotient_lift (E.mulByHom (N : ℤ))
    (E.mulByHom_torsionSubgroup_isInvariant N)).choose

variable (E) in
/-- The factored map recovers `[N]`: `π ≫ (E/E[N] ⟶ E) = [N]`. This is the defining property of
`torsionQuotientToSelf`; `quotientπ_hom_ext` makes it the *unique* such map. -/
theorem torsionQuotientπ_comp_toSelf (N : ℕ) [NeZero N] :
    (E.torsionSubgroup N).quotientπ ≫ E.torsionQuotientToSelf N = E.mulByHom (N : ℤ) :=
  ((E.torsionSubgroup N).quotient_lift (E.mulByHom (N : ℤ))
    (E.mulByHom_torsionSubgroup_isInvariant N)).choose_spec.1

end EllipticCurve

end ModularCurves
