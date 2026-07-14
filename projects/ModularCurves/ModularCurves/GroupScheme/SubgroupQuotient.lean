import ModularCurves.GroupScheme.SubgroupQuotientGlueData

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

namespace FiniteLocallyFreeSubgroup

/-- **(T-G3d-infra)** The quotient scheme `E/G` of `E` by the finite locally free subgroup
scheme `G`, over `S` — **the option-γ glue construction** (`SubgroupQuotientGlueData`): one free
affine chart patch per point of the curve, one Hopf-coinvariant patch quotient per point, glued
along the saturated images of the pairwise stable windows. Requires the killing-integer datum
`[G.HasKillingInt]` (automatic for torsion subgroups; by Deligne–Oort–Tate for constant rank).
Consumers use only the universal-property pins below. -/
noncomputable def quotient (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] : Scheme.{u} :=
  G.gluedQuotient G.killN G.killN_spec

/-- **(T-G3d-infra)** The structure morphism `E/G ⟶ S`. -/
noncomputable def quotientS (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    G.quotient ⟶ S :=
  G.gluedQuotientS G.killN G.killN_spec

/-- **(T-G3d-infra)** The quotient isogeny `E ⟶ E/G` (finite locally free of degree
`rank G`; for `G = E[N]` this is the map whose factorization of `[N]` gives `E/E[N] ≅ E`). -/
noncomputable def quotientπ (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    E.E ⟶ G.quotient :=
  G.gluedQuotientπ G.killN G.killN_spec

/-- **(T-G3d-infra pin)** The quotient isogeny is a morphism over `S`: `π ≫ (E/G ⟶ S) = E.π`. -/
theorem quotientπ_over (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    G.quotientπ ≫ G.quotientS = E.π :=
  G.gluedQuotientπ_gluedQuotientS G.killN G.killN_spec

/-- **(T-G3d-infra pin)** The quotient isogeny is `G`-invariant: it collapses each `G`-translate. -/
theorem quotientπ_isInvariant (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    G.IsInvariant G.quotientπ :=
  G.isInvariant_gluedQuotientπ G.killN G.killN_spec

/-- **(T-G3d-infra pin — universal property)** Every `G`-invariant `f : E ⟶ Y` factors **uniquely**
through the quotient: there is a unique `h : E/G ⟶ Y` with `π ≫ h = f`. This categorical-quotient
property is what the whole layer exists to supply; the `[N]`-invariance of `[N] : E ⟶ E` then yields
the factorization `E/E[N] ⟶ E` (T-G3d). -/
theorem quotient_lift (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] {Y : Scheme.{u}}
    (f : E.E ⟶ Y) (hf : G.IsInvariant f) :
    ∃! h : G.quotient ⟶ Y, G.quotientπ ≫ h = f :=
  G.gluedQuotient_existsUnique_lift G.killN G.killN_spec f hf

/-- **(T-G3d-infra — `π` is an epimorphism)** Morphisms out of `E/G` are determined by their
composition with the quotient isogeny. PROVED from `quotient_lift` + `quotientπ_isInvariant`
(the common composite `π ≫ h₁` is `G`-invariant, so both `h₁, h₂` are *the* lift of it). -/
theorem quotientπ_hom_ext (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] {Y : Scheme.{u}}
    (h₁ h₂ : G.quotient ⟶ Y) (H : G.quotientπ ≫ h₁ = G.quotientπ ≫ h₂) : h₁ = h₂ := by
  obtain ⟨_, _, huniq⟩ := G.quotient_lift (G.quotientπ ≫ h₁) (G.quotientπ_isInvariant.comp h₁)
  exact (huniq h₁ rfl).trans (huniq h₂ H.symm).symm

end FiniteLocallyFreeSubgroup

/-- **The torsion subgroup carries its killing integer by definition of the kernel**: the
pullback condition of `E[N] = E ×_{[N], E, 0} S` says exactly `ι ≫ [N] = π ≫ 0`. -/
instance (N : ℕ) [NeZero N] : (E.torsionSubgroup N).HasKillingInt :=
  ⟨N, NeZero.ne N,
    (pullback.condition (f := E.mulByHom N) (g := E.zero)).trans
      (congrArg (· ≫ E.zero) (E.torsionι_π N)).symm⟩

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
