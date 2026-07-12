/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves stream D
-/
import ModularCurves.GroupScheme.NIsogeny
import ModularCurves.ForMathlib.GrassmannianGlueData

/-!
# The moduli space of `N`-isogeny data ([L15] = KM 6.5.1) — STREAM-NISOG wave M2

KM Proposition 6.5.1 (print p. 165, verbatim): *"Given `E/S`, view `E[N]/S` as the `Spec`
of a coherent sheaf `𝓕` of bi-algebras on `S` which is locally free of rank `N²`. A
subgroup `G ⊆ E[N]` of the type being sought is nothing other than a locally free rank-`N`
quotient `𝔥` of `𝓕`, such that the locally free rank `N²−N` kernel `𝒦 ⊆ 𝓕` is a bi-ideal
in `𝓕`. Therefore `[N-Isog]` is relatively represented by a closed subscheme of the
Grassmannian of all rank `N` quotients of `𝓕`."*

This file executes the decomposition `.mathlib-quality/decomposition-nisog-L15.md`:

* [L15-b] the dictionary: `N`-isogeny data ↔ Grassmannian members (`Module.Grassmannian`,
  whose members are exactly KM's kernels `𝒦` with locally free rank-`N` quotient) that are
  bi-ideals. The bialgebra structure on the torsion sections is **hypothesis-wired**: c5β's
  E[N]-package (CHARTER-C5B-2) supplies the finite-locally-free facts, and NEW-HOPF's pins
  supply the comultiplication; until they land, both enter as explicit hypotheses/data.
* [L15-c] the relative Grassmannian over `S` (charts = fable-FP's `grassmannianScheme`
  over trivializing affines; delivered gate, zero sorries).
* [L15-d] the bi-ideal locus is closed (T-D15/LFP-arc toolbox).
* [L15-e] classification via `pointOfMember` (gate-proven forward map).
* [L15-f] finiteness (KM's fibre count; c5β substrate hypothesis-wired).
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct ModularCurves.EllipticCurve

universe u

namespace ModularCurves

variable {S : Scheme.{u}}

/-! ## The bi-ideal condition (KM 6.5.1's "is a bi-ideal in 𝓕")

Stated abstractly for a commutative ring `A`, an `A`-algebra `F` carrying comultiplication
and counit data (the bialgebra structure of the torsion sections — supplied by the
NEW-HOPF pins at consumption time), and a submodule `K ⊆ F`. -/

/-- **(KM 6.5.1, the cut condition)** A submodule `K` of an `A`-bialgebra `F` (presented
by explicit comultiplication `Δ` and counit `ε` data) is a *bi-ideal* when it is an ideal,
is killed by the counit, and is a coideal for the comultiplication:
`Δ K ⊆ K ⊗ F + F ⊗ K`. These are the equations KM cuts the Grassmannian by. -/
def IsBiIdeal {A : Type u} [CommRing A] {F : Type u} [CommRing F] [Algebra A F]
    (Δ : F →ₐ[A] F ⊗[A] F) (ε : F →ₐ[A] A) (K : Submodule A F) : Prop :=
  (∀ (f : F) (k : F), k ∈ K → f * k ∈ K) ∧
    (∀ k ∈ K, ε k = 0) ∧
      ∀ k ∈ K, Δ k ∈
        LinearMap.range (TensorProduct.map K.subtype (LinearMap.id (R := A) (M := F))) ⊔
          LinearMap.range (TensorProduct.map (LinearMap.id (R := A) (M := F)) K.subtype)

variable {A : Type u} [CommRing A] {F : Type u} [CommRing F] [Algebra A F]
  {Δ : F →ₐ[A] F ⊗[A] F} {ε : F →ₐ[A] A} {K : Submodule A F}

/-- The ideal clause of `IsBiIdeal`: `K` is closed under multiplication by `F`, so it is an
ideal of the ring `F` (KM's *"the kernel `𝒦 ⊆ 𝓕`"* is an ideal — the algebra half of
bi-ideal). Its underlying `A`-submodule is `K`. -/
def IsBiIdeal.toIdeal (h : IsBiIdeal Δ ε K) : Ideal F where
  carrier := K
  add_mem' := K.add_mem
  zero_mem' := K.zero_mem
  smul_mem' c x hx := by
    rw [smul_eq_mul]; exact h.1 c x hx

@[simp] theorem IsBiIdeal.mem_toIdeal (h : IsBiIdeal Δ ε K) {x : F} :
    x ∈ h.toIdeal ↔ x ∈ K := Iff.rfl

/-- The counit kills a bi-ideal. -/
theorem IsBiIdeal.counit_eq_zero (h : IsBiIdeal Δ ε K) {k : F} (hk : k ∈ K) : ε k = 0 :=
  h.2.1 k hk

/-! ## The `N`-isogeny moduli representation (the hypothesis-wired assembly interface)

KM 6.5.1 relatively represents `[N-Isog]` by a closed subscheme of the Grassmannian of
rank-`N` quotients of `𝓕 = O(E[N])`, cut by the bi-ideal condition, and shows it is finite
over the base. Three external inputs gate this construction, none yet landed:

* the **bialgebra sheaf** `𝓕` with its comultiplication/counit — c5β's E[N]-package
  (`CHARTER-C5B-2`) for the rank-`N²` local-freeness (`torsionπ_isFinite`/`_flat`/`torsion_rank`,
  stated, sorry-backed via the BB-boxes) and NEW-HOPF's C-layer for the comultiplication;
* the **subgroup ↔ bi-ideal dictionary** (Hopf-ideal correspondence) — NEW-HOPF's pins;
* **relative representability** of the Grassmannian — fable-FP's `grassmannianScheme`
  (forward `pointOfMember` proven) plus its boarded global-descent leaf.

Per charter (`v10.162`), these are hypothesis-wired into the record below; when the gates
close it is populated and `exists_nIsogSpace` is axiom-clean. -/

variable (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-- **Base change of an `N`-isogeny datum** along `g : T ⟶ S`: the base-changed subgroup
scheme, of the same rank. This is the functoriality of the moduli problem
`T ↦ NIsogenyStructure (E_T) N` — the coherence a *representing* (functorial)
`NIsogRepresentation` needs so that a `T`-point pulls back the universal datum (see the
Y₀(N) assembly finding in `decomposition-nisog-L15.md`). -/
noncomputable def _root_.ModularCurves.EllipticCurve.NIsogenyStructure.baseChange
    {E : EllipticCurve S} {N : ℕ} [NeZero N] (nis : NIsogenyStructure E N)
    {T : Scheme.{u}} (g : T ⟶ S) : NIsogenyStructure (E.baseChange g) N where
  subgroup := nis.subgroup.baseChange g
  hasRank := nis.hasRank.baseChange g

/-- **The subgroup-divisor commutes with base change (ideal form)** — the keystone for the
Y₀(N) assembly. The divisor of the base-changed subgroup scheme equals the base change of
the subgroup's divisor: both are `G.ι.ker` pulled back along `pullback.fst E.π g`. This lets
the cyclicity of a base-changed subgroup be read off the universal cyclicity locus. -/
theorem FiniteLocallyFreeSubgroup.toRelEffCartierDiv_baseChange_ideal
    {E : EllipticCurve S} (G : FiniteLocallyFreeSubgroup E) {T : Scheme.{u}} (g : T ⟶ S) :
    (G.baseChange g).toRelEffCartierDiv.ideal = (G.toRelEffCartierDiv.baseChange g).ideal := by
  haveI := G.closedImmersion
  rw [FiniteLocallyFreeSubgroup.toRelEffCartierDiv_ideal,
    RelEffCartierDiv.baseChange_ideal,
    FiniteLocallyFreeSubgroup.toRelEffCartierDiv_ideal]
  show (Limits.pullback.snd G.ι (Limits.pullback.fst E.π g)).ker =
      (Scheme.Hom.ker G.ι).comap (Limits.pullback.fst E.π g)
  rw [show (Limits.pullback.snd G.ι (Limits.pullback.fst E.π g)) =
      (Limits.pullbackSymmetry G.ι (Limits.pullback.fst E.π g)).hom ≫
        Limits.pullback.fst (Limits.pullback.fst E.π g) G.ι from
    (Limits.pullbackSymmetry_hom_comp_fst _ _).symm,
    Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- **[L15] the `N`-isogeny moduli representation** (hypothesis-wired pins-record). A finite
`S`-scheme `W` whose `T`-points classify `N`-isogeny data on `E ×_S T` — exactly the closed
subscheme of the Grassmannian of `𝓕` cut by the bi-ideal condition (KM 6.5.1). This bundles
the three gated inputs above; everything downstream lands on it. -/
structure NIsogRepresentation where
  /-- The moduli scheme of `N`-isogeny data. -/
  W : Scheme.{u}
  /-- Its structure morphism to the base. -/
  w : W ⟶ S
  /-- Finiteness over the base (KM 6.5.1: finite fibres via the prime-power fibre count). -/
  finite : IsFinite w
  /-- The classifying equivalence (KM 6.5.1's relative representability, through the bi-ideal
  Grassmannian and `pointOfMember`). -/
  classify : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S),
    Nonempty (NIsogenyStructure (E.baseChange t) N ≃ { h : T ⟶ W // h ≫ w = t })

/-- **[L15] the assembly** — `exists_nIsogSpace` follows from any `N`-isogeny moduli
representation. The representation is the hypothesis-wired composite of the three gates;
this theorem is the mechanical extraction, so `exists_nIsogSpace` closes with zero further
wiring the moment the gates land. -/
theorem exists_nIsogSpace_of_representation (r : NIsogRepresentation E N) :
    ∃ (W : Scheme.{u}) (w : W ⟶ S), IsFinite w ∧
      ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S),
        Nonempty (NIsogenyStructure (E.baseChange t) N ≃ { h : T ⟶ W // h ≫ w = t }) :=
  ⟨r.W, r.w, r.finite, r.classify⟩

end ModularCurves
