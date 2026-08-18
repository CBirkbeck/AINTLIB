/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.Seesaw

/-!
# The seesaw theorem over an arbitrary base (`KM-SEESAW-GLOBAL`, T8b)

`ForMathlib/Seesaw.lean` proves Stacks `0EX7` at rank one for an **affine** reduced base. This
file removes the affineness, by running that theorem over each member of an affine open cover of
the base and gluing the results:

* `exists_pullback_iso_of_restrict_pullback_cover` — the **gluing step**, stated on its own
  because it is independently useful: an invertible `M` on `X` that is, over each member of an
  open cover of `S`, isomorphic to a pullback of an invertible module from that member, is
  globally a pullback of an invertible module from `S`. It is
  `WeilPairing/RelPicLocal.lean`'s `exists_pullback_twist_of_locally'` at `M' = 𝒪_X`, with the
  `𝒪_X`-twist stripped in the skeleton monoid;
* `exists_pullback_iso_of_fibrewise_trivial_of_isReduced_of_affineCover` — the **seesaw over an
  arbitrary base**, the composition of the affine seesaw over `S.affineOpens` with that gluing.

## Why this ticket exists

The consumer is the relative theorem of the square (`Picard/SelfAdjointN.lean`), which applies the
seesaw over `B = C ×_U C`, the universal pair of points. `B` is reduced — indeed integral — but is
**not affine**, while `exists_pullback_iso_of_fibrewise_trivial_of_isReduced` carries
`[IsAffine S]`.

## Hypothesis transport (step 1)

Restricting the family along an open `V ⊆ S` means replacing `π : X ⟶ S` by
`π ∣_ V : π ⁻¹ᵁ V ⟶ V` and `M` by `M.restrict (π ⁻¹ᵁ V).ι`. Of the affine seesaw's hypotheses:

* `IsReduced`, `LocallyOfFinitePresentation`, `IsProper`, `Flat` are found by `inferInstance` —
  the first because reducedness is local, the last three by `IsZariskiLocalAtTarget.restrict`;
* `IsNoetherian` and `Scheme.IsSeparated` need the one-line bridges `isNoetherian_opens` and
  `isSeparated_opens` below. (`IsLocallyNoetherian` on an open *is* an instance; only
  `CompactSpace ↥U`, which mathlib does supply for `↥(U : Set X)`, fails to be found through the
  `U.toScheme` carrier wrapper, so it is fed by `inferInstanceAs`.)
* `UniversallyOConnected` restricts (`UniversallyOConnected.restrict`): a base change of `π ∣_ V`
  along `g : T ⟶ V` is, by pasting with `isPullback_morphismRestrict`, a base change of `π` along
  `g ≫ V.ι`, and the definition quantifies over *all* base changes.
* `hfib` restricts (`nonempty_pullback_fst_restrict_unitObj_iso`) by the same pasting: a
  field-valued point `x` of `V` is the point `x ≫ V.ι` of `S`, and the fibre-product identification
  carries the trivialisation across `pullbackComp`/`pullbackCongr`/`pullbackUnitIso`.

## The shape of `hhigh`

The affine seesaw's `hhigh` — exactness of the ordered base-Čech complex at positions `≥ 2` — is
quantified over all finite affine open covers **of the total space**, because the cover is produced
inside its proof and it gets no control on it. Here the total space varies with the piece, so the
hypothesis is quantified over **all opens `W ⊆ S`** and all finite affine covers of `π ⁻¹ᵁ W`.

That is the second of the two shapes the ticket allowed, and it is chosen over "quantify over each
`i` of a cover" because the cover of `S` is likewise produced inside the proof (it is
`S.affineOpens`), so a per-`i` form would have to name that cover in the statement and would
thereby fix it — an artificial constraint on a consumer that must supply `hhigh` anyway. Quantifying
over all opens is strictly more uniform and costs the consumer nothing: for a relative curve
`H^{≥2}` vanishes on every fibre, hence over every open of the base, exactly as it does globally.

## Consumer

`Picard/SelfAdjointN.lean`'s `exists_invertible_tensor_idealModule_add`, the single classical leaf
under `(★)`/`(★′)` and hence under the Katz–Mazur construction of the relative Weil pairing (DS4).
-/

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace ModularCurves

/-! ### Hypothesis transport along an open of the base -/

/-- An open subscheme of a Noetherian scheme is Noetherian.

`IsLocallyNoetherian` on an open is already an instance; the compactness half is
`NoetherianSpace.compactSpace` on the *set* `↑U`, which instance search does not reach through the
`U.toScheme` carrier wrapper, hence the `inferInstanceAs`. -/
theorem isNoetherian_opens {X : Scheme.{u}} [IsNoetherian X] (U : X.Opens) :
    IsNoetherian U.toScheme :=
  haveI : CompactSpace U.toScheme := inferInstanceAs (CompactSpace (U : Set X))
  ⟨⟩

/-- An open subscheme of a separated scheme is separated: `U.ι` is a monomorphism, hence
separated, and `terminal.from U = U.ι ≫ terminal.from X`. -/
theorem isSeparated_opens {X : Scheme.{u}} [X.IsSeparated] (U : X.Opens) :
    U.toScheme.IsSeparated := by
  constructor
  rw [← terminal.comp_from U.ι]
  infer_instance

/-- **Universal `O`-connectedness restricts to an open of the base.**

`UniversallyOConnected p` quantifies over *all* base changes of `p`, and a base change of `π ∣_ V`
along `g : T ⟶ V` is a base change of `π` along `g ≫ V.ι`: paste the pullback square of
`Limits.pullback (π ∣_ V) g` with `isPullback_morphismRestrict π V`. The section-components then
transport along the resulting `isoPullback`, exactly as in `UniversallyOConnected.isIso_app`. -/
theorem UniversallyOConnected.restrict {X S : Scheme.{u}} {π : X ⟶ S}
    (hπ : UniversallyOConnected π) (V : S.Opens) :
    UniversallyOConnected (π ∣_ V) := by
  intro T g W
  have hpb : IsPullback (Limits.pullback.fst (π ∣_ V) g ≫ (π ⁻¹ᵁ V).ι)
      (Limits.pullback.snd (π ∣_ V) g) π (g ≫ V.ι) :=
    (IsPullback.of_hasPullback (π ∣_ V) g).paste_horiz (isPullback_morphismRestrict π V).flip
  have h2 : IsIso ((hpb.isoPullback.hom ≫ Limits.pullback.snd π (g ≫ V.ι)).app W) := by
    rw [Scheme.Hom.comp_app]
    exact IsIso.comp_isIso' (hπ (g ≫ V.ι) W)
      (Scheme.Hom.instIsIsoCommRingCatApp hpb.isoPullback.hom _)
  rwa [hpb.isoPullback_hom_snd] at h2

/-- **Fibrewise triviality restricts to an open of the base.**

A point `x : T ⟶ V` of an open of `S` is the point `x ≫ V.ι` of `S`, and by the same pasting as in
`UniversallyOConnected.restrict` the two fibre products agree compatibly with their *first*
projections. So a trivialisation of `M` on the fibre of `π` over `x ≫ V.ι` becomes one of
`M|_{π⁻¹V}` on the fibre of `π ∣_ V` over `x`, transported along
`restrictFunctorIsoPullback`, `pullbackComp`, `pullbackCongr` and `pullbackUnitIso`. -/
theorem nonempty_pullback_fst_restrict_unitObj_iso {X S T : Scheme.{u}} (π : X ⟶ S)
    (V : S.Opens) (x : T ⟶ V.toScheme) {M : X.Modules}
    (h : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
      (Limits.pullback.fst π (x ≫ V.ι))).obj M ≅ unitObj (Limits.pullback π (x ≫ V.ι)))) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
      (Limits.pullback.fst (π ∣_ V) x)).obj (M.restrict (π ⁻¹ᵁ V).ι) ≅
        unitObj (Limits.pullback (π ∣_ V) x)) := by
  obtain ⟨h⟩ := h
  have hpb : IsPullback (Limits.pullback.fst (π ∣_ V) x ≫ (π ⁻¹ᵁ V).ι)
      (Limits.pullback.snd (π ∣_ V) x) π (x ≫ V.ι) :=
    (IsPullback.of_hasPullback (π ∣_ V) x).paste_horiz (isPullback_morphismRestrict π V).flip
  refine ⟨?_⟩
  calc (AlgebraicGeometry.Scheme.Modules.pullback
        (Limits.pullback.fst (π ∣_ V) x)).obj (M.restrict (π ⁻¹ᵁ V).ι)
      ≅ (AlgebraicGeometry.Scheme.Modules.pullback (Limits.pullback.fst (π ∣_ V) x)).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj M) :=
        (AlgebraicGeometry.Scheme.Modules.pullback _).mapIso
          ((restrictFunctorIsoPullback (π ⁻¹ᵁ V).ι).app M)
    _ ≅ (AlgebraicGeometry.Scheme.Modules.pullback
          (Limits.pullback.fst (π ∣_ V) x ≫ (π ⁻¹ᵁ V).ι)).obj M :=
        (pullbackComp (Limits.pullback.fst (π ∣_ V) x) (π ⁻¹ᵁ V).ι).app M
    _ ≅ (AlgebraicGeometry.Scheme.Modules.pullback
          (hpb.isoPullback.hom ≫ Limits.pullback.fst π (x ≫ V.ι))).obj M :=
        (pullbackCongr hpb.isoPullback_hom_fst.symm).app M
    _ ≅ (AlgebraicGeometry.Scheme.Modules.pullback hpb.isoPullback.hom).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (Limits.pullback.fst π (x ≫ V.ι))).obj M) :=
        ((pullbackComp hpb.isoPullback.hom (Limits.pullback.fst π (x ≫ V.ι))).app M).symm
    _ ≅ (AlgebraicGeometry.Scheme.Modules.pullback hpb.isoPullback.hom).obj
          (unitObj (Limits.pullback π (x ≫ V.ι))) :=
        (AlgebraicGeometry.Scheme.Modules.pullback hpb.isoPullback.hom).mapIso h
    _ ≅ unitObj (Limits.pullback (π ∣_ V) x) := pullbackUnitIso hpb.isoPullback.hom

/-! ### The gluing step -/

/-- **Being a pullback from the base is Zariski-local on the base.**

If an invertible `M` on `X` is, over each member `U i` of an open cover of `S`, isomorphic to the
pullback of an invertible `N i` on `U i`, then `M` is the pullback of a single invertible `N₀` on
`S`. This is `exists_pullback_twist_of_locally'` (`WeilPairing/RelPicLocal.lean`) at `M' = 𝒪_X`,
with both `𝒪_X`-twists stripped in the skeleton monoid — the trivial-twist manipulation is the
one already performed by `ForMathlib/Seesaw.lean`'s own assembly.

`hπ` is the section-component hypothesis the descent consumes;
`UniversallyOConnected.isIso_app` supplies it for a universally `O`-connected `π`. The cover need
not be finite. -/
theorem exists_pullback_iso_of_restrict_pullback_cover {X S : Scheme.{u}} (π : X ⟶ S)
    (hπ : ∀ W : S.Opens, IsIso (π.app W))
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} (U : ι → S.Opens) (hU : IsOpenCover U)
    (N : ∀ i, (U i).toScheme.Modules) (hN : ∀ i, IsInvertible (N i))
    (he : ∀ i, Nonempty (M.restrict (π ⁻¹ᵁ U i).ι ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (π ∣_ U i)).obj (N i))) :
    ∃ N₀ : S.Modules, IsInvertible N₀ ∧
      Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback π).obj N₀) := by
  -- the descent consumes the local trivialisations in twisted form; the `𝒪_X` twist is trivial
  have hglue : ∀ i, Nonempty (M.restrict (π ⁻¹ᵁ U i).ι ≅
      tensorObj ((unitObj X).restrict (π ⁻¹ᵁ U i).ι)
        ((AlgebraicGeometry.Scheme.Modules.pullback (π ∣_ U i)).obj (N i))) := by
    intro i
    letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory (π ⁻¹ᵁ U i).toScheme
    letI := AlgebraicGeometry.Scheme.Modules.symmetricCategory (π ⁻¹ᵁ U i).toScheme
    refine toSkeleton_eq_toSkeleton_iff.mp ?_
    have h1 : toSkeleton ((unitObj X).restrict (π ⁻¹ᵁ U i).ι) = 1 :=
      (toSkeleton_eq_toSkeleton_iff.mpr
        ⟨(restrictFunctorIsoPullback (π ⁻¹ᵁ U i).ι).app (unitObj X) ≪≫
          pullbackUnitIso (π ⁻¹ᵁ U i).ι⟩).trans toSkeleton_unitObj
    rw [toSkeleton_tensorObj_eq, h1, one_mul]
    exact toSkeleton_eq_toSkeleton_iff.mpr (he i)
  obtain ⟨N₀, hN₀, e⟩ := exists_pullback_twist_of_locally' π hπ hM isInvertible_unit U hU N hN hglue
  -- `𝒪_X ⊗ π^*N₀ ≅ π^*N₀`, so the twisted conclusion is the seesaw's
  refine ⟨N₀, hN₀, ?_⟩
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  letI := AlgebraicGeometry.Scheme.Modules.symmetricCategory X
  refine toSkeleton_eq_toSkeleton_iff.mp ?_
  have he' := toSkeleton_eq_toSkeleton_iff.mpr e
  rwa [toSkeleton_tensorObj_eq, toSkeleton_unitObj, one_mul] at he'

/-! ### The seesaw over an arbitrary base -/

/-- **(KM-SEESAW-GLOBAL, Stacks 0EX7 at rank 1, arbitrary base)** The seesaw theorem without the
affineness of the base: an invertible sheaf on a proper flat family of finite presentation over a
**reduced** (Noetherian) base, trivial on every fibre, is pulled back from the base.

Two steps, neither of which touches the affine seesaw's internals.

1. Apply `exists_pullback_iso_of_fibrewise_trivial_of_isReduced` to `π ∣_ W` and
   `M.restrict (π ⁻¹ᵁ W).ι` for each `W : S.affineOpens`. The hypothesis transport is
   `isNoetherian_opens`, `isSeparated_opens`, `UniversallyOConnected.restrict` and
   `nonempty_pullback_fst_restrict_unitObj_iso`; `IsReduced`, `IsProper`, `Flat` and
   `LocallyOfFinitePresentation` are `inferInstance`, and `IsInvertible` restricts through
   `IsInvertible.pullback` along `restrictFunctorIsoPullback`.
2. Glue with `exists_pullback_iso_of_restrict_pullback_cover` over the affine open cover
   `iSup_affineOpens_eq_top`, whose section-component hypothesis is `hπ.isIso_app`.

`hhigh` is the affine seesaw's positive-degree exactness hypothesis relativised to every open of
the base; see the module docstring for why that shape was chosen. -/
theorem exists_pullback_iso_of_fibrewise_trivial_of_isReduced_of_affineCover
    {X S : Scheme.{u}} [IsReduced S] [IsNoetherian S] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S} [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    (hhigh : ∀ (W : S.Opens) {ι : Type u} [Fintype ι] [LinearOrder ι]
      (U : ι → (π ⁻¹ᵁ W).toScheme.Opens), IsOpenCover U → (∀ i, IsAffineOpen (U i)) →
      ∀ q, 1 ≤ q → q < Fintype.card ι →
        Function.Exact
          ((orderedBaseCechComplex (π ∣_ W) (M.restrict (π ⁻¹ᵁ W).ι) U).d q (q + 1)).hom
          ((orderedBaseCechComplex (π ∣_ W) (M.restrict (π ⁻¹ᵁ W).ι) U).d (q + 1) (q + 2)).hom)
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (Limits.pullback.fst π x)).obj M ≅ unitObj (Limits.pullback π x))) :
    ∃ N : S.Modules, IsInvertible N ∧
      Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback π).obj N) := by
  have hV : IsOpenCover (fun W : S.affineOpens => (W : S.Opens)) := iSup_affineOpens_eq_top S
  -- Step 1: the affine-base seesaw on the restricted family, over each affine open of the base
  have hpiece : ∀ W : S.affineOpens, ∃ N : (W : S.Opens).toScheme.Modules, IsInvertible N ∧
      Nonempty (M.restrict (π ⁻¹ᵁ (W : S.Opens)).ι ≅
        (AlgebraicGeometry.Scheme.Modules.pullback (π ∣_ (W : S.Opens))).obj N) := by
    intro W
    haveI : IsAffine (W : S.Opens).toScheme := W.2
    haveI : IsNoetherian (W : S.Opens).toScheme := isNoetherian_opens _
    haveI : IsNoetherian (π ⁻¹ᵁ (W : S.Opens)).toScheme := isNoetherian_opens _
    haveI : (π ⁻¹ᵁ (W : S.Opens)).toScheme.IsSeparated := isSeparated_opens _
    exact exists_pullback_iso_of_fibrewise_trivial_of_isReduced (hπ.restrict (W : S.Opens))
      ((hM.pullback (π ⁻¹ᵁ (W : S.Opens)).ι).of_iso
        ((restrictFunctorIsoPullback (π ⁻¹ᵁ (W : S.Opens)).ι).app M))
      (hhigh (W : S.Opens))
      (fun {_} _ x => nonempty_pullback_fst_restrict_unitObj_iso π (W : S.Opens) x
        (hfib (x ≫ (W : S.Opens).ι)))
  choose N hN he using hpiece
  -- Step 2: glue over the affine open cover of the base
  exact exists_pullback_iso_of_restrict_pullback_cover π hπ.isIso_app hM
    (fun W : S.affineOpens => (W : S.Opens)) hV N hN he

end ModularCurves
