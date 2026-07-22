/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SchemeActionFree
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# The quotient of a relatively-affine scheme by a finite group action (relative Spec)

For a finite group `G` acting on `Z` over `f : Z ⟶ S` **affine** (`hover : σ.hom γ ≫ f = f`),
we construct the quotient `Z/G` **over an arbitrary base `S`** — no separatedness or
affine-diagonal hypothesis on `Z` or `S` — as the glued relative Spec of the invariants
presheaf `U ↦ Γ(Z, f⁻¹U)ᴳ` on the small affine Zariski site of `S`.

This is the construction Katz–Mazur cite for the KM 7.1.3 quotient step (p. 190):

> "By [De-Ga III, §2, 6.1], we know that if a finite group `G` operates freely and
> `S`-linearly on an affine `S`-scheme `X`, then the quotient `X/G` exists, `X` is a
> finite etale `G`-torsor over `X/G`, and the formation of `X/G` commutes with arbitrary
> base-change `S′ → S`."

(The bare existence of the quotient — projection, structure map, categorical universal
property — needs **no freeness**; freeness enters only the finite-étale-torsor and
base-change addenda, exactly as in KM 7.1.3(2)/(3c) vs 7.1.3(1).)

The gluing engine is mathlib's `AlgebraicGeometry.relativeGluingData`
(`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean`, feeding
`Scheme.Cover.RelativeGluingData`, stacks 01LH), applied to the `Coequifibered`
structural map `𝒪_S ⟶ (U ↦ Γ(Z, f⁻¹U)ᴳ)`; the file is a line-by-line mirror of
`Mathlib/AlgebraicGeometry/Normalization.lean` (relative normalization, the same engine
applied to the integral-closure presheaf) with the invariants subalgebra in place of the
integral closure. The chart-level algebra ("localization of invariants = invariants of
the localization", the categorical quotient property of `Spec Aᴳ`, the free-action
finite/étale/torsor facts) is already proven in `ForMathlib/InvariantLocalization.lean`,
`ForMathlib/AffineQuotient.lean`, `ForMathlib/EtaleCancellation.lean` and
`ForMathlib/SchemeActionFree.lean`; this file only assembles it over the site.

This supersedes the affine-diagonal-gated glued quotient of
`ForMathlib/SchemeQuotient.lean` (T-Q5) as the foundation for the Γ_H quotient-problem
data: the three consumers in `Moduli/GammaHRepresentability.lean`
(`exists_quotient_of_isAffineHom`, `quotientπ_finite_etale_surjective`,
`exists_quotient_baseChange_of_free`) keep their conclusion shapes and lose the
`IsAffineHom (pullback.diagonal (terminal.from Z))` instance, which was FALSE for
general `Ell/R` bases (a constant curve over a plane with doubled origin).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

namespace SchemeAction

variable {G : Type*} [Group G] [Finite G] {Z S : Scheme.{u}}
variable (σ : SchemeAction G Z) (f : Z ⟶ S)
variable (hover : ∀ γ : G, σ.hom γ ≫ f = f)

/-! ### The invariants diagram on the small affine Zariski site of the base -/

include hover in
/-- The `f`-preimage of any open of the base is stable under an action over `f`
(immediate from `hover`; the atlas-stability observation of [GHB3], now a lemma). -/
theorem isStableOpen_preimage (U : S.Opens) : σ.IsStableOpen (f ⁻¹ᵁ U) := by
  sorry

/-- Restriction of sections along nested stable opens is `G`-equivariant: the section
action (`gammaMulSemiringAction`) commutes with the presheaf restriction map. -/
theorem gamma_map_smul {V U : Z.Opens} (hV : σ.IsStableOpen V) (hU : σ.IsStableOpen U)
    (hle : U ≤ V) (g : G) (s : Γ(Z, V)) :
    letI := σ.gammaMulSemiringAction hV
    letI := σ.gammaMulSemiringAction hU
    (Z.presheaf.map (homOfLE hle).op) (g • s) = g • (Z.presheaf.map (homOfLE hle).op) s := by
  sorry

/-- The base change of a scheme action lying over `S` along `g : T ⟶ S`: the induced
action on `pullback f g` (trivial on the `T`-leg). Needed to *state* KM 7.1.3(3c).

HOIST of `Moduli/GammaHRepresentability.lean`'s `SchemeAction.basePullback` (verbatim;
that file's copy is deleted when it imports this file — its own section banner already
says "`/cleanup` may relocate this section to `ForMathlib/`"). -/
noncomputable def basePullback
    {G : Type*} [Group G] {Z S T : Scheme.{u}}
    (σ : SchemeAction G Z) (f : Z ⟶ S) (hover : ∀ γ : G, σ.hom γ ≫ f = f)
    (g : T ⟶ S) : SchemeAction G (pullback f g) where
  hom γ := pullback.map f g f g (σ.hom γ) (𝟙 T) (𝟙 S)
    (by rw [Category.comp_id, hover γ]) (by rw [Category.comp_id, Category.id_comp])
  hom_one := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, σ.hom_one, Category.comp_id, Category.id_comp]
    · rw [pullback.lift_snd, Category.comp_id, Category.id_comp]
  hom_mul := fun a b => by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc,
        σ.hom_mul, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id, Category.comp_id]

/-- The invariants presheaf on the small affine Zariski site of `S`:
`U ↦ Γ(Z, f⁻¹U)ᴳ`. The relative-Spec substrate for the quotient `Z/G` over `S`
(mirror of `Scheme.Hom.normalizationDiagram` with the fixed-point subalgebra in place
of the integral closure). -/
def invariantsDiagram : S.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U :=
    letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover U.unop.1)
    .of (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ U.unop.1) G)
  map {V U} i :=
    letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover V.unop.1)
    letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover U.unop.1)
    CommRingCat.ofHom <|
      ((Z.presheaf.map (homOfLE (f.preimage_mono
          (Scheme.AffineZariskiSite.toOpens_mono i.unop.le))).op).hom.comp
        (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ V.unop.1) G).val.toRingHom).invariantsCorestrict
        (R₀ := ℤ) (fun g r => by
          have := σ.gamma_map_smul (σ.isStableOpen_preimage f hover V.unop.1)
            (σ.isStableOpen_preimage f hover U.unop.1)
            (f.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.unop.le)) g
            (r : Γ(Z, f ⁻¹ᵁ V.unop.1))
          sorry)
  map_id := by sorry
  map_comp := by sorry

/-- The structural map `𝒪_S ⟶ (U ↦ Γ(Z, f⁻¹U)ᴳ)`: per chart it is the descended
chart ring map `quotientDescRing` (the corestriction of `f.appLE` to the invariants,
[GHB3]-layer). Mirror of `normalizationDiagramMap`. -/
def invariantsDiagramMap :
    (Scheme.AffineZariskiSite.toOpensFunctor S).op ⋙ S.presheaf ⟶
      σ.invariantsDiagram f hover where
  app U := CommRingCat.ofHom
    (σ.quotientDescRing f hover U.unop.1 (σ.isStableOpen_preimage f hover U.unop.1))
  naturality := by sorry

/-- **Invariants form a quasi-coherent `𝒪_S`-algebra**: the structural map is
`Coequifibered`, i.e. `Γ(Z, f⁻¹(D_U(r)))ᴳ` is the away-localization of
`Γ(Z, f⁻¹U)ᴳ` at the (invariant) image of `r`. Chart-level content: `f` affine
identifies `Γ(Z, f⁻¹(D_U(r)))` with the localization of `Γ(Z, f⁻¹U)` at `f♯r`, and
"localization of invariants = invariants of the localization" for a finite group
(`ForMathlib/InvariantLocalization.lean`: `mem_range_fixedPoints_awayMap_iff`,
`fixedPoints_awayMap_injective`). KM's appendix A7.1 ambient fact; mirror of
`coequifibered_normalizationDiagramMap`. -/
theorem coequifibered_invariantsDiagramMap :
    (σ.invariantsDiagramMap f hover).Coequifibered := by
  sorry

/-! ### The quotient scheme, projection, and structure morphism -/

/-- The relative gluing datum of the invariants algebra (mirror of
`normalizationGlueData`). -/
def invariantsGlueData :=
  Scheme.AffineZariskiSite.relativeGluingData (σ.coequifibered_invariantsDiagramMap f hover)

/-- **The quotient of a relatively-affine scheme by a finite group action** over an
arbitrary base: the glued relative Spec of `U ↦ Γ(Z, f⁻¹U)ᴳ`. KM p. 190 / [De-Ga III
§2, 6.1] / SGA 3 V §4. NO hypotheses on `S` or on the diagonal of `Z`. -/
def relQuotient : Scheme.{u} :=
  (σ.invariantsGlueData f hover).glued

/-- The structure morphism `Z/G ⟶ S` (chartwise `Spec Γ(Z, f⁻¹U)ᴳ ⟶ U`). -/
def relQuotientStruct : σ.relQuotient f hover ⟶ S :=
  (σ.invariantsGlueData f hover).toBase

/-- The quotient projection `Z ⟶ Z/G`, glued over the directed affine cover of `S`
from the chartwise `Spec Γ(Z, f⁻¹U) ⟶ Spec Γ(Z, f⁻¹U)ᴳ` (mirror of
`toNormalization`). -/
def relQuotientπ : Z ⟶ σ.relQuotient f hover :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((Scheme.AffineZariskiSite.directedCover S).pullback₁ f)
    (fun U =>
      letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover U.1)
      (pullbackRestrictIsoRestrict f _).hom ≫ (f ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ U.1) G).val.toRingHom) ≫
        (σ.invariantsGlueData f hover).cover.f U)
    (by sorry)

/-- The projection descends `f`: `π ≫ f₀ = f`. -/
theorem relQuotientπ_comp_relQuotientStruct :
    σ.relQuotientπ f hover ≫ σ.relQuotientStruct f hover = f := by
  sorry

/-- The projection coequalizes the action. -/
theorem hom_comp_relQuotientπ (γ : G) :
    σ.hom γ ≫ σ.relQuotientπ f hover = σ.relQuotientπ f hover := by
  sorry

/-- **The chart bridge**: over each affine chart `U` of the base, the quotient
projection restricts to the affine invariants projection
`Spec Γ(Z, f⁻¹U) ⟶ Spec Γ(Z, f⁻¹U)ᴳ` — the square

`(f⁻¹U) → Spec Γ(Z, f⁻¹U)ᴳ`, `(f⁻¹U) ↪ Z`, `Spec Γ(Z, f⁻¹U)ᴳ → Z/G`, `Z ⟶ Z/G`

is a pullback. This is the transfer principle that lets every chart-local fact of
`ForMathlib/AffineQuotient.lean` / `ForMathlib/SchemeActionFree.lean` (finite, étale,
surjective, torsor, base-change) be read off on `relQuotientπ`; composition of
`isPullback_natTrans_ι_toBase` with the `glueMorphismsOfLocallyDirected` chart
triangle of `relQuotientπ`. -/
theorem isPullback_relQuotientπ_chart (U : S.AffineZariskiSite) :
    letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover U.1)
    IsPullback
      ((f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ U.1) G).val.toRingHom))
      (f ⁻¹ᵁ U.1).ι
      ((σ.invariantsGlueData f hover).cover.f U)
      (σ.relQuotientπ f hover) := by
  sorry

/-- The structure morphism of the quotient is affine (chartwise it is
`Spec Γ(Z, f⁻¹U)ᴳ ⟶ U`; affineness is Zariski-local on the target along the
directed cover, via `toBase_preimage_eq_opensRange_ι`). -/
instance isAffineHom_relQuotientStruct : IsAffineHom (σ.relQuotientStruct f hover) := by
  sorry

/-- The projection is integral (chartwise `Aᴳ → A` is integral: every `a` is a root of
`∏_g (T − g•a)`, KM 7.1.3(4) print p. 193; mathlib `Algebra.IsInvariant.isIntegral`). -/
instance isIntegralHom_relQuotientπ : IsIntegralHom (σ.relQuotientπ f hover) := by
  sorry

/-- **The categorical quotient property** (vs an ARBITRARY target scheme): an invariant
morphism `F : Z ⟶ Y` factors uniquely through the projection. Chart-level content is
`existsUnique_invariantsπ_lift` (`ForMathlib/AffineQuotient.lean`); glued over the
directed cover. Conclusion shape = the universal-property clause of the [GHB3]
`exists_quotient_of_isAffineHom` package. -/
theorem existsUnique_relQuotientπ_lift {Y : Scheme.{u}} (F : Z ⟶ Y)
    (hF : ∀ γ : G, σ.hom γ ≫ F = F) :
    ∃! q : σ.relQuotient f hover ⟶ Y, σ.relQuotientπ f hover ≫ q = F := by
  sorry

/-- **[GHB3′] (KM 7.1.3(1)/(3) existence, diagonal-free)** — the full package of the
former `exists_quotient_of_isAffineHom`, with the `IsAffineHom (pullback.diagonal
(terminal.from Z))` instance DELETED: for any affine invariant `f : Z ⟶ S` the
quotient exists with projection, structure map, invariance, and the categorical
universal property. This is the theorem that replaces the [GHB3] body and deletes
`hbase` from `nonempty_quotPkg` → `exists_quotientProblemData` →
`gammaH_relativelyRepresentable`. -/
theorem exists_quotient_of_isAffineHom_rel :
    ∃ (Z₀ : Scheme.{u}) (π : Z ⟶ Z₀) (f₀ : Z₀ ⟶ S), π ≫ f₀ = f ∧
      (∀ γ : G, σ.hom γ ≫ π = π) ∧
      ∀ {Y : Scheme.{u}} (F : Z ⟶ Y), (∀ γ : G, σ.hom γ ≫ F = F) →
        ∃! q : Z₀ ⟶ Y, π ≫ q = F := by
  sorry

/-! ### The free-action addenda: finite étale torsor, base change (KM 7.1.3(2),(3c)) -/

section Free

variable (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ Z) (γ : G), γ ≠ 1 →
  t ≫ σ.hom γ = t → IsEmpty T)

/-- Free case: the projection is finite (chartwise `Aᴳ → A` is module-finite for a free
algebra action, `Module.Finite.of_isFreeAlgebraAction`; local on the target along the
chart cover). -/
theorem isFinite_relQuotientπ_of_free : IsFinite (σ.relQuotientπ f hover) := by
  sorry

/-- Free case: the projection is étale (chartwise `Algebra.Etale.of_isFreeAlgebraAction`). -/
theorem etale_relQuotientπ_of_free : Etale (σ.relQuotientπ f hover) := by
  sorry

/-- Free case: the projection is surjective (chartwise `Spec A ⟶ Spec Aᴳ` is surjective:
`Aᴳ → A` is integral and injective... chart core as in `quotientπ_surjective`). -/
theorem surjective_relQuotientπ_of_free : Surjective (σ.relQuotientπ f hover) := by
  sorry

/-- **[GHB5′] (KM 7.1.3(3c), diagonal-free)** — for a free action the quotient commutes
with arbitrary base change `g : T ⟶ S`: the base-changed projection
`pullback f g ⟶ pullback f₀ g` satisfies the quotient universal property for the
base-changed action. Conclusion tuple = the former `exists_quotient_baseChange_of_free`
minus the diagonal instance. Chart-level content: `[A711-BC]`
(`fixedPointsBaseChange_bijective_of_isFreeAlgebraAction`) via
`exists_invariantsπ_lift_baseChange_of_free` (`ForMathlib/AffineQuotient.lean`);
uniqueness via `epi_pullback_snd_invariantsπ_of_free`. -/
theorem exists_relQuotient_baseChange_of_free {T : Scheme.{u}} (g : T ⟶ S) :
    ∃ πT : pullback f g ⟶ pullback (σ.relQuotientStruct f hover) g,
      πT ≫ pullback.snd (σ.relQuotientStruct f hover) g = pullback.snd f g ∧
      πT ≫ pullback.fst (σ.relQuotientStruct f hover) g =
        pullback.fst f g ≫ σ.relQuotientπ f hover ∧
      (∀ γ : G, (σ.basePullback f hover g).hom γ ≫ πT = πT) ∧
      ∀ {Y : Scheme.{u}} (F : pullback f g ⟶ Y),
        (∀ γ : G, (σ.basePullback f hover g).hom γ ≫ F = F) →
          ∃! q : pullback (σ.relQuotientStruct f hover) g ⟶ Y, πT ≫ q = F := by
  sorry

end Free

end SchemeAction

end AlgebraicGeometry

end
