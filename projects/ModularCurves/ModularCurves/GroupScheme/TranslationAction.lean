import ModularCurves.GroupScheme.SubgroupQuotientInterface

/-!
# The translation action of a finite locally free subgroup scheme

**Construction support for `T-G3d-infra`** (`GroupScheme/SubgroupQuotient.lean`). The quotient
`E/G` is the coequalizer of the two maps `G ×_S E ⇉ E` — the translation action `(t, x) ↦ x + t`
and the projection `(t, x) ↦ x`. This file builds those two maps in `Over S` (where the group
multiplication `μ[E.asOver]` and the over-`S` compatibility live), as the foundation of the
construction (Piece 2 of `.mathlib-quality/decomposition-g3d-infra.md`: the translation co-action
`ρ : O_E → O_E ⊗ O_G` is the structure-sheaf dual of `translationAction`).

Working in `Over S` keeps the two maps morphisms of the cartesian-monoidal group object `E.asOver`,
so their over-`S` compatibility (`… ≫ E.π = pr ≫ E.π`) is `Over.w`, free.

## Main definitions
* `FiniteLocallyFreeSubgroup.translationAction` — `G ×_S E ⟶ E`, `(t, x) ↦ x + ι t`, as an
  `Over S`-morphism `(Over.mk G.π) ⊗ E.asOver ⟶ E.asOver`.
* `FiniteLocallyFreeSubgroup.actionProj` — the projection `G ×_S E ⟶ E`, `(t, x) ↦ x`.

## Main results
* `translationAction_left_π` / `actionProj_left_π` — both are morphisms over `S` (free from `Over`).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} {E : EllipticCurve S}

namespace FiniteLocallyFreeSubgroup

/-- The closed immersion `ι : G ⟶ E` as a morphism over `S` (`G.ι ≫ E.π = G.π` definitionally). -/
noncomputable def ιOver (G : FiniteLocallyFreeSubgroup E) : Over.mk G.π ⟶ E.asOver :=
  Over.homMk G.ι rfl

@[simp]
theorem ιOver_left (G : FiniteLocallyFreeSubgroup E) : G.ιOver.left = G.ι := rfl

/-- **The translation action `G ×_S E ⟶ E`, `(t, x) ↦ x + ι t`**, as an `Over S`-morphism: include
`G` into `E` on the first factor, then apply the group multiplication `μ[E.asOver]`. The quotient
`E/G` is the coequalizer of this with `actionProj`; the structure-sheaf dual of its underlying map
is the translation co-action `ρ` cutting out the co-invariants (Piece 2). -/
noncomputable def translationAction (G : FiniteLocallyFreeSubgroup E) :
    (Over.mk G.π) ⊗ E.asOver ⟶ E.asOver :=
  (G.ιOver ⊗ₘ 𝟙 E.asOver) ≫ μ[E.asOver]

/-- The other coequalizer leg: the projection `G ×_S E ⟶ E`, `(t, x) ↦ x`. -/
noncomputable def actionProj (G : FiniteLocallyFreeSubgroup E) :
    (Over.mk G.π) ⊗ E.asOver ⟶ E.asOver :=
  snd (Over.mk G.π) E.asOver

/-- The translation action in **hom-group form**: `act = (pr_G ≫ ι) * pr_E`, where `*` is the
pointwise group law on `Over S`-morphisms into the group object `E.asOver` (`Hom.commGroup`). This
is the bridge from the monoidal spelling `(ι ⊗ 𝟙) ≫ μ` to the point-addition spelling used to match
`IsInvariant`: on `T`-points, `act(t, x) = ι(t) + x`. -/
theorem translationAction_eq_mul (G : FiniteLocallyFreeSubgroup E) :
    letI : CommGroup ((Over.mk G.π) ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
    G.translationAction
      = (fst (Over.mk G.π) E.asOver ≫ G.ιOver) * snd (Over.mk G.π) E.asOver := by
  letI : CommGroup ((Over.mk G.π) ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
  have h : (G.ιOver ⊗ₘ 𝟙 E.asOver)
      = lift (fst (Over.mk G.π) E.asOver ≫ G.ιOver) (snd (Over.mk G.π) E.asOver) := by
    refine hom_ext _ _ ?_ ?_ <;> simp
  rw [Hom.mul_def, translationAction, h]

/-- The translation action is a morphism over `S`: `act ≫ E.π = (G ×_S E ⟶ S)`. Free from `Over`. -/
@[reassoc]
theorem translationAction_left_π (G : FiniteLocallyFreeSubgroup E) :
    G.translationAction.left ≫ E.π = ((Over.mk G.π) ⊗ E.asOver).hom :=
  Over.w G.translationAction

/-- The projection leg is a morphism over `S`. Free from `Over`. -/
@[reassoc]
theorem actionProj_left_π (G : FiniteLocallyFreeSubgroup E) :
    G.actionProj.left ≫ E.π = ((Over.mk G.π) ⊗ E.asOver).hom :=
  Over.w G.actionProj

/-- **Forward bridge (`IsInvariant ⟹ coequalizes`).** If `f` is invariant under translation by `G`,
then it coequalizes the two legs `act, pr_E : G ×_S E ⇉ E` at the scheme level:
`act ≫ f = pr_E ≫ f`. This is the direction that lets an invariant `f` factor through the
coequalizer `E/G` (the `quotient_lift` half of the interface). The proof feeds the *universal*
`G`-point `pr_G` and `E`-point `pr_E` over the base `G ×_S E` into the functor-of-points
`IsInvariant` condition: there `act` is exactly the point sum `pr_E + ι(pr_G)`
(`translationAction_eq_mul` + commutativity) and `pr_E` is the projection. -/
theorem IsInvariant.coequalizes {G : FiniteLocallyFreeSubgroup E} {Y : Scheme.{u}} {f : E.E ⟶ Y}
    (hf : G.IsInvariant f) : G.translationAction.left ≫ f = G.actionProj.left ≫ f := by
  letI : CommGroup (((Over.mk G.π) ⊗ E.asOver) ⟶ E.asOver) := Hom.commGroup
  set g := ((Over.mk G.π) ⊗ E.asOver).hom with hg
  -- the universal `E`-point `pr_E` and `G`-point `ι ∘ pr_G` over the base `G ×_S E`
  let xUniv : E.Point g := (E.pointEquivOverHom g).symm (snd (Over.mk G.π) E.asOver)
  let tUniv : E.Point g := (E.pointEquivOverHom g).symm (fst (Over.mk G.π) E.asOver ≫ G.ιOver)
  have e1 : (E.pointEquivOverHom g) xUniv = snd (Over.mk G.π) E.asOver :=
    (E.pointEquivOverHom g).apply_symm_apply _
  have e2 : (E.pointEquivOverHom g) tUniv = fst (Over.mk G.π) E.asOver ≫ G.ιOver :=
    (E.pointEquivOverHom g).apply_symm_apply _
  have hx : xUniv.1 = G.actionProj.left := congrArg CommaMorphism.left e1
  have htUniv1 : tUniv.1 = (fst (Over.mk G.π) E.asOver).left ≫ G.ι :=
    congrArg CommaMorphism.left e2
  have htUniv : tUniv ∈ G.pointSubgroup g := ⟨(fst (Over.mk G.π) E.asOver).left, htUniv1.symm⟩
  have hkey := hf g xUniv tUniv htUniv
  have hadd : (E.pointEquivOverHom g) (xUniv + tUniv) = G.translationAction := by
    rw [E.pointEquivOverHom_add, e1, e2, mul_comm]; exact G.translationAction_eq_mul.symm
  have hxt : (xUniv + tUniv).1 = G.translationAction.left := congrArg CommaMorphism.left hadd
  rw [← hxt, ← hx]; exact hkey

/-- **Backward bridge (`coequalizes ⟹ IsInvariant`).** If `f` coequalizes the two legs
`act, pr_E : G ×_S E ⇉ E` at the scheme level, then it is invariant under translation by `G`. This
is the direction that makes the quotient isogeny `π : E ⟶ E/G` (which coequalizes them by
construction) `G`-invariant (`quotientπ_isInvariant`). For each `T`-point `x` and `G`-point
`t = ι ∘ h`, precompose the coequalizer identity by the pair `(h, x) : T ⟶ G ×_S E`: there `act`
pulls back to the point sum `x + t` and `pr_E` to `x`. -/
theorem IsInvariant.of_coequalizes {G : FiniteLocallyFreeSubgroup E} {Y : Scheme.{u}}
    {f : E.E ⟶ Y} (hcoeq : G.translationAction.left ≫ f = G.actionProj.left ≫ f) :
    G.IsInvariant f := by
  intro T gg x t ht
  obtain ⟨h, hh⟩ := ht
  letI : CommGroup ((Over.mk gg) ⟶ E.asOver) := Hom.commGroup
  have hgπ : h ≫ G.π = gg := by rw [← G.ι_π, ← Category.assoc, hh]; exact t.2
  let kOver : Over.mk gg ⟶ (Over.mk G.π) ⊗ E.asOver :=
    lift (Over.homMk h hgπ) (E.pointEquivOverHom gg x)
  have hkxO : kOver ≫ (snd (Over.mk G.π) E.asOver) = E.pointEquivOverHom gg x := lift_snd _ _
  have hfst : kOver ≫ (fst (Over.mk G.π) E.asOver ≫ G.ιOver) = E.pointEquivOverHom gg t := by
    rw [← Category.assoc, lift_fst]
    refine Over.OverMorphism.ext ?_
    show h ≫ G.ι = t.1
    exact hh
  have hktO : kOver ≫ G.translationAction = E.pointEquivOverHom gg (x + t) := by
    rw [E.pointEquivOverHom_add, G.translationAction_eq_mul, MonObj.comp_mul, hfst, hkxO]
    exact mul_comm _ _
  have hkx : kOver.left ≫ G.actionProj.left = x.1 := congrArg CommaMorphism.left hkxO
  have hkt : kOver.left ≫ G.translationAction.left = (x + t).1 := congrArg CommaMorphism.left hktO
  have key := congrArg (kOver.left ≫ ·) hcoeq
  rw [← Category.assoc, ← Category.assoc, hkt, hkx] at key
  exact key

/-- **The bridge, as an iff.** A morphism out of `E` is `G`-invariant (functor-of-points) exactly
when it coequalizes the two legs `act, pr_E : G ×_S E ⇉ E` (scheme level). So `E/G` — the
coequalizer of `act, pr_E` — carries precisely the universal property `SubgroupQuotient` states via
`IsInvariant`. -/
theorem isInvariant_iff_coequalizes {G : FiniteLocallyFreeSubgroup E} {Y : Scheme.{u}}
    (f : E.E ⟶ Y) :
    G.IsInvariant f ↔ G.translationAction.left ≫ f = G.actionProj.left ≫ f :=
  ⟨IsInvariant.coequalizes, IsInvariant.of_coequalizes⟩

/-- **Pins from a coequalizer.** If `π : E ⟶ Q` is a colimit cofork of the two legs `act, pr_E`
(i.e. `Q = E/G` as the coequalizer), then every `G`-invariant `f` factors **uniquely** through `π` —
which is exactly the `quotient_lift` universal property of `SubgroupQuotient`. Combined with
`IsInvariant.of_coequalizes` (giving `quotientπ_isInvariant`), this reduces the whole construction to
one obligation: **build `Q` with `π` a coequalizer of `act, pr_E`**. The proof turns invariance into
coequalization (`IsInvariant.coequalizes`) and applies the cofork's universal property. -/
theorem exists_unique_lift_of_isColimit {G : FiniteLocallyFreeSubgroup E} {Q : Scheme.{u}}
    {π : E.E ⟶ Q} (hcoeq : G.translationAction.left ≫ π = G.actionProj.left ≫ π)
    (hπ : IsColimit (Cofork.ofπ π hcoeq)) {Y : Scheme.{u}} (f : E.E ⟶ Y) (hf : G.IsInvariant f) :
    ∃! h : Q ⟶ Y, π ≫ h = f := by
  have hd : π ≫ hπ.desc (Cofork.ofπ f hf.coequalizes) = f :=
    hπ.fac (Cofork.ofπ f hf.coequalizes) WalkingParallelPair.one
  refine ⟨hπ.desc (Cofork.ofπ f hf.coequalizes), hd, fun h' hh' => ?_⟩
  have hh'' : π ≫ h' = f := hh'
  exact Cofork.IsColimit.hom_ext hπ (hh''.trans hd.symm)

/-- **The graph of the translation action** `⟨act, pr_E⟩ : G ×_S E ⟶ E ×_S E`, `(t, x) ↦ (x + ι t, x)`.
Its image is the equivalence relation `x ∼ x + ι t` whose quotient is `E/G`: `E/G` is the coequalizer
of `act, pr_E`, equivalently the quotient of `E` by (the image of) `actPair`. The two components
recover the legs (`actPair_fst`, `actPair_snd`). The action is free — `actPair` is a monomorphism —
which is what makes the finite-locally-free groupoid an equivalence relation with effective quotient
(the input to Piece 3's existence, `.mathlib-quality/decomposition-g3d-infra.md`). -/
noncomputable def actPair (G : FiniteLocallyFreeSubgroup E) :
    (Over.mk G.π) ⊗ E.asOver ⟶ E.asOver ⊗ E.asOver :=
  lift G.translationAction G.actionProj

@[reassoc, simp]
theorem actPair_fst (G : FiniteLocallyFreeSubgroup E) :
    G.actPair ≫ fst E.asOver E.asOver = G.translationAction :=
  lift_fst _ _

@[reassoc, simp]
theorem actPair_snd (G : FiniteLocallyFreeSubgroup E) :
    G.actPair ≫ snd E.asOver E.asOver = G.actionProj :=
  lift_snd _ _

/-- The inclusion `ιOver : G ⟶ E` is a monomorphism (it is a closed immersion). -/
instance ιOver_mono (G : FiniteLocallyFreeSubgroup E) : Mono G.ιOver := by
  haveI : Mono G.ι := inferInstance
  refine ⟨fun {Z} a b h => Over.OverMorphism.ext ?_⟩
  have h' : a.left ≫ G.ι = b.left ≫ G.ι := congrArg CommaMorphism.left h
  exact (cancel_mono G.ι).mp h'

/-- **Freeness of the translation action.** `actPair = ⟨act, pr_E⟩ : G ×_S E ⟶ E ×_S E` is a
monomorphism: from `(x + ι t, x)` one recovers `x` (second component) and then `ι t` (hence `t`,
`ι` mono) — so `G` acts freely. This makes the finite-locally-free groupoid `G ×_S E ⇉ E` an
equivalence relation, the input to the effective-quotient existence (Piece 3) and the degree count
`deg[N] = N² = rank E[N]` in `E/E[N] ≅ E` (`[T-G3d-Niso]`). -/
instance actPair_mono (G : FiniteLocallyFreeSubgroup E) : Mono G.actPair := by
  refine ⟨fun {Z} a b h => ?_⟩
  letI : CommGroup (Z ⟶ E.asOver) := Hom.commGroup
  have hsnd : a ≫ snd (Over.mk G.π) E.asOver = b ≫ snd (Over.mk G.π) E.asOver := by
    have h2 := congrArg (· ≫ snd E.asOver E.asOver) h
    rwa [Category.assoc, Category.assoc, G.actPair_snd] at h2
  have hact : a ≫ G.translationAction = b ≫ G.translationAction := by
    have h2 := congrArg (· ≫ fst E.asOver E.asOver) h
    rwa [Category.assoc, Category.assoc, G.actPair_fst] at h2
  rw [G.translationAction_eq_mul, MonObj.comp_mul, MonObj.comp_mul, Hom.mul_def, Hom.mul_def,
    hsnd] at hact
  have hfstι : a ≫ (fst (Over.mk G.π) E.asOver ≫ G.ιOver)
      = b ≫ (fst (Over.mk G.π) E.asOver ≫ G.ιOver) :=
    GrpObj.lift_left_mul_ext _ hact
  rw [← Category.assoc, ← Category.assoc] at hfstι
  refine hom_ext _ _ ((cancel_mono G.ιOver).mp hfstι) hsnd

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
