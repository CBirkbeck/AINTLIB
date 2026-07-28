/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-NOETH.
-/
import ModularCurves.ForMathlib.FlatLocus
-- v4.33 bump: these no longer arrive transitively through `FlatLocus`.
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Noetherian approximation for finitely-presented algebras

Every commutative ring `R` is the filtered union of its finitely-generated `ℤ`-subalgebras,
each of which is **noetherian** (finitely generated over `ℤ`, hence a Hilbert basis theorem
applies: `Algebra.FiniteType.isNoetherianRing` with `IsNoetherianRing ℤ`). This is the
substrate for *spreading-out* / *noetherian approximation*: a finitely-presented `R`-algebra
`A` is the base change of a finitely-presented algebra over one of these noetherian
subalgebras, so a flatness/regularity statement over `R` can be discharged by descending to
the noetherian stage (where annihilators are finitely generated) and base-changing back.

## Main results

* `exists_noetherianSubalgebra_supset`: every finite subset of `R` lies in a
  finitely-generated `ℤ`-subalgebra `R₀`, which is therefore noetherian.

* `exists_noetherian_descent`: a finitely-presented `R`-algebra `A` is `R`-algebra isomorphic
  to `R ⊗[R₀] A₀` for some noetherian finitely-generated `ℤ`-subalgebra `R₀ ⊆ R` and some
  finitely-presented `R₀`-algebra `A₀`. Proof: destructure the presentation
  `A ≃ₐ[R] MvPolynomial (Fin n) R ⧸ I` with `I` finitely generated, collect all coefficients
  of a finite generating set into a finite set `T`, take `R₀ := Algebra.adjoin ℤ T`, lift each
  generator to `MvPolynomial (Fin n) R₀` (its coefficients lie in `R₀`), and set
  `A₀ := MvPolynomial (Fin n) R₀ ⧸ I₀` for the span `I₀` of the lifts. The isomorphism chains
  `Algebra.TensorProduct.tensorQuotientEquiv` (tensor commutes with quotient),
  `MvPolynomial.algebraTensorAlgEquiv` (`R ⊗[R₀] MvPolynomial (Fin n) R₀ ≃ MvPolynomial (Fin n) R`)
  and `Ideal.quotientKerAlgEquivOfSurjective`.

* `exists_noetherian_descent_flat`: the flat refinement — if `A` is additionally `R`-flat then,
  after enlarging `R₀` if necessary, `A₀` is `R₀`-flat. This is **Stacks 07RF / EGA IV 11.2.6**
  (spreading out of flatness). The proof enlarges the first descent's base `R₀` to a noetherian
  `R₁ ⊆ R` at which the flat locus is all of `Spec (R₁ ⊗[R₀] A₀)`, then reads off flatness by
  locality (`flat_of_flatLocus_univ`, from `Module.flat_of_isLocalized_maximal`) and re-expresses
  the base change through `Algebra.TensorProduct.cancelBaseChange`. Enlargement is genuinely
  necessary (`A₀ = ℤ ⧸ pℤ` over `R₀ = ℤ` is not flat although `ℚ ⊗ A₀ = 0` is). The geometric step
  `exists_flatLocus_univ_stage` is a thin wrapper (via `flatLocus_eq_univ_of_flat`) around
  `exists_subalgebra_flat_baseChange`: *flatness of the colimit descends to a finite `ℤ`-stage*.

  The **directed-colimit + quasi-compactness assembly** for that descent is built in the
  `### Scheme-limit machinery` section below and is otherwise axiom-clean:
  `R ⊗[R₀] A₀ = colimᵢ (Rᵢ ⊗[R₀] A₀)` over the finitely-generated stages (`stageColimit`, via
  `TensorProduct.Algebra.exists_of_fg` and the filtered-colimit recognition
  `Types.FilteredColimit.isColimitOf'`); `Spec (R ⊗[R₀] A₀) = limᵢ Spec (Rᵢ ⊗[R₀] A₀)` as a
  cofiltered limit of affine schemes (`stageIsLimit`, via `Scheme.Spec` preserving limits); the
  non-flat loci are closed (`isOpen_flatLocus`) and the cofiltered-limit engine
  `AlgebraicGeometry.exists_mem_of_isClosed_of_nonempty` collapses them to a single stage
  (`exists_fg_flat_stage`). Two *local* facts are isolated as named boxes: `flat_stalk_descends` —
  the pointwise flat descent of **Stacks 00R6** (the local flatness criterion for
  finitely-presented algebras), the one genuinely mathlib-absent ingredient — and `nonflat_mapsTo`,
  the base-change *ascent* of stalk flatness (`Module.Flat.baseChange` + localisation; provable,
  not a mathlib gap).

## References

Grothendieck, *EGA IV*, §8.5 (spreading out finitely-presented algebras) and §11.2
(spreading out flatness, in particular 11.2.6); Stacks project, tag 05LZ.
-/

open TensorProduct MvPolynomial

-- v4.33 bump: the category instances are no longer transparent enough for the rewrites below.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- Auxiliary: the canonical `R₀ ⊗ MvPolynomial → MvPolynomial` equivalence composed with the
right inclusion `MvPolynomial (Fin n) R₀ → R ⊗[R₀] MvPolynomial (Fin n) R₀` is the coefficient
map `MvPolynomial.map (algebraMap R₀ R)`. -/
private theorem algebraTensorAlgEquiv_includeRight_apply (R : Type u) [CommRing R]
    (R₀ : Subalgebra ℤ R) (n : ℕ) (p₀ : MvPolynomial (Fin n) R₀) :
    (MvPolynomial.algebraTensorAlgEquiv R₀ (σ := Fin n) R)
      (Algebra.TensorProduct.includeRight p₀) = MvPolynomial.map (algebraMap R₀ R) p₀ := by
  induction p₀ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp
  | mul_X p i hp => simp

/-- Auxiliary: a multivariate polynomial all of whose coefficients lie in a `ℤ`-subalgebra `R₀`
is the coefficient-image of a polynomial over `R₀`. -/
private theorem exists_map_eq_of_coeff_mem (R : Type u) [CommRing R] (R₀ : Subalgebra ℤ R)
    (n : ℕ) (p : MvPolynomial (Fin n) R) (hp : ∀ m ∈ p.support, coeff m p ∈ R₀) :
    ∃ p₀ : MvPolynomial (Fin n) R₀, MvPolynomial.map (algebraMap R₀ R) p₀ = p := by
  classical
  refine ⟨∑ m ∈ p.support.attach, monomial m.1 (⟨coeff m.1 p, hp m.1 m.2⟩ : R₀), ?_⟩
  rw [map_sum]
  conv_rhs => rw [MvPolynomial.as_sum p]
  rw [← Finset.sum_attach p.support (fun m => monomial m (coeff m p))]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.map_monomial]
  congr 1

/-- Every finite subset of a commutative ring lies in a finitely-generated `ℤ`-subalgebra,
which is therefore noetherian. -/
theorem exists_noetherianSubalgebra_supset (R : Type u) [CommRing R] (s : Finset R) :
    ∃ (R₀ : Subalgebra ℤ R), Algebra.FiniteType ℤ R₀ ∧ IsNoetherianRing R₀ ∧
      (↑s : Set R) ⊆ (R₀ : Set R) := by
  refine ⟨Algebra.adjoin ℤ (↑s : Set R), ?_, ?_, Algebra.subset_adjoin⟩
  · exact (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)
  · haveI : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (↑s : Set R)) :=
      (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)
    exact Algebra.FiniteType.isNoetherianRing ℤ _

/-- A finite set of multivariate polynomials over `R` descends to a noetherian
finitely-generated `ℤ`-subalgebra: there is a noetherian `R₀ ⊆ R` and a finite set `G₀` of
polynomials over `R₀` whose coefficient-image `MvPolynomial.map (algebraMap R₀ R) '' G₀` is exactly
`G`. Take `R₀ := Algebra.adjoin ℤ` of all coefficients of all members of `G` (noetherian by the
Hilbert basis theorem) and lift each `g` via `exists_map_eq_of_coeff_mem`. -/
private theorem exists_noetherianSubalgebra_map_image (R : Type u) [CommRing R] (n : ℕ)
    (G : Finset (MvPolynomial (Fin n) R)) :
    ∃ (R₀ : Subalgebra ℤ R), IsNoetherianRing R₀ ∧
      ∃ G₀ : Finset (MvPolynomial (Fin n) R₀),
        (MvPolynomial.map (algebraMap R₀ R)) '' (↑G₀ : Set (MvPolynomial (Fin n) R₀))
          = (↑G : Set (MvPolynomial (Fin n) R)) := by
  classical
  -- The finite set of all coefficients of all members of `G`.
  set T : Finset R := G.biUnion (fun g => g.support.image (fun m => coeff m g)) with hT
  have hTmem : ∀ g ∈ G, ∀ m ∈ g.support, coeff m g ∈ T := by
    intro g hg m hm
    rw [hT, Finset.mem_biUnion]
    exact ⟨g, hg, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩
  -- The noetherian subalgebra generated by those coefficients (NOETH1).
  obtain ⟨R₀, hFT, hNoeth, hTsub⟩ := exists_noetherianSubalgebra_supset R T
  have hTR₀ : ∀ g ∈ G, ∀ m ∈ g.support, coeff m g ∈ R₀ := by
    intro g hg m hm
    exact hTsub (hTmem g hg m hm)
  -- Lift each member of `G` to `MvPolynomial (Fin n) R₀`.
  choose lift hlift using
    (fun (g : {x // x ∈ G}) => exists_map_eq_of_coeff_mem R R₀ n g.1 (hTR₀ g.1 g.2))
  refine ⟨R₀, hNoeth, G.attach.image lift, ?_⟩
  rw [Finset.coe_image, Set.image_image]
  apply subset_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    simp only [hlift g]
    exact g.2
  · intro g hg
    exact ⟨⟨g, hg⟩, Finset.mem_coe.mpr (Finset.mem_attach _ _), hlift ⟨g, hg⟩⟩

/-- A finitely-presented `R`-algebra `A` is the base change of a finitely-presented algebra over
a noetherian finitely-generated `ℤ`-subalgebra `R₀ ⊆ R`. -/
theorem exists_noetherian_descent (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    ∃ (R₀ : Subalgebra ℤ R) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra R₀ A₀),
      IsNoetherianRing R₀ ∧ Algebra.FinitePresentation R₀ A₀ ∧
      Nonempty (A ≃ₐ[R] (R ⊗[R₀] A₀)) := by
  classical
  obtain ⟨n, f, hf_surj, hf_fg⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  set P := MvPolynomial (Fin n) R with hP
  set I : Ideal P := RingHom.ker f.toRingHom with hI
  obtain ⟨G, hG⟩ := hf_fg
  -- Descend the generating set to a noetherian `ℤ`-subalgebra `R₀ ⊆ R`.
  obtain ⟨R₀, hNoeth, G₀, hset⟩ := exists_noetherianSubalgebra_map_image R n G
  set I₀ : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span ↑G₀ with hI₀
  set A₀ : Type u := MvPolynomial (Fin n) R₀ ⧸ I₀
  refine ⟨R₀, A₀, inferInstance, inferInstance, hNoeth, ?_, ?_⟩
  · -- `A₀` is finitely presented: it is a quotient of a polynomial algebra by a f.g. ideal.
    exact Algebra.FinitePresentation.quotient (Submodule.fg_span G₀.finite_toSet)
  · -- The base-change isomorphism `A ≃ₐ[R] R ⊗[R₀] A₀`.
    refine ⟨?_⟩
    have hJI : Ideal.map (MvPolynomial.algebraTensorAlgEquiv R₀ (σ := Fin n) R)
        (Ideal.map Algebra.TensorProduct.includeRight I₀) = I := by
      rw [hI₀, Ideal.map_span, Ideal.map_span, Set.image_image,
        Set.image_congr (g := MvPolynomial.map (algebraMap R₀ R))
          (fun g₀ _ => algebraTensorAlgEquiv_includeRight_apply R R₀ n g₀), hset, hG]
    exact
      ((Algebra.TensorProduct.tensorQuotientEquiv (R := R₀) R
          (MvPolynomial (Fin n) R₀) R I₀).trans
        ((Ideal.quotientEquivAlg _ I
            (MvPolynomial.algebraTensorAlgEquiv R₀ (σ := Fin n) R) hJI.symm).trans
          (Ideal.quotientKerAlgEquivOfSurjective hf_surj))).symm

/-- **Flatness is local on the total space.** If the flat locus `flatLocus R₁ A₁ A₁ ⊆ Spec A₁` of
the `R₁`-algebra `A₁` is all of `Spec A₁` — i.e. the localisation `(A₁)_𝔮` is `R₁`-flat at every
prime `𝔮` of `A₁` — then `A₁` itself is flat over `R₁`.

This is `Module.flat_of_isLocalized_maximal`: flatness over `R₁` can be checked at the maximal
ideals of `A₁`, and those are among the primes recorded by the flat locus. It is the
module-theoretic half of Stacks 07RF (the geometric half is `exists_flatLocus_univ_stage`). -/
private theorem flat_of_flatLocus_univ {R₁ A₁ : Type u} [CommRing R₁] [CommRing A₁]
    [Algebra R₁ A₁] (h : flatLocus R₁ A₁ A₁ = Set.univ) : Module.Flat R₁ A₁ := by
  apply Module.flat_of_isLocalized_maximal A₁ A₁ (fun P _ => LocalizedModule P.primeCompl A₁)
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl A₁)
  intro P hP
  have hmem : (⟨P, hP.isPrime⟩ : PrimeSpectrum A₁) ∈ flatLocus R₁ A₁ A₁ := by
    rw [h]; exact Set.mem_univ _
  exact mem_flatLocus.mp hmem

/-- **Converse of `flat_of_flatLocus_univ`.** If the `R₁`-algebra `A₁` is `R₁`-flat then its flat
locus is the whole spectrum: every localisation `(A₁)_𝔮` stays `R₁`-flat because localisation is an
exact `R₁`-linear functor (`flat_localizedModule_of_flat`). Together with `flat_of_flatLocus_univ`
this makes `flatLocus R₁ A₁ A₁ = Set.univ` and `Module.Flat R₁ A₁` equivalent, so the geometric box
below only has to produce flatness at a finite stage. -/
private theorem flatLocus_eq_univ_of_flat {R₁ A₁ : Type u} [CommRing R₁] [CommRing A₁]
    [Algebra R₁ A₁] [Module.Flat R₁ A₁] : flatLocus R₁ A₁ A₁ = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro q
  rw [mem_flatLocus]
  exact flat_localizedModule_of_flat q.asIdeal.primeCompl

/-! ### Scheme-limit machinery for `exists_subalgebra_flat_baseChange` (Stacks 07RF) -/

open CategoryTheory Limits AlgebraicGeometry

/-- The tensor-map along `f` (identity on the second factor) equals `rTensor` as a linear map. -/
private theorem tensorMap_id_toLinearMap {B S T N : Type*} [CommRing B] [CommRing S]
    [CommRing T] [CommRing N] [Algebra B S] [Algebra B T] [Algebra B N] (f : S →ₐ[B] T) :
    (Algebra.TensorProduct.map f (AlgHom.id B N)).toLinearMap
      = LinearMap.rTensor N f.toLinearMap := by
  refine TensorProduct.ext' fun s n => ?_
  simp

section Machinery

variable {R : Type u} [CommRing R] (R₀ : Subalgebra ℤ R)
  (A₀ : Type u) [CommRing A₀] [Algebra R₀ A₀]

/-- Index category: finitely-generated `R₀`-subalgebras of `R`, directed by `≤`. -/
private abbrev FlatStage : Type u := {A : Subalgebra R₀ R // A.FG}

instance : Nonempty (FlatStage R₀) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

instance : IsDirected (FlatStage R₀) (· ≤ ·) :=
  ⟨fun A B => ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩,
    (le_sup_left : A.1 ≤ A.1 ⊔ B.1), (le_sup_right : B.1 ≤ A.1 ⊔ B.1)⟩⟩

/-- The ring-level diagram `A ↦ A ⊗[R₀] A₀` over the finitely-generated stages. -/
private noncomputable def stageFunctor : FlatStage R₀ ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of (A.1 ⊗[R₀] A₀)
  map {A B} h := CommRingCat.ofHom
    (Algebra.TensorProduct.map (Subalgebra.inclusion h.le) (AlgHom.id R₀ A₀)).toRingHom
  map_id A := by
    apply CommRingCat.hom_ext
    ext x
    · simp
    · simp
  map_comp {A B C} f g := by
    apply CommRingCat.hom_ext
    ext x
    · simp [Subalgebra.inclusion_inclusion]
    · simp

/-- The colimit cocone with apex `R ⊗[R₀] A₀`. -/
private noncomputable def stageCocone : Cocone (stageFunctor R₀ A₀) where
  pt := CommRingCat.of (R ⊗[R₀] A₀)
  ι :=
    { app A := CommRingCat.ofHom
        (Algebra.TensorProduct.map A.1.val (AlgHom.id R₀ A₀)).toRingHom
      naturality {A B} h := by
        have key : (Algebra.TensorProduct.map (B.1).val (AlgHom.id R₀ A₀)).comp
            (Algebra.TensorProduct.map (Subalgebra.inclusion h.le) (AlgHom.id R₀ A₀))
            = Algebra.TensorProduct.map (A.1).val (AlgHom.id R₀ A₀) := by
          rw [← Algebra.TensorProduct.map_comp, Subalgebra.val_comp_inclusion, AlgHom.comp_id]
        exact congrArg (fun φ : (A.1 ⊗[R₀] A₀) →ₐ[R₀] (R ⊗[R₀] A₀) =>
          CommRingCat.ofHom φ.toRingHom) key }

/-- Computation of a leg of the (underlying-type) colimit cocone as `rTensor`. -/
private theorem stageMapCocone_ι (A : FlatStage R₀) (xi : A.1 ⊗[R₀] A₀) :
    ((forget CommRingCat.{u}).mapCocone (stageCocone R₀ A₀)).ι.app A xi
      = LinearMap.rTensor A₀ A.1.val.toLinearMap xi := by
  rw [← DFunLike.congr_fun (tensorMap_id_toLinearMap A.1.val) xi]
  rfl

/-- Computation of a `stageFunctor` transition map as `rTensor`. -/
private theorem stageFunctor_map_apply {A B : FlatStage R₀} (h : A ⟶ B) (x : A.1 ⊗[R₀] A₀) :
    (stageFunctor R₀ A₀ ⋙ forget CommRingCat.{u}).map h x
      = LinearMap.rTensor A₀ (Subalgebra.inclusion h.le).toLinearMap x := by
  rw [← DFunLike.congr_fun (tensorMap_id_toLinearMap (Subalgebra.inclusion h.le)) x]
  rfl

/-- `R ⊗[R₀] A₀` is the filtered colimit of the `A ⊗[R₀] A₀` over finitely-generated stages `A`. -/
private noncomputable def stageColimit : IsColimit (stageCocone R₀ A₀) := by
  haveI : ReflectsColimit (stageFunctor R₀ A₀) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat.{u})
  apply Types.FilteredColimit.isColimitOf'
  · -- jointly surjective: every element of `R ⊗ A₀` comes from a finite stage
    intro x
    obtain ⟨A, hA, xi, hxi⟩ := TensorProduct.Algebra.exists_of_fg (N := A₀) x
    exact ⟨⟨A, hA⟩, xi, by rw [stageMapCocone_ι, hxi]⟩
  · -- eventually equal: two elements agreeing at the colimit agree at a later stage
    intro A x y hxy
    rw [stageMapCocone_ι, stageMapCocone_ι] at hxy
    obtain ⟨B, hAB, hBfg, heq⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq A.2 hxy
    refine ⟨⟨B, hBfg⟩, homOfLE hAB, ?_⟩
    rw [stageFunctor_map_apply, stageFunctor_map_apply]
    exact heq

/-- The cofiltered scheme diagram `A ↦ Spec (A ⊗[R₀] A₀)` with affine transition maps. -/
private noncomputable def stageDiagram : (FlatStage R₀)ᵒᵖ ⥤ Scheme.{u} :=
  (stageFunctor R₀ A₀).op ⋙ Scheme.Spec

instance stageDiagram_affineHom {i j : (FlatStage R₀)ᵒᵖ} (f : i ⟶ j) :
    IsAffineHom ((stageDiagram R₀ A₀).map f) := by
  haveI : IsAffine ((stageDiagram R₀ A₀).obj i) := inferInstanceAs (IsAffine (Scheme.Spec.obj _))
  haveI : IsAffine ((stageDiagram R₀ A₀).obj j) := inferInstanceAs (IsAffine (Scheme.Spec.obj _))
  exact isAffineHom_of_isAffine _

instance stageDiagram_compactSpace (i : (FlatStage R₀)ᵒᵖ) :
    CompactSpace ((stageDiagram R₀ A₀).obj i) :=
  inferInstanceAs (CompactSpace (Spec _))

/-- The limit cone on `stageDiagram` with apex `Spec (R ⊗[R₀] A₀)`. -/
private noncomputable def stageLimitCone : Cone (stageDiagram R₀ A₀) :=
  Scheme.Spec.mapCone (stageCocone R₀ A₀).op

/-- `Spec (R ⊗[R₀] A₀)` is the cofiltered limit of the `Spec (A ⊗[R₀] A₀)`. -/
private noncomputable def stageIsLimit : IsLimit (stageLimitCone R₀ A₀) :=
  isLimitOfPreserves Scheme.Spec (stageColimit R₀ A₀).op

variable [IsNoetherianRing R₀] [Algebra.FinitePresentation R₀ A₀]

/-- Each finitely-generated stage `A ⊇ R₀` is a Noetherian ring. -/
private theorem stageNoeth (A : FlatStage R₀) : IsNoetherianRing ↥A.1 := by
  haveI : Algebra.FiniteType ↥R₀ ↥A.1 := (Subalgebra.fg_iff_finiteType A.1).mp A.2
  exact Algebra.FiniteType.isNoetherianRing ↥R₀ ↥A.1

/-- **Stacks 00R6 (the isolated homological gap).** The `R`-flatness of `(R ⊗ A₀)_𝔮` at a prime
`𝔮` (here the image of the limit point `s`) descends to `A`-flatness of `(A ⊗ A₀)` at the contracted
prime, at a finite finitely-generated stage `A ⊇ R₀`.  This is the local flatness criterion for
finitely-presented algebras (= Lemma 10.128.3), which current mathlib does not provide; every other
step of `exists_subalgebra_flat_baseChange` is discharged around this box. -/
private theorem flat_stalk_descends (hflat : Module.Flat R (R ⊗[R₀] A₀))
    (s : (stageLimitCone R₀ A₀).pt) :
    ∃ A : FlatStage R₀, (stageLimitCone R₀ A₀).π.app (Opposite.op A) s ∈
      flatLocus ↥A.1 (↥A.1 ⊗[R₀] A₀) (↥A.1 ⊗[R₀] A₀) :=
  sorry -- Stacks 00R6

/-- **Flatness ascends along the stages.** If `A' ≤ A` are finitely-generated stages and the
contraction of `q : Spec (A ⊗ A₀)` to `Spec (A' ⊗ A₀)` is `A'`-flat, then `q` is `A`-flat: base
change of a flat module along `A' → A` stays flat, and localisation preserves it.  This gives the
`MapsTo` on non-flat loci needed to feed the cofiltered-limit engine. -/
private theorem nonflat_mapsTo {i i' : (FlatStage R₀)ᵒᵖ} (f : i ⟶ i') :
    Set.MapsTo ((stageDiagram R₀ A₀).map f)
      (flatLocus ↥(i.unop).1 (↥(i.unop).1 ⊗[R₀] A₀) (↥(i.unop).1 ⊗[R₀] A₀))ᶜ
      (flatLocus ↥(i'.unop).1 (↥(i'.unop).1 ⊗[R₀] A₀) (↥(i'.unop).1 ⊗[R₀] A₀))ᶜ :=
  sorry -- flatness base-change ascent (provable; not a mathlib gap)

/-- **The cofiltered-limit collapse.** From the `R`-flatness of `R ⊗ A₀` there is a single
finitely-generated stage `A ⊇ R₀` at which `A ⊗[R₀] A₀` is already `A`-flat. -/
private theorem exists_fg_flat_stage (hflat : Module.Flat R (R ⊗[R₀] A₀)) :
    ∃ (A : Subalgebra ↥R₀ R), A.FG ∧ Module.Flat ↥A (↥A ⊗[R₀] A₀) := by
  by_contra hcon
  push_neg at hcon
  set Z : ∀ i : (FlatStage R₀)ᵒᵖ, Set ((stageDiagram R₀ A₀).obj i) := fun i =>
    (flatLocus ↥(i.unop).1 (↥(i.unop).1 ⊗[R₀] A₀) (↥(i.unop).1 ⊗[R₀] A₀))ᶜ with hZ
  have hZc : ∀ i, IsClosed (Z i) := by
    intro i
    haveI := stageNoeth (A := i.unop)
    exact isOpen_flatLocus.isClosed_compl
  have hZne : ∀ i, (Z i).Nonempty := by
    intro i
    haveI := stageNoeth (A := i.unop)
    apply Set.nonempty_compl.mpr
    intro huniv
    exact hcon (i.unop).1 (i.unop).2 (flat_of_flatLocus_univ huniv)
  have hZcpt : ∀ i, IsCompact (Z i) := fun i => (hZc i).isCompact
  obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty (stageDiagram R₀ A₀)
    (stageLimitCone R₀ A₀) (stageIsLimit R₀ A₀) Z hZc hZne hZcpt
    (fun f => nonflat_mapsTo R₀ A₀ f)
  obtain ⟨A, hA⟩ := flat_stalk_descends R₀ A₀ hflat s
  exact (hs (Opposite.op A)) hA

end Machinery

/-- **Flatness descends to a finite `ℤ`-stage (Stacks 07RF = Lemma 10.168.1(3) / EGA IV 11.2.6).**
The genuinely homological core of the flatness-spreading box, isolated as a single statement:
given the Noetherian base `R₀ ⊆ R` and the finitely-presented `R₀`-algebra `A₀` whose base change
`R ⊗[R₀] A₀` is `R`-flat, there is a *larger* finitely-generated `ℤ`-subalgebra `R₁`,
`R₀ ⊆ R₁ ⊆ R` (still Noetherian), at which `R₁ ⊗[R₀] A₀` is already `R₁`-flat.

Enlargement past `R₀` is genuinely necessary: with `A₀ = ℤ ⧸ pℤ` over `R₀ = ℤ` inside `R = ℚ`, no
`ℤ[1/n]` with `p ∤ n` gives a flat base change, but `R₁ = ℤ[1/p]` gives `R₁ ⊗[ℤ] A₀ = 0`, flat.

**Intended proof and the precise mathlib gap.** Write `R` as the filtered colimit `R = colimᵢ Rᵢ`
of its finitely-generated `ℤ`-subalgebras `Rᵢ ⊇ R₀` (each `IsNoetherianRing`, being finitely
generated over `ℤ`), so `R ⊗[R₀] A₀ = colimᵢ (Rᵢ ⊗[R₀] A₀)`. Then:
* *Pointwise descent* (**Stacks 00R6** = Lemma 10.128.3): for each prime `𝔮` of `R ⊗[R₀] A₀`, the
  `R`-flatness of the localisation at `𝔮` descends to `Rᵢ`-flatness of the localisation of
  `Rᵢ ⊗[R₀] A₀` at the contracted prime, at a finite stage `i(𝔮)`. For the finitely *presented*
  algebra `Rᵢ ⊗[R₀] A₀` this is a *finite* condition (the local criterion for flatness,
  **Stacks 00MK/00R4**) which therefore survives the colimit. **This is the fact current mathlib
  lacks**: there is no `Module.Flat` filtered-colimit descent, and no local flatness criterion for
  finitely-presented algebras — it is the homological cousin of the boxed
  `exists_basicOpen_subset_flatLocus_of_mem` in `FlatLocus`.
* *Openness* (`isOpen_flatLocus`, **Stacks 00RC**): over the Noetherian `Rᵢ` the flat locus
  `flatLocus Rᵢ (Rᵢ ⊗[R₀] A₀) (Rᵢ ⊗[R₀] A₀)` is open, upgrading each `𝔮` to an open
  stage-neighbourhood.
* *Cofiltered-limit collapse*: `Spec (R ⊗[R₀] A₀) = limᵢ Spec (Rᵢ ⊗[R₀] A₀)` is a cofiltered limit
  of affine schemes with affine transition maps; the open flat loci cover it, and quasi-compactness
  of this limit collapses the cover to a single stage `R₁`. This topological engine **is** present
  in mathlib (`AlgebraicGeometry.exists_map_eq_top` / `exists_mem_of_isClosed_of_nonempty`,
  **Stacks 01Z2/01Z3/01Z4**); only wiring the ring colimit `R ⊗[R₀] A₀ = colimᵢ (Rᵢ ⊗[R₀] A₀)` into
  its scheme-limit cone remains. The irreducible missing ingredient is the pointwise descent above.
  -/
private theorem exists_subalgebra_flat_baseChange {R : Type u} [CommRing R]
    (R₀ : Subalgebra ℤ R) [IsNoetherianRing R₀]
    (A₀ : Type u) [CommRing A₀] [Algebra R₀ A₀] [Algebra.FinitePresentation R₀ A₀]
    (hflat : Module.Flat R (R ⊗[R₀] A₀)) :
    ∃ (R₁ : Subalgebra ℤ R) (h : R₀ ≤ R₁), IsNoetherianRing R₁ ∧
      (letI : Algebra R₀ R₁ := (Subalgebra.inclusion h).toAlgebra
       Module.Flat R₁ (R₁ ⊗[R₀] A₀)) := by
  obtain ⟨A, hAfg, hAflat⟩ := exists_fg_flat_stage R₀ A₀ hflat
  refine ⟨Subalgebra.restrictScalars ℤ A, ?hle, ?noeth, ?flat⟩
  case hle =>
    intro x hx
    rw [Subalgebra.mem_restrictScalars]
    simpa using A.algebraMap_mem ⟨x, hx⟩
  case noeth => exact stageNoeth (A := (⟨A, hAfg⟩ : FlatStage R₀))
  case flat => exact hAflat

/-- **Spreading out of flatness, geometric core (Stacks 07RF = Lemma 10.168.1(3) / EGA IV 11.2.6).**

Given the noetherian base `R₀ ⊆ R` and the finitely-presented `R₀`-algebra `A₀` whose base change
`R ⊗[R₀] A₀` is `R`-flat, there is a *larger* finitely-generated `ℤ`-subalgebra `R₁`,
`R₀ ⊆ R₁ ⊆ R` (still noetherian), at which the **entire** flat locus is captured:
`flatLocus R₁ (R₁ ⊗[R₀] A₀) (R₁ ⊗[R₀] A₀) = Set.univ`.

Enlargement is genuinely necessary — flatness need not hold for the `R₀` produced by the
presentation-coefficient descent (`A₀ = ℤ ⧸ pℤ` over `R₀ = ℤ` is not `ℤ`-flat although
`ℚ ⊗ A₀ = 0` is `ℚ`-flat).

This is now a thin geometric wrapper: `exists_subalgebra_flat_baseChange` (the isolated Stacks 07RF
core) produces a finite stage `R₁` at which `R₁ ⊗[R₀] A₀` is `R₁`-*flat*, and
`flatLocus_eq_univ_of_flat` turns that module-level flatness into `flatLocus … = Set.univ` (each
localisation stays flat, localisation being an exact functor). -/
private theorem exists_flatLocus_univ_stage {R : Type u} [CommRing R]
    (R₀ : Subalgebra ℤ R) [IsNoetherianRing R₀]
    (A₀ : Type u) [CommRing A₀] [Algebra R₀ A₀] [Algebra.FinitePresentation R₀ A₀]
    (hflat : Module.Flat R (R ⊗[R₀] A₀)) :
    ∃ (R₁ : Subalgebra ℤ R) (h : R₀ ≤ R₁), IsNoetherianRing R₁ ∧
      (letI : Algebra R₀ R₁ := (Subalgebra.inclusion h).toAlgebra
       flatLocus R₁ (R₁ ⊗[R₀] A₀) (R₁ ⊗[R₀] A₀) = Set.univ) := by
  obtain ⟨R₁, h, hNoeth, hfl⟩ := exists_subalgebra_flat_baseChange R₀ A₀ hflat
  refine ⟨R₁, h, hNoeth, ?_⟩
  letI : Algebra R₀ R₁ := (Subalgebra.inclusion h).toAlgebra
  haveI : Module.Flat R₁ (R₁ ⊗[R₀] A₀) := hfl
  exact flatLocus_eq_univ_of_flat

/-- **Spreading out of flatness (Stacks 07RF / EGA IV 11.2.6).** If a finitely-presented
`R`-algebra `A` is `R`-flat, then — *after enlarging the base if necessary* — it is the base change
of a finitely-presented, `R₀`-flat algebra `A₀` over a noetherian finitely-generated
`ℤ`-subalgebra `R₀ ⊆ R`.

`exists_noetherian_descent` supplies a first noetherian descent `A ≃ₐ[R] R ⊗[R₀] A₀`; over that
`R₀` the algebra `A₀` need not be flat, so the base is enlarged to a noetherian `R₁` with
`R₀ ⊆ R₁ ⊆ R` at which the flat locus is everything (`exists_flatLocus_univ_stage`, the registered
Stacks 07RF box), whence `A₁ := R₁ ⊗[R₀] A₀` is flat by locality of flatness on the total space
(`flat_of_flatLocus_univ`), and the base change is re-expressed `A ≃ₐ[R] R ⊗[R₁] A₁` through
`Algebra.TensorProduct.cancelBaseChange`. -/
theorem exists_noetherian_descent_flat (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat R A] :
    ∃ (R₀ : Subalgebra ℤ R) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra R₀ A₀),
      IsNoetherianRing R₀ ∧ Algebra.FinitePresentation R₀ A₀ ∧ Module.Flat R₀ A₀ ∧
      Nonempty (A ≃ₐ[R] (R ⊗[R₀] A₀)) := by
  obtain ⟨R₀, A₀, hCR, hAlg, hNoeth, hFP, ⟨e⟩⟩ := exists_noetherian_descent R A
  letI := hCR
  letI := hAlg
  -- transport `R`-flatness across the base-change isomorphism
  haveI hRflat : Module.Flat R (R ⊗[R₀] A₀) := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  -- Stacks 07RF: enlarge `R₀` to a noetherian `R₁` at which the flat locus is everything
  obtain ⟨R₁, hle, hNoeth₁, huniv⟩ := exists_flatLocus_univ_stage R₀ A₀ hRflat
  letI : Algebra R₀ R₁ := (Subalgebra.inclusion hle).toAlgebra
  haveI : IsScalarTower R₀ R₁ R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- flatness is local on the total space `Spec (R₁ ⊗[R₀] A₀)`
  haveI hflat₁ : Module.Flat R₁ (R₁ ⊗[R₀] A₀) := flat_of_flatLocus_univ huniv
  refine ⟨R₁, R₁ ⊗[R₀] A₀, inferInstance, inferInstance, hNoeth₁, inferInstance, hflat₁, ⟨?_⟩⟩
  exact e.trans (Algebra.TensorProduct.cancelBaseChange R₀ R₁ R R A₀).symm
