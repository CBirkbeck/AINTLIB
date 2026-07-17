/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-NOETH.
-/
import ModularCurves.ForMathlib.FlatLocus

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
  `exists_flatLocus_univ_stage` is now a thin wrapper (via `flatLocus_eq_univ_of_flat`) around the
  single remaining **registered box** `exists_subalgebra_flat_baseChange`: *flatness of the
  colimit descends to a finite `ℤ`-stage*. Its irreducible missing ingredient is the pointwise
  flat descent of **Stacks 00R6** (the local flatness criterion for finitely-presented algebras),
  which mathlib does not yet support; the surrounding directed-colimit + quasi-compactness assembly
  (*openness of the flat locus*, `isOpen_flatLocus`, and the cofiltered limit of affine schemes,
  `AlgebraicGeometry.exists_mem_of_isClosed_of_nonempty`) is available in mathlib.

## References

Grothendieck, *EGA IV*, §8.5 (spreading out finitely-presented algebras) and §11.2
(spreading out flatness, in particular 11.2.6); Stacks project, tag 05LZ.
-/

open TensorProduct MvPolynomial

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
       Module.Flat R₁ (R₁ ⊗[R₀] A₀)) :=
  sorry

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
