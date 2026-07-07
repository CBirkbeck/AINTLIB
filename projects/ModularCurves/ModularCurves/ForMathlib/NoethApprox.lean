/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-NOETH.
-/
import Mathlib

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

* `exists_noetherian_descent_flat`: the flat refinement — if `A` is additionally `R`-flat then
  (possibly after enlarging `R₀`) `A₀` is `R₀`-flat. This is **EGA IV 11.2.6** (spreading out of
  flatness). The non-flatness component is currently a **registered `sorry`**: a faithful proof
  needs the uniform enlargement bound supplied by *openness of the flat locus* over a noetherian
  ring (EGA IV 11.1.1), which mathlib does not yet have. Everything else — `R₀`, `A₀`, their
  noetherianity, finite presentation, and the base-change isomorphism — is discharged by
  `exists_noetherian_descent`; only `Module.Flat R₀ A₀` is boxed. See the note before the
  declaration for the precise sticking point.

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
  -- The finite set of all coefficients of all generators.
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
  -- Lift each generator to `MvPolynomial (Fin n) R₀`.
  choose lift hlift using
    (fun (g : {x // x ∈ G}) => exists_map_eq_of_coeff_mem R R₀ n g.1 (hTR₀ g.1 g.2))
  set G₀ : Finset (MvPolynomial (Fin n) R₀) := G.attach.image lift with hG₀
  set I₀ : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span ↑G₀ with hI₀
  -- The coefficient map sends the lifted generators back to the originals.
  have hset : (MvPolynomial.map (algebraMap R₀ R)) '' (↑G₀ : Set (MvPolynomial (Fin n) R₀))
      = (↑G : Set P) := by
    rw [hG₀, Finset.coe_image, Set.image_image]
    apply subset_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      simp only [hlift g]
      exact g.2
    · intro g hg
      exact ⟨⟨g, hg⟩, Finset.mem_coe.mpr (Finset.mem_attach _ _), hlift ⟨g, hg⟩⟩
  have hI₀map : Ideal.map (MvPolynomial.map (algebraMap R₀ R)) I₀ = I := by
    rw [hI₀, Ideal.map_span, hset, hG]
  set A₀ : Type u := MvPolynomial (Fin n) R₀ ⧸ I₀ with hA₀
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

/-- **Spreading out of flatness (EGA IV 11.2.6).** If a finitely-presented `R`-algebra `A` is
`R`-flat, then it is the base change of a finitely-presented, `R₀`-flat algebra `A₀` over a
noetherian finitely-generated `ℤ`-subalgebra `R₀ ⊆ R`.

The base ring `R₀`, the descended algebra `A₀`, its noetherianity, finite presentation and the
base-change isomorphism `A ≃ₐ[R] R ⊗[R₀] A₀` are all provided by `exists_noetherian_descent`.
The remaining flatness `Module.Flat R₀ A₀` is a **registered `sorry`** for EGA IV 11.2.6.

Sticking point: descending flatness requires *enlarging* `R₀` (flatness genuinely need not hold
for the first `R₀` produced by the presentation-coefficient descent — e.g. `A₀ = ℤ ⧸ pℤ` over
`R₀ = ℤ` is not flat even when its base change is), and one needs a *single* enlargement that
trivialises **every** relation simultaneously (via the equational criterion
`Module.Flat.iff_forall_exists_factorization`, each individual relation can be trivialised after
some enlargement because tensor products commute with the filtered colimit `R = colim R₁`, but a
uniform bound is required). That uniform bound is exactly *openness of the flat locus* over a
noetherian ring (EGA IV 11.1.1) — not currently available in mathlib. -/
theorem exists_noetherian_descent_flat (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat R A] :
    ∃ (R₀ : Subalgebra ℤ R) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra R₀ A₀),
      IsNoetherianRing R₀ ∧ Algebra.FinitePresentation R₀ A₀ ∧ Module.Flat R₀ A₀ ∧
      Nonempty (A ≃ₐ[R] (R ⊗[R₀] A₀)) := by
  obtain ⟨R₀, A₀, hCR, hAlg, hNoeth, hFP, he⟩ := exists_noetherian_descent R A
  letI := hCR
  letI := hAlg
  refine ⟨R₀, A₀, hCR, hAlg, hNoeth, hFP, ?_, he⟩
  -- EGA IV 11.2.6 (spreading out of flatness): registered box. See the docstring above.
  sorry
