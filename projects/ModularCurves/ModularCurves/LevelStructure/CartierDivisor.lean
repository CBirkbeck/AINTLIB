import ModularCurves.EllipticCurve.GroupLaw
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Nilpotent
import ModularCurves.ForMathlib.NormBaseChange
import ModularCurves.ForMathlib.IdealSheafComapMul

/-!
# Relative effective Cartier divisors and full sets of sections (KM Ch. 1)

The substrate for Drinfeld level structures, transcribed from KM Ch. 1 (which the project
has in full, with proofs, via the KM preview: §§1.1–1.9).

* A **relative effective Cartier divisor** `D` in a curve `C/S` (KM 1.1–1.2). Official
  definition: a closed subscheme, flat over `S`, whose ideal sheaf is invertible. Mathlib
  has no invertible-ideal-sheaf API yet, so we take as *working definition* the
  characterisation in the relative-curve case (KM 1.2.3): a closed subscheme which is
  finite locally free over the base. The equivalence with the official definition, in the
  smooth-relative-curve case we use, is ticket `T-D1` (its statement needs the
  invertible-`O_C`-module API — API gap AG-LB in plan.md — and is recorded there, not
  here, to avoid a junk placeholder).

* A **full set of sections** (KM 1.8.2; working form from the proof of KM 1.9.1, verbatim:
  "The points `P₁,…,P_N` form a full set of sections of `Spec(B)/R` if and only if this
  universal `f` satisfies `Norm(f) = ∏ f(Pᵢ)`"). We state the affine case as an honest
  definition quantified over base changes (equivalent to KM's single universal case
  `A = R[T₁,…,T_N]`, by KM 1.8.4).

* The **divisor `Σᵢ [Pᵢ]` attached to a family of sections** (KM 1.2.2 for one section;
  sums of divisors via ideal products). The sum is a registered construction (DS4a,
  ticket `T-D3`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {C S : Scheme.{u}}

/-- A relative effective Cartier divisor in `C/S`, in the working form for relative curves
(KM 1.2.3): a closed subscheme of `C` (given by its ideal sheaf) which is finite, flat and
of finite presentation (= finite locally free) over `S`.

Official definition (KM 1.1.1): a closed subscheme `D ⊆ C`, flat over `S`, whose ideal
sheaf is an invertible `O_C`-module; equivalence in our situation: ticket `T-D1`
(blocked on API gap AG-LB). -/
structure RelEffCartierDiv (π : C ⟶ S) where
  /-- The ideal sheaf of the divisor. -/
  ideal : C.IdealSheafData
  finite : IsFinite (ideal.subschemeι ≫ π)
  flat : Flat (ideal.subschemeι ≫ π)
  lfp : LocallyOfFinitePresentation (ideal.subschemeι ≫ π)

namespace RelEffCartierDiv

variable {π : C ⟶ S}

/-- The degree of a relative effective Cartier divisor at `s : S` — the rank of the finite
locally free morphism `D ⟶ S` (KM 1.2; locally constant in `s`). -/
noncomputable def degree (D : RelEffCartierDiv π) (s : S) : ℕ :=
  haveI := D.finite
  haveI := D.flat
  (D.ideal.subschemeι ≫ π).finrank s

/-- The base-change square of a section is cartesian: `T` is the fibre product of
`C ×_S T ⟶ C` against the section `z`. -/
theorem isPullback_sectionBaseChange {π : C ⟶ S} (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    {T : Scheme.{u}} (t : T ⟶ S) :
    IsPullback
      (Limits.pullback.lift (t ≫ z) (𝟙 T)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]))
      t (Limits.pullback.fst π t) z := by
  have hb' : ∀ s : Limits.PullbackCone (Limits.pullback.fst π t) z,
      (s.fst ≫ Limits.pullback.snd π t) ≫ t = s.snd := by
    intro s
    have h2 : (s.fst ≫ Limits.pullback.fst π t) ≫ π =
        (s.fst ≫ Limits.pullback.snd π t) ≫ t := by
      rw [Category.assoc, Category.assoc, Limits.pullback.condition]
    calc (s.fst ≫ Limits.pullback.snd π t) ≫ t
        = (s.fst ≫ Limits.pullback.fst π t) ≫ π := h2.symm
      _ = (s.snd ≫ z) ≫ π := by rw [s.condition]
      _ = s.snd := by rw [Category.assoc, hz, Category.comp_id]
  refine IsPullback.of_isLimit' ⟨by rw [Limits.pullback.lift_fst]⟩ ?_
  refine Limits.PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ Limits.pullback.snd π t)
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_)
  · apply Limits.pullback.hom_ext
    · simp only [Category.assoc]
      rw [Limits.pullback.lift_fst, reassoc_of% (hb' s)]
      exact s.condition.symm
    · simp only [Category.assoc]
      rw [Limits.pullback.lift_snd, Category.comp_id]
  · exact hb' s
  · have h := congrArg (fun q => q ≫ Limits.pullback.snd π t) hm₁
    simp only [Category.assoc] at h
    rw [show Limits.pullback.lift (t ≫ z) (𝟙 T)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]) ≫
        Limits.pullback.snd π t = 𝟙 T from Limits.pullback.lift_snd _ _ _,
      Category.comp_id] at h
    exact h

/-- The kernel of a base-changed section is the scheme-theoretic preimage of the
kernel of the section. -/
theorem ker_sectionBaseChange {π : C ⟶ S} [IsSeparated π] (z : S ⟶ C)
    (hz : z ≫ π = 𝟙 S) {T : Scheme.{u}} (t : T ⟶ S) :
    (Limits.pullback.lift (t ≫ z) (𝟙 T)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]) :
      T ⟶ Limits.pullback π t).ker =
      (Scheme.Hom.ker z).comap (Limits.pullback.fst π t) := by
  haveI : IsClosedImmersion z := by
    have h1 : IsClosedImmersion (z ≫ π) := by rw [hz]; infer_instance
    exact IsClosedImmersion.of_comp z π
  rw [← (isPullback_sectionBaseChange z hz t).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- **(T-D3, single-section case — KM 1.2.2)** The divisor `[P]` of a single section of
a separated morphism: the closed subscheme cut out by the kernel ideal of the section.
Its subscheme is isomorphic to `S` itself (`IsIso z.toImage`), so all relative
finiteness properties transport from the identity. -/
noncomputable def sectionDivisor (π : C ⟶ S) [IsSeparated π] (z : S ⟶ C)
    (hz : z ≫ π = 𝟙 S) : RelEffCartierDiv π := by
  haveI hzc : IsClosedImmersion z := by
    have h1 : IsClosedImmersion (z ≫ π) := by
      rw [hz]
      infer_instance
    exact IsClosedImmersion.of_comp z π
  have hι : z.ker.subschemeι = inv z.toImage ≫ z := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  have hπ : z.ker.subschemeι ≫ π = inv z.toImage := by
    rw [hι, Category.assoc, hz, Category.comp_id]
  exact
    { ideal := z.ker
      finite := by rw [hπ]; infer_instance
      flat := by rw [hπ]; infer_instance
      lfp := by rw [hπ]; infer_instance }

/-- **(T-D3, single-section degree)** The divisor of a single section has degree `1`. -/
theorem sectionDivisor_degree (π : C ⟶ S) [IsSeparated π] (z : S ⟶ C)
    (hz : z ≫ π = 𝟙 S) (s : S) : (sectionDivisor π z hz).degree s = 1 := by
  haveI hzc : IsClosedImmersion z := by
    have h1 : IsClosedImmersion (z ≫ π) := by rw [hz]; infer_instance
    exact IsClosedImmersion.of_comp z π
  have hπ : (Scheme.Hom.ker z).subschemeι ≫ π = inv z.toImage := by
    rw [show (Scheme.Hom.ker z).subschemeι = inv z.toImage ≫ z from by
      rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι], Category.assoc, hz,
      Category.comp_id]
  show ((sectionDivisor π z hz).ideal.subschemeι ≫ π).finrank s = 1
  rw [show (sectionDivisor π z hz).ideal = Scheme.Hom.ker z from rfl, hπ]
  have h1 := Scheme.Hom.finrank_eq_one_of_isIso (inv z.toImage)
  simp [h1]

/-! #### T-D22 (HB-REGIMM, KM 1.2.2 / GME §2.1.4): local principality of a section ideal

Pure-algebra core: for an `R`-algebra retraction `σ : A →ₐ[R] R` of a standard-smooth
algebra of relative dimension `1`, the conormal argument (via `Ω[A⁄R]` free of rank one)
produces an explicit `f ∈ I := ker σ` with `I = (f) + I²`; Nakayama then gives `r ≡ 1 mod I`
with `r • I ≤ (f)`, and inverting `r` (a basic open around the section) makes `I` principal.
-/

section KerPrincipal

/-- Expansion of an element of a module with a singleton basis. -/
private theorem kerPrincipalAux_basis_expand {A : Type u} [CommRing A] {M : Type*}
    [AddCommGroup M] [Module A M] {ι : Type*} [Unique ι] (b : Module.Basis ι A M)
    (m : M) : m = b.repr m default • b default := by
  apply b.repr.injective
  refine Finsupp.ext fun j => ?_
  obtain rfl : j = default := Unique.eq_default j
  simp [Module.Basis.repr_self, smul_eq_mul]

/-- The kernel of a retraction `σ` of an algebra with `Ω[A⁄R]` free of rank one contains
an element whose differential's coordinate maps to `1` under `σ`. This is surjectivity of
(the retraction-twisted form of) the conormal map `I/I² → R ⊗[A] Ω[A⁄R]`. -/
private theorem kerPrincipalAux_exists_repr_one {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {ι : Type*} [Unique ι] (b : Module.Basis ι A (Ω[A⁄R]))
    (σ : A →ₐ[R] R) :
    ∃ x ∈ RingHom.ker σ,
      σ (b.repr (KaehlerDifferential.D R A x) default) = 1 := by
  classical
  have hσφ : ∀ r : R, σ (algebraMap R A r) = r := fun r => by simp
  set κ : A → A := fun x => b.repr (KaehlerDifferential.D R A x) default with hκdef
  have hκ_algebraMap_mul : ∀ (r : R) (x : A),
      κ (algebraMap R A r * x) = algebraMap R A r * κ x := by
    intro r x
    have h1 : KaehlerDifferential.D R A (algebraMap R A r * x)
        = algebraMap R A r • KaehlerDifferential.D R A x := by
      rw [Derivation.leibniz]
      simp [Derivation.map_algebraMap]
    show b.repr (KaehlerDifferential.D R A (algebraMap R A r * x)) default = _
    rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul]
  obtain ⟨x₀, hx₀⟩ : ∃ x : A, σ (κ x) = 1 := by
    have hmem : (b default : Ω[A⁄R])
        ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    have key : ∀ m ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)),
        ∃ x : A, σ (κ x) = σ (b.repr m default) := by
      intro m hm
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨a, rfl⟩ := hm; exact ⟨a, rfl⟩
      | zero => exact ⟨0, by simp [hκdef]⟩
      | add m₁ m₂ _ _ ih₁ ih₂ =>
        obtain ⟨x₁, h₁⟩ := ih₁
        obtain ⟨x₂, h₂⟩ := ih₂
        refine ⟨x₁ + x₂, ?_⟩
        have e1 : κ (x₁ + x₂) = κ x₁ + κ x₂ := by
          show b.repr (KaehlerDifferential.D R A (x₁ + x₂)) default = _
          rw [map_add, map_add, Finsupp.add_apply]
        rw [e1, map_add, h₁, h₂]
        conv_rhs => rw [map_add, Finsupp.add_apply, map_add]
      | smul a m _ ih =>
        obtain ⟨x, h⟩ := ih
        refine ⟨algebraMap R A (σ a) * x, ?_⟩
        rw [hκ_algebraMap_mul, map_mul, hσφ, h]
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
    obtain ⟨x, hx⟩ := key _ hmem
    refine ⟨x, ?_⟩
    rw [hx, Module.Basis.repr_self]
    simp
  refine ⟨x₀ - algebraMap R A (σ x₀), ?_, ?_⟩
  · simp [RingHom.mem_ker, map_sub, hσφ]
  · have h1 : KaehlerDifferential.D R A (x₀ - algebraMap R A (σ x₀))
        = KaehlerDifferential.D R A x₀ := by
      rw [map_sub, Derivation.map_algebraMap, sub_zero]
    rw [h1]
    exact hx₀

open scoped Pointwise in
/-- Conormal step for T-D22: if `Ω[A⁄R]` has a singleton basis and `σ` is an `R`-algebra
retraction of `A`, then `I := ker σ` satisfies `I ≤ (f) ⊔ I • I` for an explicit `f ∈ I`.
The generator is found via the (inverse of the) conormal isomorphism
`I/I² ≅ R ⊗[A] Ω[A⁄R]`, both directions of which are proved here by hand: surjectivity
because `d(φσa) = 0`, injectivity via the canonical derivation `a ↦ [a - φ(σ a)]` into
`A ⧸ I•I`. -/
private theorem kerPrincipalAux_le_span_sup {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {ι : Type*} [Unique ι] (b : Module.Basis ι A (Ω[A⁄R]))
    (σ : A →ₐ[R] R) :
    ∃ f ∈ RingHom.ker σ,
      RingHom.ker σ ≤ Ideal.span {f} ⊔ RingHom.ker σ • RingHom.ker σ := by
  classical
  set I : Ideal A := RingHom.ker σ with hI
  have hσφ : ∀ r : R, σ (algebraMap R A r) = r := fun r => by simp
  have hmemI : ∀ a : A, a - algebraMap R A (σ a) ∈ I := fun a => by
    simp [hI, RingHom.mem_ker, map_sub, hσφ]
  -- the coordinate of the differential with respect to the basis
  set κ : A → A := fun x => b.repr (KaehlerDifferential.D R A x) default with hκdef
  have hκ_add : ∀ x y, κ (x + y) = κ x + κ y := fun x y => by simp [hκdef]
  have hκ_algebraMap_mul : ∀ (r : R) (x : A),
      κ (algebraMap R A r * x) = algebraMap R A r * κ x := by
    intro r x
    have h1 : KaehlerDifferential.D R A (algebraMap R A r * x)
        = algebraMap R A r • KaehlerDifferential.D R A x := by
      rw [Derivation.leibniz]
      simp [Derivation.map_algebraMap]
    show b.repr (KaehlerDifferential.D R A (algebraMap R A r * x)) default = _
    rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul]
  -- expansion of a differential in the singleton basis
  have hDeq : ∀ x : A, KaehlerDifferential.D R A x = κ x • b default := fun x =>
    kerPrincipalAux_basis_expand b (KaehlerDifferential.D R A x)
  -- Step (i): the conormal generator, from `kerPrincipalAux_exists_repr_one`
  obtain ⟨f, hfI, hκf₀⟩ := kerPrincipalAux_exists_repr_one b σ
  rw [← hI] at hfI
  have hκf : σ (κ f) = 1 := hκf₀
  refine ⟨f, hfI, ?_⟩
  -- Step (ii): the canonical derivation into `A ⧸ I•I`
  set J : Ideal A := I • I with hJdef
  set L : A →ₗ[R] A ⧸ J :=
    (J.mkQ.restrictScalars R) ∘ₗ
      (LinearMap.id - (Algebra.linearMap R A ∘ₗ σ.toLinearMap)) with hLdef
  have hL : ∀ a : A, L a = Submodule.Quotient.mk (a - algebraMap R A (σ a)) := fun a => rfl
  set 𝔇 : Derivation R A (A ⧸ J) :=
    { toLinearMap := L
      map_one_eq_zero' := by
        rw [hL]
        simp
      leibniz' := by
        intro a c
        rw [hL, hL, hL, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
          ← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
        have h1 : a * c - algebraMap R A (σ (a * c)) -
            (a • (c - algebraMap R A (σ c)) + c • (a - algebraMap R A (σ a)))
            = -((a - algebraMap R A (σ a)) * (c - algebraMap R A (σ c))) := by
          simp only [smul_eq_mul, map_mul]
          ring
        rw [h1]
        exact neg_mem (hJdef ▸ Submodule.smul_mem_smul (hmemI a) (hmemI c)) } with h𝔇def
  have h𝔇 : ∀ a : A, 𝔇 a = Submodule.Quotient.mk (a - algebraMap R A (σ a)) := fun a => rfl
  -- the image of the lift lies in the image of `I`
  obtain ⟨i₀, hi₀I, hi₀⟩ : ∃ i₀ ∈ I,
      𝔇.liftKaehlerDifferential (b default) = Submodule.Quotient.mk i₀ := by
    have h1 : LinearMap.range 𝔇.liftKaehlerDifferential ≤ Submodule.map J.mkQ I := by
      rw [LinearMap.range_eq_map, ← KaehlerDifferential.span_range_derivation,
        Submodule.map_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      refine Submodule.mem_map.mpr ⟨a - algebraMap R A (σ a), hmemI a, ?_⟩
      rw [Derivation.liftKaehlerDifferential_comp_D, h𝔇, Submodule.mkQ_apply]
    obtain ⟨i₀, hi₀, heq⟩ := Submodule.mem_map.mp
      (h1 (LinearMap.mem_range_self _ (b default)))
    exact ⟨i₀, hi₀, heq.symm⟩
  -- the inclusion
  intro x hx
  set y := x - algebraMap R A (σ (κ x)) * f with hydef
  have hyI : y ∈ I := Ideal.sub_mem _ hx (Ideal.mul_mem_left _ _ hfI)
  have hκy : σ (κ y) = 0 := by
    have h1 : κ y = κ x - algebraMap R A (σ (κ x)) * κ f := by
      have h2 : y + algebraMap R A (σ (κ x)) * f = x := by rw [hydef]; ring
      have h3 := hκ_add y (algebraMap R A (σ (κ x)) * f)
      rw [h2, hκ_algebraMap_mul] at h3
      rw [eq_sub_iff_add_eq]
      exact h3.symm
    rw [h1, map_sub, map_mul, hσφ, hκf, mul_one, sub_self]
  have hκyI : κ y ∈ I := by rw [hI, RingHom.mem_ker]; exact hκy
  have hyJ : y ∈ J := by
    have hσy : σ y = 0 := by rw [← RingHom.mem_ker, ← hI]; exact hyI
    have h1 : Submodule.Quotient.mk (p := J) y = 𝔇 y := by
      rw [h𝔇, hσy, map_zero, sub_zero]
    have h2 : (𝔇 y : A ⧸ J) = κ y • 𝔇.liftKaehlerDifferential (b default) := by
      rw [← Derivation.liftKaehlerDifferential_comp_D 𝔇 y, hDeq y, map_smul]
    rw [h2, hi₀, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h1
    have h4 : κ y • i₀ ∈ J := hJdef ▸ Submodule.smul_mem_smul hκyI hi₀I
    simpa using J.add_mem h1 h4
  refine Submodule.mem_sup.mpr ⟨algebraMap R A (σ (κ x)) * f, ?_, y, hyJ, ?_⟩
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [hydef]; ring

/-- For a nontrivial standard-smooth algebra of relative dimension `1`, the chosen basis
index type of the (free, rank-one) module `Ω[A⁄R]` is a singleton. -/
@[reducible]
private noncomputable def kerPrincipalAux_unique_index (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Nontrivial A] [Algebra.IsStandardSmoothOfRelativeDimension 1 R A] :
    haveI : Algebra.IsStandardSmooth R A :=
      Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
    Unique (Module.Free.ChooseBasisIndex A (Ω[A⁄R])) := by
  haveI : Algebra.IsStandardSmooth R A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have hrank : Module.rank A (Ω[A⁄R]) = 1 :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1
  have h1 : Cardinal.mk (Module.Free.ChooseBasisIndex A (Ω[A⁄R])) = 1 := by
    rw [← Module.Free.rank_eq_card_chooseBasisIndex, hrank]
  rw [Cardinal.eq_one_iff_unique] at h1
  exact @Unique.mk' _ ⟨Classical.choice h1.2⟩ h1.1

/-- Existence of a "Nakayama-inverted" generator for the kernel of a retraction of a
standard-smooth algebra of relative dimension one: `f ∈ I` and `r ≡ 1 mod I` with
`r·I ⊆ (f)`. (T-D22 pure-algebra heart.) -/
private theorem kerPrincipalAux_exists_gen {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Nontrivial A] [Algebra.IsStandardSmoothOfRelativeDimension 1 R A]
    (σ : A →ₐ[R] R) :
    ∃ f ∈ RingHom.ker σ, ∃ r : A, r - 1 ∈ RingHom.ker σ ∧
      ∀ x ∈ RingHom.ker σ, r * x ∈ Ideal.span {f} := by
  haveI : Algebra.IsStandardSmooth R A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI := kerPrincipalAux_unique_index R A
  obtain ⟨f, hfI, hle⟩ :=
    kerPrincipalAux_le_span_sup (Module.Free.chooseBasis A (Ω[A⁄R])) σ
  have hfg : (RingHom.ker σ).FG := by
    have hsurj : Function.Surjective σ := fun r =>
      ⟨algebraMap R A r, by simp⟩
    exact Algebra.FinitePresentation.ker_fG_of_surjective σ hsurj
  obtain ⟨r, hr1, hrsm⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl hle
  exact ⟨f, hfI, r, hr1, fun x hx => by
    simpa [smul_eq_mul] using hrsm (Submodule.smul_mem_pointwise_smul x r _ hx)⟩

open TensorProduct in
/-- **T-D22 nonzerodivisor leg.** A generator of the kernel of a retraction of a
standard-smooth algebra of relative dimension `1` is a nonzerodivisor
(EGA IV 17.12.1 / KM 1.2.2).

Proof sketch: let `g := κ f` be the basis coordinate of `d f` in the rank-one free
module `Ω[A⁄R]`. The conormal argument shows `σ g` is a unit of `R`. On the
localization `A' := A[1/g]`, the differential `d f` *generates* `Ω[A'⁄R]`, so `A'` is
formally smooth over `P := R[X]` (`X ↦ f`) by the Jacobi–Zariski sequence, hence
`A'` is `P`-smooth, hence `P`-flat, and therefore `X`-torsion-free; so `f` is a
nonzerodivisor in `A'`. Finally, if `x·f = 0` in `A` then `x` dies in `A'`, i.e.
`gⁿ·x = 0`; writing `gⁿ = φ((σ g)ⁿ) + f·c` (binomially, since `g ≡ φ(σ g) mod (f)`)
and using `x·f = 0` once more gives `φ((σ g)ⁿ)·x = 0` with a unit factor, so `x = 0`. -/
private theorem kerPrincipalAux_nzd {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.IsStandardSmoothOfRelativeDimension 1 R A]
    (σ : A →ₐ[R] R) (f : A) (hf : RingHom.ker σ = Ideal.span {f}) :
    f ∈ nonZeroDivisors A := by
  classical
  rw [mem_nonZeroDivisors_iff]
  suffices key : ∀ x : A, x * f = 0 → x = 0 by
    exact ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact fun x _ => Subsingleton.elim x 0
  haveI : Algebra.IsStandardSmooth R A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI := kerPrincipalAux_unique_index R A
  set b := Module.Free.chooseBasis A (Ω[A⁄R]) with hbdef
  -- the coordinate of `d f`, whose image under `σ` is a unit
  set g : A := b.repr (KaehlerDifferential.D R A f) default with hgdef
  have hσf : σ f = 0 := by
    have h0 : f ∈ RingHom.ker σ := hf ▸ Ideal.subset_span (Set.mem_singleton f)
    rwa [RingHom.mem_ker] at h0
  have hunit : IsUnit (σ g) := by
    obtain ⟨f₀, hf₀I, hf₀κ⟩ := kerPrincipalAux_exists_repr_one b σ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hf ▸ hf₀I)
    rw [← hc] at hf₀κ
    have hkmul : b.repr (KaehlerDifferential.D R A (c * f)) default
        = c * b.repr (KaehlerDifferential.D R A f) default
          + f * b.repr (KaehlerDifferential.D R A c) default := by
      rw [Derivation.leibniz, map_add, map_smul, map_smul, Finsupp.add_apply,
        Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [hkmul, map_add, map_mul, map_mul, hσf, zero_mul, add_zero] at hf₀κ
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hf₀κ)
  -- the localization inverting `g`
  set A' := Localization.Away g with hA'def
  -- the key vanishing: any `x` with `x * f = 0` dies in `A'`
  have hkill : ∀ x : A, x * f = 0 → algebraMap A A' x = 0 := by
    rcases subsingleton_or_nontrivial A' with hA' | hA'
    · exact fun x _ => Subsingleton.elim _ _
    haveI hstdA' : Algebra.IsStandardSmoothOfRelativeDimension 1 R A' := by
      haveI h0 : Algebra.IsStandardSmoothOfRelativeDimension 0 A A' := by
        rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
        exact RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway A' g
      have h1 := Algebra.IsStandardSmoothOfRelativeDimension.trans
        (n := 1) (m := 0) R A A'
      simpa using h1
    haveI : Algebra.IsStandardSmooth R A' :=
      Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
    haveI := kerPrincipalAux_unique_index R A'
    set f' : A' := algebraMap A A' f with hf'def
    have hgu : IsUnit (algebraMap A A' g) :=
      IsLocalization.map_units A' (⟨g, Submonoid.mem_powers g⟩ : Submonoid.powers g)
    -- `d f'` generates `Ω[A'⁄R]`
    have hgen : ∀ m : Ω[A'⁄R], ∃ a : A', m = a • KaehlerDifferential.D R A' f' := by
      have hDf' : KaehlerDifferential.D R A' f'
          = algebraMap A A' g • KaehlerDifferential.map R R A A' (b default) := by
        rw [hf'def, ← KaehlerDifferential.map_D R R A A' f]
        conv_lhs => rw [kerPrincipalAux_basis_expand b (KaehlerDifferential.D R A f)]
        rw [map_smul, algebraMap_smul]
      obtain ⟨u, hu⟩ := hgu
      have hb0 : KaehlerDifferential.map R R A A' (b default)
          = (↑u⁻¹ : A') • KaehlerDifferential.D R A' f' := by
        rw [hDf', ← hu, smul_smul, Units.inv_mul, one_smul]
      intro m
      have hm : m ∈ Submodule.span A'
          (Set.range (KaehlerDifferential.map R R A A' ∘ KaehlerDifferential.D R A)) := by
        rw [KaehlerDifferential.span_range_map_derivation_of_isLocalization
          (R := R) (S := A) (T := A') (Submonoid.powers g)]
        trivial
      induction hm using Submodule.span_induction with
      | mem m hm =>
        obtain ⟨x, rfl⟩ := hm
        refine ⟨algebraMap A A' (b.repr (KaehlerDifferential.D R A x) default) * ↑u⁻¹, ?_⟩
        show KaehlerDifferential.map R R A A' (KaehlerDifferential.D R A x) = _
        conv_lhs => rw [kerPrincipalAux_basis_expand b (KaehlerDifferential.D R A x)]
        rw [map_smul,
          show (b.repr (KaehlerDifferential.D R A x) default)
              • KaehlerDifferential.map R R A A' (b default)
            = algebraMap A A' (b.repr (KaehlerDifferential.D R A x) default)
              • KaehlerDifferential.map R R A A' (b default) from
            (algebraMap_smul A' _ _).symm,
          hb0, smul_smul]
      | zero => exact ⟨0, by simp⟩
      | add m₁ m₂ _ _ ih₁ ih₂ =>
        obtain ⟨a₁, rfl⟩ := ih₁
        obtain ⟨a₂, rfl⟩ := ih₂
        exact ⟨a₁ + a₂, by rw [add_smul]⟩
      | smul a m _ ih =>
        obtain ⟨a₀, rfl⟩ := ih
        exact ⟨a * a₀, by rw [smul_smul]⟩
    -- `a • d f' = 0` forces `a = 0`
    have hreg : ∀ a : A', a • KaehlerDifferential.D R A' f' = 0 → a = 0 := by
      intro a ha
      set b' := Module.Free.chooseBasis A' (Ω[A'⁄R]) with hb'def
      obtain ⟨e, he⟩ := hgen (b' default)
      set c : A' := b'.repr (KaehlerDifferential.D R A' f') default with hcdef
      have h2 : e * c = 1 := by
        have h3 := congrArg (fun m => b'.repr m default) he
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul,
          Module.Basis.repr_self, Finsupp.single_eq_same] at h3
        exact h3.symm
      have h4 : a * c = 0 := by
        have h5 := congrArg (fun m => b'.repr m default) ha
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero,
          Finsupp.zero_apply] at h5
        exact h5
      calc a = a * (c * e) := by rw [mul_comm c e, h2, mul_one]
      _ = a * c * e := by ring
      _ = 0 := by rw [h4, zero_mul]
    -- the polynomial algebra `P = R[X]`, mapping `X ↦ f'`
    letI : Algebra (Polynomial R) A' := (Polynomial.aeval f').toRingHom.toAlgebra
    haveI : IsScalarTower R (Polynomial R) A' :=
      IsScalarTower.of_algebraMap_eq' (by
        ext r
        exact (Polynomial.aeval_C f' r).symm)
    have halgX : algebraMap (Polynomial R) A' Polynomial.X = f' := Polynomial.aeval_X f'
    -- `Ω[A'⁄P] = 0`
    have hΩP : Subsingleton (Ω[A'⁄Polynomial R]) := by
      have hzero : ∀ x : A', KaehlerDifferential.D (Polynomial R) A' x = 0 := by
        intro x
        obtain ⟨a, ha⟩ := hgen (KaehlerDifferential.D R A' x)
        have h1 := congrArg (KaehlerDifferential.map R (Polynomial R) A' A') ha
        rw [KaehlerDifferential.map_D, map_smul, KaehlerDifferential.map_D] at h1
        rw [show algebraMap A' A' x = x from by simp] at h1
        rw [show algebraMap A' A' f' = f' from by simp] at h1
        rw [← halgX, Derivation.map_algebraMap, smul_zero] at h1
        exact h1
      refine subsingleton_of_forall_eq 0 fun m => ?_
      have hm : m ∈ Submodule.span A'
          (Set.range (KaehlerDifferential.D (Polynomial R) A')) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨x, rfl⟩ := hm; exact hzero x
      | zero => rfl
      | add m₁ m₂ _ _ ih₁ ih₂ => rw [ih₁, ih₂, add_zero]
      | smul a m _ ih => rw [ih, smul_zero]
    -- injectivity of `mapBaseChange R P A'` (it sends the generator `1 ⊗ dX` to `d f'`)
    have hrep : ∀ t : A' ⊗[Polynomial R] (Ω[Polynomial R⁄R]), ∃ a : A', t = a •
        ((1 : A') ⊗ₜ[Polynomial R]
          KaehlerDifferential.D R (Polynomial R) Polynomial.X) := by
      intro t
      induction t with
      | zero => exact ⟨0, by simp⟩
      | tmul p ω =>
        obtain ⟨q, rfl⟩ : ∃ q : Polynomial R,
            ω = q • KaehlerDifferential.D R (Polynomial R) Polynomial.X := by
          refine ⟨KaehlerDifferential.polynomialEquiv R ω, ?_⟩
          conv_lhs =>
            rw [← (KaehlerDifferential.polynomialEquiv R).symm_apply_apply ω]
          rfl
        refine ⟨algebraMap (Polynomial R) A' q * p, ?_⟩
        have e1 : p ⊗ₜ[Polynomial R] (q • KaehlerDifferential.D R (Polynomial R) Polynomial.X)
            = (algebraMap (Polynomial R) A' q * p) ⊗ₜ[Polynomial R]
              KaehlerDifferential.D R (Polynomial R) Polynomial.X := by
          rw [TensorProduct.tmul_smul, ← algebraMap_smul A' q, TensorProduct.smul_tmul',
            smul_eq_mul]
        rw [e1, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add t₁ t₂ ih₁ ih₂ =>
        obtain ⟨a₁, rfl⟩ := ih₁
        obtain ⟨a₂, rfl⟩ := ih₂
        exact ⟨a₁ + a₂, by rw [add_smul]⟩
    have hker : ∀ t : A' ⊗[Polynomial R] (Ω[Polynomial R⁄R]),
        KaehlerDifferential.mapBaseChange R (Polynomial R) A' t = 0 → t = 0 := by
      intro t ht
      obtain ⟨a, rfl⟩ := hrep t
      rw [map_smul] at ht
      have h2 : KaehlerDifferential.mapBaseChange R (Polynomial R) A'
          ((1 : A') ⊗ₜ[Polynomial R]
            KaehlerDifferential.D R (Polynomial R) Polynomial.X)
          = KaehlerDifferential.D R A' f' := by
        rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, halgX,
          one_smul]
      rw [h2] at ht
      rw [hreg a ht, zero_smul]
    -- formal smoothness of `A'` over `P` via the Jacobi–Zariski sequence
    haveI hFS : Algebra.FormallySmooth (Polynomial R) A' := by
      rw [Algebra.formallySmooth_iff]
      refine ⟨?_, ?_⟩
      · haveI := hΩP
        haveI : Module.Free A' (Ω[A'⁄Polynomial R]) := Module.Free.of_subsingleton A' _
        infer_instance
      · refine subsingleton_of_forall_eq 0 fun x => ?_
        have hδ : Algebra.H1Cotangent.δ R (Polynomial R) A' x = 0 :=
          hker _ ((Algebra.H1Cotangent.exact_δ_mapBaseChange
            R (Polynomial R) A').apply_apply_eq_zero x)
        obtain ⟨y, hy⟩ :=
          (Algebra.H1Cotangent.exact_map_δ R (Polynomial R) A' x).mp hδ
        rw [← hy, Subsingleton.elim y 0, map_zero]
    -- `A'` is `P`-smooth, hence `P`-flat, hence `X`-torsion-free
    haveI hFP : Algebra.FinitePresentation (Polynomial R) A' :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation
        (R := R) (A := Polynomial R) (B := A')
    haveI hSm : Algebra.Smooth (Polynomial R) A' := ⟨hFS, hFP⟩
    haveI hFl : Module.Flat (Polynomial R) A' := Algebra.Smooth.flat _ _
    have hX : IsSMulRegular A' (Polynomial.X : Polynomial R) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors
        Polynomial.monic_X.mem_nonZeroDivisors
    intro x hx
    have hx' : (Polynomial.X : Polynomial R) • algebraMap A A' x
        = (Polynomial.X : Polynomial R) • (0 : A') := by
      rw [smul_zero, Algebra.smul_def, halgX, hf'def, ← map_mul, mul_comm f x, hx, map_zero]
    exact hX hx'
  -- endgame: from `gⁿ x = 0` and `g ≡ φ(σ g) mod (f)`, conclude `x = 0`
  intro x hx
  have h1 : algebraMap A A' x = 0 := hkill x hx
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers g)] at h1
  obtain ⟨m, hm⟩ := h1
  obtain ⟨n, hn⟩ := m.2
  rw [← hn] at hm
  -- `g` decomposes along the section
  have hgmem : g - algebraMap R A (σ g) ∈ RingHom.ker σ := by
    rw [RingHom.mem_ker, map_sub]
    simp
  obtain ⟨bb, hbb⟩ := Ideal.mem_span_singleton'.mp (hf ▸ hgmem)
  have hgeq : g = algebraMap R A (σ g) + bb * f := by rw [hbb]; ring
  obtain ⟨cc, hcc⟩ : ∃ cc : A, g ^ n = algebraMap R A ((σ g) ^ n) + f * cc := by
    clear hm hn
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨c₁, hc₁⟩ := ih
      refine ⟨algebraMap R A ((σ g) ^ k) * bb + c₁ * algebraMap R A (σ g)
        + c₁ * (bb * f), ?_⟩
      rw [pow_succ, hc₁, pow_succ, map_mul]
      linear_combination (algebraMap R A ((σ g) ^ k) + f * c₁) * hgeq
  have h2 : algebraMap R A ((σ g) ^ n) * x = 0 := by
    have h3 : g ^ n * x = 0 := hm
    rw [hcc, add_mul] at h3
    have h4 : f * cc * x = 0 := by
      calc f * cc * x = cc * (x * f) := by ring
      _ = 0 := by rw [hx, mul_zero]
    rwa [h4, add_zero] at h3
  have h5 : IsUnit (algebraMap R A ((σ g) ^ n)) := (hunit.pow n).map (algebraMap R A)
  exact (IsUnit.mul_right_eq_zero h5).mp h2


/-- Mapping a `⊆`-witnessed principal ideal into a localization inverting the Nakayama
multiplier makes it exactly principal. -/
private lemma kerPrincipalAux_ideal_map_span {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (r : A) [IsLocalization.Away r B] (I : Ideal A) (f : A) (hfI : f ∈ I)
    (hr : ∀ x ∈ I, r * x ∈ Ideal.span {f}) :
    I.map (algebraMap A B) = Ideal.span {algebraMap A B f} := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_)
    (Ideal.span_le.mpr ?_)
  · show algebraMap A B x ∈ Ideal.span {algebraMap A B f}
    have hu : IsUnit (algebraMap A B r) :=
      IsLocalization.map_units B (⟨r, Submonoid.mem_powers r⟩ : Submonoid.powers r)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hr x hx)
    have h1 : algebraMap A B x = ↑hu.unit⁻¹ * (algebraMap A B c * algebraMap A B f) := by
      rw [Units.eq_inv_mul_iff_mul_eq, IsUnit.unit_spec, ← map_mul, ← map_mul, hc]
    rw [h1]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
      (Ideal.subset_span (Set.mem_singleton _)))
  · rintro _ rfl
    exact Ideal.mem_map_of_mem _ hfI

variable (π) in
/-- Composing `π.appLE` with `z.appLE` along a "retraction pair" of opens gives the
identity, because `z ≫ π = 𝟙 S`. -/
private lemma kerPrincipalAux_retraction (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    {U : S.Opens} {V : C.Opens} (hVU : V ≤ π ⁻¹ᵁ U) (hUV : U ≤ z ⁻¹ᵁ V) :
    π.appLE U V hVU ≫ z.appLE V U hUV = 𝟙 Γ(S, U) := by
  rw [Scheme.Hom.appLE_comp_appLE]
  have h1 : ∀ (w : S ⟶ S), w = 𝟙 S → ∀ (e : U ≤ w ⁻¹ᵁ U), w.appLE U U e = 𝟙 Γ(S, U) := by
    rintro w rfl e
    have h5 : (𝟙 S : S ⟶ S).appLE U U e = S.presheaf.map (𝟙 (Opposite.op U)) := rfl
    rw [h5]
    exact S.presheaf.map_id (Opposite.op U)
  exact h1 _ hz _

/-- On a retraction pair `(U, V)`, points of `U` land via `z` in any basic open of `V`
whose "value along the section" is `1`. -/
private lemma kerPrincipalAux_le_preimage_basicOpen (z : S ⟶ C)
    {U : S.Opens} {V : C.Opens} (hUV : U ≤ z ⁻¹ᵁ V) (t : Γ(C, V))
    (ht : z.appLE V U hUV t = 1) : U ≤ z ⁻¹ᵁ C.basicOpen t := by
  intro s hs
  have hzs : z.base s ∈ V := hUV hs
  show z.base s ∈ C.basicOpen t
  rw [Scheme.mem_basicOpen C t (z.base s) hzs]
  have h2 : S.presheaf.germ U s hs (z.appLE V U hUV t)
      = z.stalkMap s (C.presheaf.germ V (z.base s) hzs t) := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    show S.presheaf.germ U s hs ((S.presheaf.map (homOfLE hUV).op) (z.app V t)) = _
    rw [TopCat.Presheaf.germ_res_apply]
  have h3 : IsUnit (z.stalkMap s (C.presheaf.germ V (z.base s) hzs t)) := by
    rw [← h2, ht, map_one]
    exact isUnit_one
  exact isUnit_of_map_unit _ _ h3

variable (π) in
/-- The preimage under the section of an open contained in `π ⁻¹ᵁ U` is contained
in `U`. -/
private lemma kerPrincipalAux_preimage_le (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    {U : S.Opens} {V : C.Opens} (hVU : V ≤ π ⁻¹ᵁ U) : z ⁻¹ᵁ V ≤ U := by
  intro s hs
  have h1 : π.base (z.base s) ∈ U := hVU hs
  have h2 : π.base (z.base s) = s := by
    have h3 : π.base (z.base s) = (z ≫ π).base s := rfl
    rw [h3, hz]
    rfl
  rwa [h2] at h1

variable (π) in
/-- Kernels of `z.app` and `z.appLE` agree on a retraction pair (the two target opens
are equal). -/
private lemma kerPrincipalAux_ker_app (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    {U : S.Opens} {V : C.Opens} (hVU : V ≤ π ⁻¹ᵁ U) (hUV : U ≤ z ⁻¹ᵁ V) :
    RingHom.ker (z.app V).hom = RingHom.ker (z.appLE V U hUV).hom := by
  haveI h3 : IsIso (homOfLE hUV) :=
    ⟨homOfLE (kerPrincipalAux_preimage_le π z hz hVU), Subsingleton.elim _ _,
      Subsingleton.elim _ _⟩
  have h2 : Function.Injective (S.presheaf.map (homOfLE hUV).op).hom :=
    (ConcreteCategory.bijective_of_isIso (S.presheaf.map (homOfLE hUV).op)).1
  have h4 : ∀ x : Γ(C, V), (z.appLE V U hUV).hom x
      = (S.presheaf.map (homOfLE hUV).op).hom ((z.app V).hom x) := fun _ => rfl
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, h4]
  exact ⟨fun h => by rw [h, map_zero], fun h => h2 (h.trans (map_zero _).symm)⟩

variable (π) in
/-- Transport of standard-smoothness of relative dimension `1` along a simultaneous
basic-open shrink of source and target (`IsAffineOpen.appLE_eq_away_map`). -/
private lemma kerPrincipalAux_stdSmooth_shrink {U₀ : S.Opens} {V₀ : C.Opens}
    (hU₀ : IsAffineOpen U₀) (hV₀ : IsAffineOpen V₀) (e₀ : V₀ ≤ π ⁻¹ᵁ U₀)
    (hstd : RingHom.IsStandardSmoothOfRelativeDimension 1 (π.appLE U₀ V₀ e₀).hom)
    (g : Γ(S, U₀)) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      (π.appLE (S.basicOpen g) (C.basicOpen (π.appLE U₀ V₀ e₀ g))
        (by simp [Scheme.Hom.appLE])).hom := by
  letI := hU₀.isLocalization_basicOpen g
  letI := hV₀.isLocalization_basicOpen (π.appLE U₀ V₀ e₀ g)
  rw [IsAffineOpen.appLE_eq_away_map π hU₀ hV₀ e₀ g, CommRingCat.hom_ofHom]
  exact (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves 1).away
    (π.appLE U₀ V₀ e₀).hom g _ _ hstd

variable (π) in
/-- Transport of standard-smoothness of relative dimension `1` along a basic-open
shrink of the source only. -/
private lemma kerPrincipalAux_stdSmooth_res {U : S.Opens} {V : C.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ π ⁻¹ᵁ U)
    (hstd : RingHom.IsStandardSmoothOfRelativeDimension 1 (π.appLE U V hVU).hom)
    (t : Γ(C, V)) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      (π.appLE U (C.basicOpen t) ((C.basicOpen_le t).trans hVU)).hom := by
  have h1 : π.appLE U (C.basicOpen t) ((C.basicOpen_le t).trans hVU)
      = π.appLE U V hVU ≫ C.presheaf.map (homOfLE (C.basicOpen_le t)).op :=
    (Scheme.Hom.appLE_map π hVU (homOfLE (C.basicOpen_le t)).op).symm
  rw [h1, CommRingCat.hom_comp]
  letI := hV.isLocalization_basicOpen t
  have h2 : RingHom.IsStandardSmoothOfRelativeDimension 0
      (C.presheaf.map (homOfLE (C.basicOpen_le t)).op).hom := by
    have h3 : algebraMap Γ(C, V) Γ(C, C.basicOpen t)
        = (C.presheaf.map (homOfLE (C.basicOpen_le t)).op).hom := rfl
    rw [← h3]
    exact RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway
      Γ(C, C.basicOpen t) t
  have h4 := RingHom.IsStandardSmoothOfRelativeDimension.comp h2 hstd
  simpa using h4

/-- **(T-D22 = HB-REGIMM, KM 1.2.2 / GME §2.1.4)** The kernel ideal of a section of a
smooth relative curve is, affine-locally on the total space, principal on a
nonzerodivisor. -/
theorem exists_affineOpen_ker_principal_nonZeroDivisor (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (c : C) :
    ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ f : Γ(C, V.1),
      (Scheme.Hom.ker z).ideal V = Ideal.span {f} ∧
      f ∈ nonZeroDivisors Γ(C, V.1) := by
  haveI hzc : IsClosedImmersion z := by
    have h1 : IsClosedImmersion (z ≫ π) := by rw [hz]; infer_instance
    exact IsClosedImmersion.of_comp z π
  by_cases hc : c ∈ (Scheme.Hom.ker z).support
  case neg =>
    -- `c` is off the section: the ideal is the unit ideal on a small affine.
    obtain ⟨_, ⟨W, hW, rfl⟩, hcW, hWs⟩ :=
      C.isBasis_affineOpens.exists_subset_of_mem_open (show c ∈ (_ᶜ : Set C) from hc)
        (Scheme.Hom.ker z).support.2.isOpen_compl
    refine ⟨⟨W, hW⟩, hcW, 1, ?_, one_mem _⟩
    have htop : (Scheme.Hom.ker z).ideal ⟨W, hW⟩ = ⊤ := by
      have h1 : C.zeroLocus (U := W) ((Scheme.Hom.ker z).ideal ⟨W, hW⟩ : Set _) ∩ W = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨h2, h3⟩
        exact hWs h3
          ((Scheme.Hom.ker z).zeroLocus_inter_subset_supportSet ⟨W, hW⟩ ⟨h2, h3⟩)
      have h4 := hW.fromSpec_image_zeroLocus
        ((Scheme.Hom.ker z).ideal ⟨W, hW⟩ : Set Γ(C, W))
      rw [h1, Set.image_eq_empty] at h4
      exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp h4
    rw [htop, Ideal.span_singleton_one]
  case pos =>
    -- `c` is on the section: `c = z s₀`.
    obtain ⟨s₀, hs₀⟩ : c ∈ Set.range ⇑z := by
      have h2 : c ∈ closure (Set.range ⇑z) := by
        rw [← Scheme.Hom.support_ker z]
        exact hc
      rwa [z.isClosedEmbedding.isClosed_range.closure_eq] at h2
    have hπz : ∀ s : S, π.base (z.base s) = s := by
      intro s
      have h3 : π.base (z.base s) = (z ≫ π).base s := rfl
      rw [h3, hz]
      rfl
    have hπc : π.base c = s₀ := by rw [← hs₀, hπz]
    -- initial standard-smooth chart around `c`
    obtain ⟨U₀, hU₀, V₀, hV₀, hcV₀, e₀, hstd₀⟩ :=
      hsm.exists_isStandardSmoothOfRelativeDimension c
    have hs₀U₀ : s₀ ∈ U₀ := by
      have h1 : π.base c ∈ U₀ := e₀ hcV₀
      rwa [hπc] at h1
    have hs₀z : s₀ ∈ z ⁻¹ᵁ V₀ := show z.base s₀ ∈ V₀ from hs₀ ▸ hcV₀
    -- shrink the base to a basic open inside `z ⁻¹ᵁ V₀`
    obtain ⟨g, hg_le, hs₀g⟩ :=
      hU₀.exists_basicOpen_le (V := z ⁻¹ᵁ V₀) ⟨s₀, hs₀z⟩ hs₀U₀
    -- the retraction pair `(U₁, V₁)`
    set U₁ : S.Opens := S.basicOpen g with hU₁def
    have hU₁ : IsAffineOpen U₁ := hU₀.basicOpen g
    set t₁ : Γ(C, V₀) := π.appLE U₀ V₀ e₀ g with ht₁def
    set V₁ : C.Opens := C.basicOpen t₁ with hV₁def
    have hV₁ : IsAffineOpen V₁ := hV₀.basicOpen t₁
    have ht₁app : t₁ = (C.presheaf.map (homOfLE e₀).op) (π.app U₀ g) := rfl
    have hV₁eq : V₁ = V₀ ⊓ π ⁻¹ᵁ U₁ := by
      rw [hV₁def, ht₁app, Scheme.basicOpen_res, hU₁def, ← Scheme.preimage_basicOpen]
    have hcV₁ : c ∈ V₁ := by
      rw [hV₁eq]
      exact ⟨hcV₀, show π.base c ∈ U₁ from hπc ▸ hs₀g⟩
    have hVU₁ : V₁ ≤ π ⁻¹ᵁ U₁ := hV₁eq.le.trans inf_le_right
    have hUV₁ : U₁ ≤ z ⁻¹ᵁ V₁ := by
      intro s hs
      show z.base s ∈ V₁
      rw [hV₁eq]
      refine ⟨hg_le hs, ?_⟩
      show π.base (z.base s) ∈ U₁
      rw [hπz s]
      exact hs
    -- standard smoothness of relative dimension 1 on the pair
    have hstd₁ : RingHom.IsStandardSmoothOfRelativeDimension 1 (π.appLE U₁ V₁ hVU₁).hom :=
      kerPrincipalAux_stdSmooth_shrink π hU₀ hV₀ e₀ hstd₀ g
    set φ₁ := π.appLE U₁ V₁ hVU₁ with hφ₁def
    set σ₁ := z.appLE V₁ U₁ hUV₁ with hσ₁def
    have hretr₁ : φ₁ ≫ σ₁ = 𝟙 Γ(S, U₁) := kerPrincipalAux_retraction π z hz hVU₁ hUV₁
    letI : Algebra Γ(S, U₁) Γ(C, V₁) := φ₁.hom.toAlgebra
    haveI halg₁ : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(S, U₁) Γ(C, V₁) := hstd₁
    set σA : Γ(C, V₁) →ₐ[Γ(S, U₁)] Γ(S, U₁) :=
      { toRingHom := σ₁.hom
        commutes' := fun a => by
          have h2 := congrArg (fun (w : Γ(S, U₁) ⟶ Γ(S, U₁)) => w.hom a) hretr₁
          simpa [RingHom.algebraMap_toAlgebra] using h2 } with hσAdef
    haveI : Nontrivial Γ(C, V₁) := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact (hV₁.primeIdealOf ⟨c, hcV₁⟩).isPrime.ne_top
        ((Ideal.eq_top_iff_one _).mpr
          (by rw [Subsingleton.elim (1 : Γ(C, V₁)) 0]; exact zero_mem _))
    -- the pure-algebra heart
    obtain ⟨f₀, hf₀I, r, hr1, hrmul⟩ := kerPrincipalAux_exists_gen σA
    have hkerA : RingHom.ker σA = RingHom.ker σ₁.hom := rfl
    -- the kernel-ideal dictionary at `V₁`
    have hker₁ : (Scheme.Hom.ker z).ideal ⟨V₁, hV₁⟩ = RingHom.ker σ₁.hom := by
      rw [Scheme.Hom.ker_apply]
      exact kerPrincipalAux_ker_app π z hz hVU₁ hUV₁
    have hr1' : r - 1 ∈ (Scheme.Hom.ker z).ideal ⟨V₁, hV₁⟩ := by
      rw [hker₁, ← hkerA]; exact hr1
    -- the final affine open `V₂ = D(r)`
    set V₂ : C.Opens := C.basicOpen r with hV₂def
    have hV₂ : IsAffineOpen V₂ := hV₁.basicOpen r
    have hcV₂ : c ∈ V₂ := by
      rw [hV₂def, Scheme.mem_basicOpen C r c hcV₁]
      have hnu : ¬IsUnit (C.presheaf.germ V₁ c hcV₁ (r - 1)) := by
        intro hu
        have hbo : c ∈ C.basicOpen (r - 1) :=
          (Scheme.mem_basicOpen C (r - 1) c hcV₁).mpr hu
        have hzl : c ∈ C.zeroLocus
            (U := V₁) ((Scheme.Hom.ker z).ideal ⟨V₁, hV₁⟩ : Set Γ(C, V₁)) :=
          (Scheme.IdealSheafData.mem_support_iff_of_mem hcV₁).mp hc
        exact (Scheme.mem_zeroLocus_iff C
          ((Scheme.Hom.ker z).ideal ⟨V₁, hV₁⟩ : Set Γ(C, V₁)) c).mp hzl _ hr1' hbo
      have hsum : (C.presheaf.germ V₁ c hcV₁) r
          = 1 + (C.presheaf.germ V₁ c hcV₁) (r - 1) := by
        conv_lhs => rw [show r = 1 + (r - 1) from by ring]
        rw [map_add, map_one]
      rw [hsum]
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
        ((1 : C.presheaf.stalk c) + (C.presheaf.germ V₁ c hcV₁) (r - 1)) with h | h
      · exact h
      · refine absurd ?_ hnu
        have h2 := h.neg
        rwa [show -(1 - (1 + (C.presheaf.germ V₁ c hcV₁) (r - 1)))
            = (C.presheaf.germ V₁ c hcV₁) (r - 1) from by ring] at h2
    -- retraction pair at `V₂`
    have hσ₁r : σ₁ r = 1 := by
      have h1 : σ₁.hom (r - 1) = 0 := by
        have h0 := hr1
        rwa [hkerA, RingHom.mem_ker] at h0
      have h2 : σ₁.hom r - 1 = 0 := by rwa [map_sub, map_one] at h1
      exact sub_eq_zero.mp h2
    have hUV₂ : U₁ ≤ z ⁻¹ᵁ V₂ :=
      kerPrincipalAux_le_preimage_basicOpen z hUV₁ r hσ₁r
    have hVU₂ : V₂ ≤ π ⁻¹ᵁ U₁ := (C.basicOpen_le r).trans hVU₁
    letI := hV₁.isLocalization_basicOpen r
    -- the generator over `V₂`
    set f : Γ(C, V₂) := (C.presheaf.map (homOfLE (C.basicOpen_le r)).op) f₀ with hfdef
    have hfalg : f = algebraMap Γ(C, V₁) Γ(C, V₂) f₀ := rfl
    have hideal : (Scheme.Hom.ker z).ideal ⟨V₂, hV₂⟩ = Ideal.span {f} := by
      have h1 := (Scheme.Hom.ker z).map_ideal_basicOpen ⟨V₁, hV₁⟩ r
      have h1' : (Scheme.Hom.ker z).ideal ⟨V₂, hV₂⟩
          = ((Scheme.Hom.ker z).ideal ⟨V₁, hV₁⟩).map
              (C.presheaf.map (homOfLE (C.basicOpen_le r)).op).hom := h1.symm
      rw [h1', hker₁, ← hkerA]
      have h3 : (C.presheaf.map (homOfLE (C.basicOpen_le r)).op).hom
          = algebraMap Γ(C, V₁) Γ(C, V₂) := rfl
      rw [h3, kerPrincipalAux_ideal_map_span r (RingHom.ker σA) f₀ hf₀I hrmul, hfalg]
    -- nonzerodivisor via the isolated leg
    have hstd₂ : RingHom.IsStandardSmoothOfRelativeDimension 1
        (π.appLE U₁ V₂ ((C.basicOpen_le r).trans hVU₁)).hom :=
      kerPrincipalAux_stdSmooth_res π hV₁ hVU₁ hstd₁ r
    set φ₂ := π.appLE U₁ V₂ hVU₂ with hφ₂def
    set σ₂ := z.appLE V₂ U₁ hUV₂ with hσ₂def
    have hretr₂ : φ₂ ≫ σ₂ = 𝟙 Γ(S, U₁) := kerPrincipalAux_retraction π z hz hVU₂ hUV₂
    letI : Algebra Γ(S, U₁) Γ(C, V₂) := φ₂.hom.toAlgebra
    haveI halg₂ : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(S, U₁) Γ(C, V₂) := hstd₂
    set σA₂ : Γ(C, V₂) →ₐ[Γ(S, U₁)] Γ(S, U₁) :=
      { toRingHom := σ₂.hom
        commutes' := fun a => by
          have h2 := congrArg (fun (w : Γ(S, U₁) ⟶ Γ(S, U₁)) => w.hom a) hretr₂
          simpa [RingHom.algebraMap_toAlgebra] using h2 } with hσA₂def
    have hker₂ : RingHom.ker σA₂ = Ideal.span {f} := by
      have h1 : (Scheme.Hom.ker z).ideal ⟨V₂, hV₂⟩ = RingHom.ker σ₂.hom := by
        rw [Scheme.Hom.ker_apply]
        exact kerPrincipalAux_ker_app π z hz hVU₂ hUV₂
      rw [show RingHom.ker σA₂ = RingHom.ker σ₂.hom from rfl, ← h1, hideal]
    exact ⟨⟨V₂, hV₂⟩, hcV₂, f, hideal, kerPrincipalAux_nzd σA₂ f hker₂⟩

end KerPrincipal

/-- **Register box (T-D3/T-D1, finiteness; KM 1.2.2 + 1.2.3)**: over a separated smooth
relative curve the product of the section ideals cuts out a subscheme finite over the
base. KM 1.2.3 (verbatim quote banked on T-D3): *"Let `D ⊆ C` be a closed sub-scheme
which is finite and flat over `S`, and of finite presentation over `S`. Then `D` is an
effective Cartier divisor in `C/S` … Conversely every effective Cartier divisor in
`C/S` which is proper over `S` is of this form."* Discharge is the T-D1 route
(invertible ideal sheaves, API gap AG-LB). -/
theorem sectionsIdeal_isFinite (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) :
    IsFinite ((∏ i, Scheme.Hom.ker (P i).1).subschemeι ≫ π) := by sorry

/-- **Register box (T-D3/T-D1, flatness; KM 1.2.2 + 1.2.3)** — see
`sectionsIdeal_isFinite`. -/
theorem sectionsIdeal_flat (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) :
    Flat ((∏ i, Scheme.Hom.ker (P i).1).subschemeι ≫ π) := by sorry

/-- **Register box (T-D3/T-D1, finite presentation; KM 1.2.2 + 1.2.3)** — see
`sectionsIdeal_isFinite`. -/
theorem sectionsIdeal_lfp (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) :
    LocallyOfFinitePresentation ((∏ i, Scheme.Hom.ker (P i).1).subschemeι ≫ π) := by
  sorry

/-- **Register box (T-D3, degree; KM 1.2.6)**: the divisor sum has rank `n` — KM 1.2.6
(verbatim quote banked on T-D3): *"`deg(D₁ + D₂) = deg(D₁) + deg(D₂)`"*, applied `n`
times to the degree-1 section divisors (`sectionDivisor_degree`); the SES argument
consumes the invertibility of the ideals (AG-LB), same gate as the other boxes. -/
theorem sectionsIdeal_finrank (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) (s : S) :
    haveI := sectionsIdeal_isFinite π hsm P
    haveI := sectionsIdeal_flat π hsm P
    ((∏ i, Scheme.Hom.ker (P i).1).subschemeι ≫ π).finrank s = n := by sorry

open scoped Classical in
noncomputable def sectionsDivisor (π : C ⟶ S) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) : RelEffCartierDiv π :=
  if h : IsSeparated π ∧ SmoothOfRelativeDimension 1 π then
    haveI := h.1
    { ideal := ∏ i, Scheme.Hom.ker (P i).1
      finite := sectionsIdeal_isFinite π h.2 P
      flat := sectionsIdeal_flat π h.2 P
      lfp := sectionsIdeal_lfp π h.2 P }
  else
    { ideal := ⊤
      finite := ((IsClosedImmersion.iff_isFinite_and_mono
        ((⊤ : C.IdealSheafData).subschemeι ≫ π)).mp inferInstance).1
      flat := inferInstance
      lfp := inferInstance }

/-- **(T-D3a, specification of DS4a)** `Σᵢ [Pᵢ]` has degree `n`, under KM 1.2.1's
standing hypotheses.

ADVERSARIAL FIX (2026-07-06): the hypotheses are REQUIRED — for `π = 𝟙 (Spec k)`,
`n = 2`, no degree-2 divisor in `Spec k` exists at all (statement was unsatisfiable
by any data filling); on the nodal `Spec k[x,y]/(xy)` the squared node-section ideal
has length `3 ≠ 2`. Source: KM 1.2.2, proved under the standing assumptions of
KM 1.2.1. -/
theorem sectionsDivisor_degree (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) (s : S) :
    (sectionsDivisor π P).degree s = n := by
  have h : IsSeparated π ∧ SmoothOfRelativeDimension 1 π := ⟨‹_›, hsm⟩
  show ((sectionsDivisor π P).ideal.subschemeι ≫ π).finrank s = n
  rw [show (sectionsDivisor π P).ideal = ∏ i, Scheme.Hom.ker (P i).1 from by
    rw [sectionsDivisor, dif_pos h]]
  exact sectionsIdeal_finrank π hsm P s

/-- Base change of a relative effective Cartier divisor along `t : T ⟶ S`: the ideal
sheaf of the base-changed closed subscheme `D ×_S T ↪ C ×_S T` (kernel ideal of the
pulled-back closed immersion), as a divisor in the base-changed curve (structure
morphism `pullback.snd π t`). Finiteness/flatness/finite presentation are base-change
stability, ticket `T-D12`; formation is functorial (KM 1.1). -/
private lemma baseChange_prop (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.RespectsIso] (D : RelEffCartierDiv π)
    {T : Scheme.{u}} (t : T ⟶ S) (hD : P (D.ideal.subschemeι ≫ π)) :
    P ((pullback.snd D.ideal.subschemeι (pullback.fst π t)).ker.subschemeι ≫
      pullback.snd π t) := by
  haveI : IsClosedImmersion (pullback.snd D.ideal.subschemeι (pullback.fst π t)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hι : (pullback.snd D.ideal.subschemeι (pullback.fst π t)).ker.subschemeι =
      inv (pullback.snd D.ideal.subschemeι (pullback.fst π t)).toImage ≫
        pullback.snd D.ideal.subschemeι (pullback.fst π t) := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  have hsq := (IsPullback.of_hasPullback D.ideal.subschemeι
    (pullback.fst π t)).paste_vert (IsPullback.of_hasPullback π t)
  have hP : P (pullback.snd D.ideal.subschemeι (pullback.fst π t) ≫
      pullback.snd π t) :=
    MorphismProperty.of_isPullback hsq hD
  rw [hι, Category.assoc]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mpr hP

noncomputable def baseChange (D : RelEffCartierDiv π) {T : Scheme.{u}} (t : T ⟶ S) :
    RelEffCartierDiv (pullback.snd π t) where
  ideal := (pullback.snd D.ideal.subschemeι (pullback.fst π t)).ker
  finite := baseChange_prop @IsFinite D t D.finite
  flat := baseChange_prop @Flat D t D.flat
  lfp := baseChange_prop @LocallyOfFinitePresentation D t D.lfp

/-- The ideal sheaf of a base-changed divisor is the scheme-theoretic preimage of the
original ideal along the first projection. -/
theorem baseChange_ideal (D : RelEffCartierDiv π) {T : Scheme.{u}} (t : T ⟶ S) :
    (D.baseChange t).ideal = D.ideal.comap (Limits.pullback.fst π t) := by
  show (Limits.pullback.snd D.ideal.subschemeι (Limits.pullback.fst π t)).ker =
    D.ideal.comap (Limits.pullback.fst π t)
  rw [show (Limits.pullback.snd D.ideal.subschemeι (Limits.pullback.fst π t)) =
      (Limits.pullbackSymmetry D.ideal.subschemeι (Limits.pullback.fst π t)).hom ≫
        Limits.pullback.fst (Limits.pullback.fst π t) D.ideal.subschemeι from
    (Limits.pullbackSymmetry_hom_comp_fst _ _).symm,
    Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    Scheme.IdealSheafData.ker_subschemeι]

end RelEffCartierDiv

section FullSections

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

open TensorProduct in
/-- The base change of a section `P : B →ₐ[R] R` to an `R`-algebra `A`, as a section
`A ⊗[R] B →ₐ[A] A`. -/
noncomputable def AlgHom.sectionBaseChange (A : Type u) [CommRing A] [Algebra R A]
    (P : B →ₐ[R] R) : A ⊗[R] B →ₐ[A] A :=
  ((Algebra.TensorProduct.rid R A A).toAlgHom).comp
    (Algebra.TensorProduct.map (AlgHom.id A A) P)

open TensorProduct in
/-- **Full set of sections, affine case** (KM 1.8.2; universal-norm form of KM 1.9.1).
`B` an `R`-algebra (finite locally free as `R`-module in applications), sections
`P₁, ⋯, Pₙ : B →ₐ[R] R`. They are a *full set of sections* of `Spec B / Spec R` if for
every `R`-algebra `A` and every `f ∈ A ⊗_R B`:
`Norm_{(A ⊗ B)/A}(f) = ∏ᵢ (Pᵢ)_A(f)`.

Verbatim source (proof of KM 1.9.1): "The points `P₁,…,P_N` form a full set of sections of
`Spec(B)/R` if and only if this universal `f` satisfies `Norm(f) = ∏ f(Pᵢ)` in
`R[T₁,…,T_N]`" — quantifying over all `A` is equivalent by base change (KM 1.8.4).

ADVERSARIAL FIX (2026-07-06): `[Module.Free R B] [Module.Finite R B]` are REQUIRED —
mathlib's `Algebra.norm` is junk (constantly `1`) on modules with no finite basis, so
without freeness the definition is falsely strong on the locally-free-non-free stratum
(e.g. `B` of rank `N` with nontrivial determinant line: the legitimate full set
`P₁ = ⋯ = P_N = 0` fails the equation at `f = 0`, `1 ≠ 0`). For `B` free, `A ⊗[R] B`
is free over every `A`, so the norm is honest throughout the quantifier. KM's
projective case must be reached via a trivialising cover (T-D4), never by applying
this definition on arbitrary affines. -/
def IsFullSetOfSectionsAlg [Module.Free R B] [Module.Finite R B] {n : ℕ}
    (P : Fin n → (B →ₐ[R] R)) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A],
    ∀ f : A ⊗[R] B,
      Algebra.norm A f = ∏ i, AlgHom.sectionBaseChange R B A (P i) f

/-- In a reduced commutative ring, two elements are equal as soon as every ring
homomorphism to a field identifies them (the difference lies in every prime, hence in
the nilradical). -/
theorem eq_of_forall_field_hom_eq {A₀ : Type u} [CommRing A₀] [IsReduced A₀]
    {x y : A₀} (h : ∀ (K : Type u) [Field K] (χ : A₀ →+* K), χ x = χ y) : x = y := by
  have hd : x - y ∈ nilradical A₀ := by
    rw [nilradical_eq_sInf]
    refine Ideal.mem_sInf.mpr ?_
    rintro p hp
    haveI : p.IsPrime := hp
    have hχ := h (FractionRing (A₀ ⧸ p))
      ((algebraMap (A₀ ⧸ p) (FractionRing (A₀ ⧸ p))).comp (Ideal.Quotient.mk p))
    have hmk : Ideal.Quotient.mk p x = Ideal.Quotient.mk p y := by
      apply IsFractionRing.injective (A₀ ⧸ p) (FractionRing (A₀ ⧸ p))
      simpa using hχ
    simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using hmk
  rw [nilradical_eq_zero] at hd
  exact sub_eq_zero.mp (by simpa using hd)

open TensorProduct in
/-- Sections base-change functorially: transporting `f` along `ψ : A →ₐ[R] A'` and
evaluating the section agrees with evaluating over `A` and applying `ψ`. -/
theorem sectionBaseChange_tensor_map {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] (ψ : A →ₐ[R] A') (P : B →ₐ[R] R) (f : A ⊗[R] B) :
    AlgHom.sectionBaseChange R B A' P (Algebra.TensorProduct.map ψ (AlgHom.id R B) f) =
      ψ (AlgHom.sectionBaseChange R B A P f) := by
  induction f with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp [h₁, h₂]
  | tmul a b =>
    simp [AlgHom.sectionBaseChange, Algebra.smul_def, map_mul]

/-- **(T-D2 = KM 1.9.2, verbatim source in hand with proof)** Over a *reduced* base, "in
order that `P₁,…,P_N` form a full set of sections of `Z/S`, it is necessary and sufficient
that for every geometric point `Spec(k) → S` … `Norm(f) = ∏ f((Pᵢ)_k)`" — i.e. it suffices
to check the norm equation after base change to every residue field. -/
theorem isFullSetOfSectionsAlg_iff_fields [IsReduced R] [Module.Free R B]
    [Module.Finite R B] {n : ℕ} (P : Fin n → (B →ₐ[R] R)) :
    IsFullSetOfSectionsAlg R B P ↔
      ∀ (K : Type u) [Field K] [Algebra R K], ∀ f : TensorProduct R K B,
        Algebra.norm K f = ∏ i, AlgHom.sectionBaseChange R B K (P i) f := by
  classical
  constructor
  · intro h K _ _ f
    exact h K f
  · intro h A _ _ f
    set ι := Module.Free.ChooseBasisIndex R B with hι
    set b : Module.Basis ι R B := Module.Free.chooseBasis R B with hb
    set A₀ := MvPolynomial ι R with hA₀
    set f₀ : TensorProduct R A₀ B :=
      ∑ j, (MvPolynomial.X j : A₀) ⊗ₜ[R] (b j) with hf₀
    have huniv : Algebra.norm A₀ f₀ =
        ∏ i, AlgHom.sectionBaseChange R B A₀ (P i) f₀ := by
      apply eq_of_forall_field_hom_eq
      intro K _ χ₀
      letI : Algebra R K := (χ₀.comp (algebraMap R A₀)).toAlgebra
      let χ : A₀ →ₐ[R] K := { toRingHom := χ₀, commutes' := fun r => rfl }
      have hK := h K ((Algebra.TensorProduct.map χ (AlgHom.id R B)) f₀)
      rw [norm_tensor_map χ f₀] at hK
      rw [Finset.prod_congr rfl
        (fun i _ => sectionBaseChange_tensor_map R B χ (P i) f₀), ← map_prod] at hK
      exact hK
    have hbbdef : ∀ (bb : Module.Basis ι A (TensorProduct R A B)),
        bb = Algebra.TensorProduct.basis A b →
        (Algebra.TensorProduct.map
          (MvPolynomial.aeval (fun j => bb.repr f j) : A₀ →ₐ[R] A)
          (AlgHom.id R B)) f₀ = f := by
      intro bb hbb
      rw [hf₀, map_sum]
      have hterm : ∀ j : ι,
          (Algebra.TensorProduct.map
            (MvPolynomial.aeval (fun j => bb.repr f j) : A₀ →ₐ[R] A)
            (AlgHom.id R B)) ((MvPolynomial.X j : A₀) ⊗ₜ[R] (b j)) =
          (bb.repr f j : A) ⊗ₜ[R] (b j) := by
        intro j
        rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          MvPolynomial.aeval_X]
      rw [Finset.sum_congr rfl fun j _ => hterm j]
      calc ∑ j, (bb.repr f j : A) ⊗ₜ[R] (b j)
          = ∑ j, (bb.repr f j : A) • ((1 : A) ⊗ₜ[R] (b j)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        _ = ∑ j, bb.repr f j • bb j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hbb, Algebra.TensorProduct.basis_apply]
        _ = f := bb.sum_repr f
    set bb : Module.Basis ι A (TensorProduct R A B) :=
      Algebra.TensorProduct.basis A b with hbb
    set φ : A₀ →ₐ[R] A := MvPolynomial.aeval (fun j => bb.repr f j) with hφ
    have hf : (Algebra.TensorProduct.map φ (AlgHom.id R B)) f₀ = f :=
      hbbdef bb hbb
    calc Algebra.norm A f
        = Algebra.norm A ((Algebra.TensorProduct.map φ (AlgHom.id R B)) f₀) := by
          rw [hf]
      _ = φ (Algebra.norm A₀ f₀) := norm_tensor_map φ f₀
      _ = φ (∏ i, AlgHom.sectionBaseChange R B A₀ (P i) f₀) := by rw [huniv]
      _ = ∏ i, φ (AlgHom.sectionBaseChange R B A₀ (P i) f₀) := map_prod φ _ _
      _ = ∏ i, AlgHom.sectionBaseChange R B A (P i) f := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← sectionBaseChange_tensor_map R B φ (P i) f₀, hf]

end FullSections

end ModularCurves
