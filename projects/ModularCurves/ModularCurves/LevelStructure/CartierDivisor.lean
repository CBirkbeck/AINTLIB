import ModularCurves.EllipticCurve.GroupLaw
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Nilpotent
import ModularCurves.ForMathlib.NormBaseChange

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
