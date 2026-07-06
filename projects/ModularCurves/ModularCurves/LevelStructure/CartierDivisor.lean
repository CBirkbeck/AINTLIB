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

/-- **(DS4a, ticket T-D3)** The divisor `Σᵢ [Pᵢ]` attached to a finite family of sections
of `π` — the closed subscheme whose ideal is the *product* of the ideal sheaves of the
(closed-immersion) sections. DATA-SORRY (register entry DS4a).

SCOPE (adversarial pass 2026-07-06): the construction and its specifications are pinned
under KM 1.2.1's standing hypotheses — `π` separated (sections are closed immersions)
and smooth of relative dimension 1 (ideal products have the right length); the data
slot is total, but nothing is promised outside that scope. Specifications: degree `= n`
(`sectionsDivisor_degree`, hypothesised accordingly), and formation commutes with
arbitrary base change (KM 1.1). -/
noncomputable def sectionsDivisor (π : C ⟶ S) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) : RelEffCartierDiv π := sorry

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
    (sectionsDivisor π P).degree s = n := by sorry

/-- Base change of a relative effective Cartier divisor along `t : T ⟶ S`: the ideal
sheaf of the base-changed closed subscheme `D ×_S T ↪ C ×_S T` (kernel ideal of the
pulled-back closed immersion), as a divisor in the base-changed curve (structure
morphism `pullback.snd π t`). Finiteness/flatness/finite presentation are base-change
stability, ticket `T-D12`; formation is functorial (KM 1.1). -/
noncomputable def baseChange (D : RelEffCartierDiv π) {T : Scheme.{u}} (t : T ⟶ S) :
    RelEffCartierDiv (pullback.snd π t) where
  ideal := (pullback.snd D.ideal.subschemeι (pullback.fst π t)).ker
  finite := by sorry
  flat := by sorry
  lfp := by sorry

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
