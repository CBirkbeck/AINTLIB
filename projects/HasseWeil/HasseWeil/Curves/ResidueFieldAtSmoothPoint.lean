import HasseWeil.Curves.NormValuation
import HasseWeil.Curves.CurveMap
import HasseWeil.Curves.GenericFiber
import Mathlib.RingTheory.Finiteness.Quotient

/-!
# Residue-field AlgEquiv route for Piece 9

**Goal**: sidestep the `Module.Free`/`Module.Finite` diamond blocking
stream A's Piece 9 by building an **explicit** `F`-algebra isomorphism
`C.CR/M ≃ₐ[F] F` at each smooth-point-maximal-ideal over algebraically
closed `F`. With this iso in hand, the inertia-degree computation for
`C₂.CR/Q → C₁.CR/P` reduces to a finrank computation we can do
directly via the iso instead of going through `finrank_mul_finrank`
or `Module.Finite` on the quotient pair.

## Status

**Partial.** This file delivers the core AlgEquiv:

* `SmoothPlaneCurve.quotientAlgEquivBase` — `C.CR/M ≃ₐ[F] F` under
  `[IsAlgClosed F]` for any maximal ideal `M ⊂ C.CR`.

Given this, the full Piece 9 closure
(`CurveMap.CoordHom.inertiaDeg_eq_one_of_isAlgClosed`) still requires
the Module instance on the quotient pair. Even with the AlgEquiv, Lean
needs `Module (C₂.CR/Q) (C₁.CR/P)` in scope to state the finrank — and
that's the specific instance coming out of `Ideal.Quotient`'s default
algebra structure. The AlgEquiv lets us **transport** known facts, but
doesn't itself create the Module instance.

## What this unlocks

With `quotientAlgEquivBase` in place:
* Any consumer that can supply the `Module` instance explicitly
  (e.g., by working in a local section where both structures are
  established by `letI` + `attribute [local instance]`) can use the
  iso to compute finrank.
* The iso can be composed to produce the full
  `(C₂.CR/Q) ≃ₐ[F] (C₁.CR/P)` as F-algebras, which in principle
  characterises the quotient pair up to F-linear isomorphism.

The remaining gap is the final transport step — the instance-search
concern that neither worker-K nor worker A could work around in the
generic `CurveMap` setting.
-/

open IsDedekindDomain

namespace HasseWeil.Curves

variable {F : Type*} [Field F]

/-! ### AlgEquiv `C.CR/M ≃ₐ[F] F` via bijective algebra map -/

/-- **F-algebra isomorphism from residue field of maximal ideal to F**.

Under `[IsAlgClosed F]`, for any maximal ideal `M ⊂ C.CR`, the structure
map `algebraMap F (C.CR/M)` is bijective (worker-K's
`algebraMap_bijective_quotient_of_maximal` via Zariski's lemma + alg-
closure). Promoting that bijection to an `AlgEquiv` gives the explicit
residue-field identification used by Piece 9. -/
noncomputable def SmoothPlaneCurve.quotientAlgEquivBase
    [IsAlgClosed F] (C : SmoothPlaneCurve F)
    {M : Ideal C.CoordinateRing} (hM : M.IsMaximal) :
    letI : Field (C.CoordinateRing ⧸ M) := Ideal.Quotient.field M
    F ≃ₐ[F] (C.CoordinateRing ⧸ M) :=
  letI : Field (C.CoordinateRing ⧸ M) := Ideal.Quotient.field M
  AlgEquiv.ofBijective (Algebra.ofId F (C.CoordinateRing ⧸ M))
    (C.algebraMap_bijective_quotient_of_maximal hM)

@[simp] theorem SmoothPlaneCurve.quotientAlgEquivBase_apply
    [IsAlgClosed F] (C : SmoothPlaneCurve F)
    {M : Ideal C.CoordinateRing} (hM : M.IsMaximal) (c : F) :
    letI : Field (C.CoordinateRing ⧸ M) := Ideal.Quotient.field M
    C.quotientAlgEquivBase hM c = algebraMap F (C.CoordinateRing ⧸ M) c :=
  rfl

/-! ### Composed AlgEquiv (C₂.CR/Q) ≃ₐ[F] (C₁.CR/P)

Composing `quotientAlgEquivBase` for both sides gives an F-algebra iso
between the two residue fields — both are F via the base, so any pair
is F-isomorphic.

This is the content Silverman II.2.6(b) uses at the residue-field level:
over alg-closed, the residue extensions `(C₂.CR/Q) → (C₁.CR/P)` are
trivial. -/

/-- **Two residue fields are F-isomorphic** (over alg-closed). -/
noncomputable def SmoothPlaneCurve.residueFieldsAlgEquiv
    [IsAlgClosed F]
    (C₁ C₂ : SmoothPlaneCurve F)
    {Q : Ideal C₂.CoordinateRing} (hQ : Q.IsMaximal)
    {P : Ideal C₁.CoordinateRing} (hP : P.IsMaximal) :
    letI : Field (C₂.CoordinateRing ⧸ Q) := Ideal.Quotient.field Q
    letI : Field (C₁.CoordinateRing ⧸ P) := Ideal.Quotient.field P
    (C₂.CoordinateRing ⧸ Q) ≃ₐ[F] (C₁.CoordinateRing ⧸ P) :=
  letI : Field (C₂.CoordinateRing ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (C₁.CoordinateRing ⧸ P) := Ideal.Quotient.field P
  (C₂.quotientAlgEquivBase hQ).symm.trans (C₁.quotientAlgEquivBase hP)

/-! ### LinearEquiv transport + inertiaDeg closure -/

variable {C₁ C₂ : SmoothPlaneCurve F}

/-- **LinearEquiv from bijective algebra map** (generic): if the algebra
map `R → S` is bijective, then `R ≃ₗ[R] S` as `R`-modules. -/
noncomputable def LinearEquiv.ofBijectiveAlgebraMap
    {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (h : Function.Bijective (algebraMap R S)) :
    R ≃ₗ[R] S :=
  LinearEquiv.ofBijective (Algebra.linearMap R S) h

/-- **Under `[IsAlgClosed F]`, algebra map on residue fields is injective**.
Any ring hom between fields with a nonzero source is injective; the
algebra map `(C₂.CR/Q) → (C₁.CR/P)` is nonzero because the source is a
field. -/
theorem algebraMap_residueField_injective
    [IsAlgClosed F]
    {Q : Ideal C₂.CoordinateRing} (hQ : Q.IsMaximal)
    {P : Ideal C₁.CoordinateRing} (hP : P.IsMaximal)
    (φ : Curves.CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    (hLies :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      P.LiesOver Q) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    letI : Field (C₂.CoordinateRing ⧸ Q) := Ideal.Quotient.field Q
    letI : Field (C₁.CoordinateRing ⧸ P) := Ideal.Quotient.field P
    Function.Injective
      (algebraMap (C₂.CoordinateRing ⧸ Q) (C₁.CoordinateRing ⧸ P)) := by
  letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
  haveI := hLies
  letI : Field (C₂.CoordinateRing ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (C₁.CoordinateRing ⧸ P) := Ideal.Quotient.field P
  -- AlgHoms between fields are injective (as ring homs).
  exact (algebraMap (C₂.CoordinateRing ⧸ Q) (C₁.CoordinateRing ⧸ P)).injective

/-- **Residue-field LinearEquiv** over the quotient scalar ring.

The combined output of:
* surjectivity of `algebraMap (C₂.CR/Q) (C₁.CR/P)` (from both F→quotient
  bijections + scalar tower), and
* injectivity (fields).

This gives a `(C₂.CR/Q)`-linear equivalence between `(C₂.CR/Q)` and
`(C₁.CR/P)` — the key ingredient for `finrank = 1`. -/
noncomputable def CurveMap.CoordHom.residueLinearEquiv
    [IsAlgClosed F]
    (φ : Curves.CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    {Q : Ideal C₂.CoordinateRing} (hQ : Q.IsMaximal)
    {P : Ideal C₁.CoordinateRing} (hP : P.IsMaximal)
    (hLies :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      P.LiesOver Q)
    (hScalarTower :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      IsScalarTower F (C₂.CoordinateRing ⧸ Q) (C₁.CoordinateRing ⧸ P)) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    letI : Field (C₂.CoordinateRing ⧸ Q) := Ideal.Quotient.field Q
    letI : Field (C₁.CoordinateRing ⧸ P) := Ideal.Quotient.field P
    (C₂.CoordinateRing ⧸ Q) ≃ₗ[C₂.CoordinateRing ⧸ Q] (C₁.CoordinateRing ⧸ P) := by
  letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
  haveI := hLies
  letI : Field (C₂.CoordinateRing ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (C₁.CoordinateRing ⧸ P) := Ideal.Quotient.field P
  haveI := hScalarTower
  have hFQ := C₂.algebraMap_bijective_quotient_of_maximal hQ
  have hFP := C₁.algebraMap_bijective_quotient_of_maximal hP
  have h_surj :
      Function.Surjective
        (algebraMap (C₂.CoordinateRing ⧸ Q) (C₁.CoordinateRing ⧸ P)) := by
    intro b
    obtain ⟨c, hc⟩ := hFP.2 b
    refine ⟨algebraMap F (C₂.CoordinateRing ⧸ Q) c, ?_⟩
    rw [← IsScalarTower.algebraMap_apply F (C₂.CoordinateRing ⧸ Q)
      (C₁.CoordinateRing ⧸ P) c]
    exact hc
  have h_inj := algebraMap_residueField_injective hQ hP φ coordHom hLies
  exact LinearEquiv.ofBijectiveAlgebraMap ⟨h_inj, h_surj⟩

/-- **Full Piece 9 closure via LinearEquiv transport**: `inertiaDeg = 1`
for any `CurveMap.CoordHom` lying-over pair under `[IsAlgClosed F]`.

Uses `residueLinearEquiv` above to transport `finrank_self = 1` from
`(C₂.CR/Q)` to `(C₁.CR/P)` without needing `Module.Finite` or the
`Module.Free` diamond. -/
theorem CurveMap.CoordHom.inertiaDeg_eq_one_of_isAlgClosed
    [IsAlgClosed F]
    (φ : Curves.CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    {Q : Ideal C₂.CoordinateRing} (hQ : Q.IsMaximal)
    {P : Ideal C₁.CoordinateRing} (hP : P.IsMaximal)
    (hLies :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      P.LiesOver Q)
    (hScalarTower :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      IsScalarTower F (C₂.CoordinateRing ⧸ Q) (C₁.CoordinateRing ⧸ P)) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    Ideal.inertiaDeg Q P = 1 := by
  letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
  haveI := hLies
  letI : Field (C₂.CoordinateRing ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (C₁.CoordinateRing ⧸ P) := Ideal.Quotient.field P
  haveI := hScalarTower
  rw [Ideal.inertiaDeg_algebraMap]
  -- Use the LinearEquiv to transport finrank.
  have linEq :=
    CurveMap.CoordHom.residueLinearEquiv φ coordHom hQ hP hLies hScalarTower
  rw [← linEq.finrank_eq]
  exact CommSemiring.finrank_self _

/-! ### Composition of Piece 5 + Piece 9 — atomic per-prime witness

The `h_ef_one_Q` hypothesis of Piece 8
(`primesOverFinset_card_eq_degree_of_unramified`) requires
`ramificationIdx · inertiaDeg = 1` for each prime P above Q. Over
`[IsAlgClosed F]`, this decomposes as:
* `ramificationIdx = 1` via unramification (Piece 3).
* `inertiaDeg = 1` via `inertiaDeg_eq_one_of_isAlgClosed` above
  (Piece 9).

The atomic version below does the composition at a single P. Stream A's
final assembly theorem (Deliverable 1) quantifies over the whole finset. -/

/-- **Atomic per-prime witness**: combines Piece 3's ramification output
with Piece 9's inertia output. For a single P above Q, given the
ramification-is-1 witness (Piece 3's output on P) plus the scalar-tower
witness for the residue fields (Piece 9's input under alg-closed), we
get `ramificationIdx · inertiaDeg = 1`.

Takes the ramification = 1 fact as a hypothesis rather than re-deriving
it — stream A's assembly theorem will supply it from the unramified
witness via Piece 3's `ramificationIdx_eq_one_of_isUnramifiedAt_of_ne_bot`. -/
theorem CurveMap.CoordHom.ef_one_of_ram_one_and_algClosed
    [IsAlgClosed F]
    (φ : CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    {Q : Ideal C₂.CoordinateRing} (hQ : Q.IsMaximal)
    {P : Ideal C₁.CoordinateRing} (hP : P.IsMaximal)
    (hLies :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      P.LiesOver Q)
    (hRamOne :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      Ideal.ramificationIdx Q P = 1)
    (hScalarTower :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      letI : Field (C₂.CoordinateRing ⧸ Q) := Ideal.Quotient.field Q
      letI : Field (C₁.CoordinateRing ⧸ P) := Ideal.Quotient.field P
      IsScalarTower F (C₂.CoordinateRing ⧸ Q) (C₁.CoordinateRing ⧸ P)) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    Ideal.ramificationIdx Q P *
      Ideal.inertiaDeg Q P = 1 := by
  letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
  have h_f : Ideal.inertiaDeg Q P = 1 :=
    CurveMap.CoordHom.inertiaDeg_eq_one_of_isAlgClosed φ coordHom hQ hP hLies hScalarTower
  rw [hRamOne, h_f, one_mul]

/-! ### Deliverable 1 — unconditional `exists_fiber_card_eq_sepDegree`

Assembles Pieces 1–9 into the fully unconditional form of T-II-2-009 over
`[IsAlgClosed F]`: for a separable, finite, module-torsion-free,
faithfully-scaling `CurveMap` with coordinate-ring pullback, there exists a
height-one prime `Q` in `C₂` whose entire fiber in `C₁` has cardinality
equal to `φ.separableDegree`.

Strategy:
1. Piece 1 ⇒ bad locus `{P | P ∣ differentIdeal} ⊂ HeightOneSpectrum C₁` is finite.
2. Contract via `HeightOneSpectrum.under` to a finite "bad-Q" set in C₂.
3. Piece 6 ⇒ `HeightOneSpectrum C₂` is infinite, so the complement is nonempty.
4. Pick a good Q; for each P above, combine Piece 2/3 (e = 1) + Piece 9 (f = 1).
5. Apply Piece 8. -/

/-- **Good height-one prime exists** (Pieces 1 + 6): contracting the finite
ramified locus of `C₁.CoordinateRing` via `HeightOneSpectrum.under` to a
finite subset of `HeightOneSpectrum C₂.CoordinateRing`, and using that the
latter is infinite over an algebraically closed elliptic base, there exists a
height-one prime `Q` in `C₂.CoordinateRing` lying under **no** ramified prime
of `C₁.CoordinateRing` — i.e. its whole fiber avoids `differentIdeal`. -/
private theorem CurveMap.exists_heightOneSpectrum_not_liesUnder_ramified
    [IsAlgClosed F]
    [C₂.toAffine.IsElliptic]
    [IsIntegrallyClosed C₂.CoordinateRing]
    [IsIntegrallyClosed C₁.CoordinateRing]
    (φ : Curves.CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    (hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra.toModule)
    (htorsion : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra.toModule)
    (hfaithful : @FaithfulSMul C₂.CoordinateRing C₁.CoordinateRing
      coordHom.toAlgebra.toSMul)
    (hsepFF :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      @Algebra.IsSeparable (FractionRing C₂.CoordinateRing)
        (FractionRing C₁.CoordinateRing) _ _
        (FractionRing.liftAlgebra C₂.CoordinateRing (FractionRing C₁.CoordinateRing))) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    ∃ Q : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing,
      ∀ P : IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing,
        P.asIdeal ∣ differentIdeal C₂.CoordinateRing C₁.CoordinateRing →
        P.under C₂.CoordinateRing ≠ Q := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR := hfin
  haveI htorsion' : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    htorsion
  haveI hfaithful' : @FaithfulSMul C₂.CoordinateRing C₁.CoordinateRing algCR.toSMul :=
    hfaithful
  -- Step 1: bad locus in C₁.CR is finite (Piece 1).
  have hfin_bad :
      {P : IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing |
        P.asIdeal ∣ differentIdeal C₂.CoordinateRing C₁.CoordinateRing}.Finite :=
    IsDedekindDomain.finite_ramified_primes
      (A := C₂.CoordinateRing) (B := C₁.CoordinateRing) hsepFF
  -- Step 2–3: badQ is finite, HeightOneSpectrum C₂ is infinite ⇒ good Q exists.
  have hinf_C2 : Set.Infinite
      ({P : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing | True}) :=
    C₂.heightOneSpectrum_infinite
  by_contra h
  push Not at h
  apply hinf_C2
  have hsub : ({P : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing | True} : Set _)
      ⊆ (fun P : IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing ↦ P.under C₂.CoordinateRing)
        '' {P | P.asIdeal ∣ differentIdeal C₂.CoordinateRing C₁.CoordinateRing} := by
    intro Q _
    obtain ⟨P, hPdvd, hPeq⟩ := h Q
    exact ⟨P, hPdvd, hPeq⟩
  exact (hfin_bad.image _).subset hsub

/-- **Fiber prime avoids the ramified locus** (contraction step): if a
height-one prime `Q` of `C₂.CoordinateRing` lies under no ramified prime of
`C₁.CoordinateRing` (the `hQ_good` witness), then any prime `P` of
`C₁.CoordinateRing` lying over `Q.asIdeal` does **not** divide the different
ideal. Wraps `P` as a height-one spectrum and contracts it back to `Q` via
`HeightOneSpectrum.under`. -/
private theorem CurveMap.not_dvd_differentIdeal_of_liesOver_good
    [IsIntegrallyClosed C₂.CoordinateRing]
    [IsIntegrallyClosed C₁.CoordinateRing]
    (φ : Curves.CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    (hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra.toModule)
    (htorsion : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra.toModule)
    (Q : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing)
    (hQ_good :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      ∀ P : IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing,
        P.asIdeal ∣ differentIdeal C₂.CoordinateRing C₁.CoordinateRing →
        P.under C₂.CoordinateRing ≠ Q)
    {P : Ideal C₁.CoordinateRing} (hP_prime : P.IsPrime) (hP_ne : P ≠ ⊥)
    (hP_lies :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      P.LiesOver Q.asIdeal) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    ¬ P ∣ differentIdeal C₂.CoordinateRing C₁.CoordinateRing := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR := hfin
  haveI htorsion' : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    htorsion
  haveI := hP_lies
  -- Wrap `P` as a height-one prime and show its contraction to `C₂` is `Q`.
  let P' : IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing :=
    ⟨P, hP_prime, hP_ne⟩
  have hP'_under_eq : P'.under C₂.CoordinateRing = Q := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    show P.under C₂.CoordinateRing = Q.asIdeal
    exact (Ideal.over_def P Q.asIdeal).symm
  exact fun hdvd ↦ hQ_good P' hdvd hP'_under_eq

/-- **Ramification index is `1`** (Pieces 2/3): a prime `P` of
`C₁.CoordinateRing` lying over `Q.asIdeal` that does **not** divide the
different ideal is unramified over `C₂.CoordinateRing` (Piece 2), hence has
ramification index `1` (Piece 3). The lying-over hypothesis identifies
`P.under C₂.CoordinateRing` with `Q.asIdeal`. -/
private theorem CurveMap.ramificationIdx_eq_one_of_not_dvd_differentIdeal
    [IsIntegrallyClosed C₂.CoordinateRing]
    [IsIntegrallyClosed C₁.CoordinateRing]
    (φ : Curves.CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    (hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra.toModule)
    (htorsion : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra.toModule)
    (hfaithful : @FaithfulSMul C₂.CoordinateRing C₁.CoordinateRing
      coordHom.toAlgebra.toSMul)
    (hessfin : @Algebra.EssFiniteType C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra)
    (hsepFF :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      @Algebra.IsSeparable (FractionRing C₂.CoordinateRing)
        (FractionRing C₁.CoordinateRing) _ _
        (FractionRing.liftAlgebra C₂.CoordinateRing (FractionRing C₁.CoordinateRing)))
    (Q : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing)
    {P : Ideal C₁.CoordinateRing} (hP_prime : P.IsPrime) (hP_ne : P ≠ ⊥)
    (hP_lies :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      P.LiesOver Q.asIdeal)
    (hP_nd :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      ¬ P ∣ differentIdeal C₂.CoordinateRing C₁.CoordinateRing) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    Ideal.ramificationIdx Q.asIdeal P = 1 := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ modCR := hfin
  haveI htorsion' : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _ modCR :=
    htorsion
  haveI hfaithful' : @FaithfulSMul C₂.CoordinateRing C₁.CoordinateRing algCR.toSMul :=
    hfaithful
  haveI hessfin' : @Algebra.EssFiniteType C₂.CoordinateRing C₁.CoordinateRing _ _ algCR :=
    hessfin
  haveI := hP_prime
  haveI := hP_lies
  -- Piece 2: not dividing the different ideal ⇒ unramified at `P`.
  haveI hUnram : Algebra.IsUnramifiedAt C₂.CoordinateRing P :=
    IsDedekindDomain.isUnramifiedAt_of_not_dvd_differentIdeal hsepFF hP_nd
  -- Piece 3: unramified ⇒ ramification index `1` (rewriting `P.under` to `Q`).
  have := IsDedekindDomain.ramificationIdx_eq_one_of_isUnramifiedAt_of_ne_bot
    (A := C₂.CoordinateRing) (B := C₁.CoordinateRing) (P := P) hP_ne
  rwa [← Ideal.over_def P Q.asIdeal] at this

/-- **Per-prime `e · f = 1`** (Pieces 2/3 + Piece 9): for a height-one prime
`Q` of `C₂.CoordinateRing` whose fiber avoids the ramified locus, every prime
`P` in that fiber has `ramificationIdx Q P * inertiaDeg Q P = 1`. The
ramification side `e = 1` is Pieces 2/3 (unramified at `P` ⇒ `e = 1`); the
inertia side `f = 1` is Piece 9 over the algebraically closed base. This is
exactly the witness consumed by
`exists_heightOneSpectrum_fiber_card_eq_sepDegree`. -/
private theorem CurveMap.ramificationIdx_mul_inertiaDeg_eq_one_of_not_liesUnder_ramified
    [IsAlgClosed F]
    [IsIntegrallyClosed C₂.CoordinateRing]
    [IsIntegrallyClosed C₁.CoordinateRing]
    (φ : Curves.CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    (hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra.toModule)
    (htorsion : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra.toModule)
    (hfaithful : @FaithfulSMul C₂.CoordinateRing C₁.CoordinateRing
      coordHom.toAlgebra.toSMul)
    (hessfin : @Algebra.EssFiniteType C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra)
    (hsepFF :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      @Algebra.IsSeparable (FractionRing C₂.CoordinateRing)
        (FractionRing C₁.CoordinateRing) _ _
        (FractionRing.liftAlgebra C₂.CoordinateRing (FractionRing C₁.CoordinateRing)))
    (Q : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing)
    (hQ_good :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      ∀ P : IsDedekindDomain.HeightOneSpectrum C₁.CoordinateRing,
        P.asIdeal ∣ differentIdeal C₂.CoordinateRing C₁.CoordinateRing →
        P.under C₂.CoordinateRing ≠ Q) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    ∀ P ∈ IsDedekindDomain.primesOverFinset Q.asIdeal C₁.CoordinateRing,
      Ideal.ramificationIdx Q.asIdeal P *
        Ideal.inertiaDeg Q.asIdeal P = 1 := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
  -- Scalar tower F → C₂.CR → C₁.CR from coordHom.compat (needed for Piece 9).
  haveI : IsScalarTower F C₂.CoordinateRing C₁.CoordinateRing :=
    IsScalarTower.of_algHom coordHom.toAlgHom
  haveI hQmax : Q.asIdeal.IsMaximal := Q.isPrime.isMaximal Q.ne_bot
  intro P hP_mem
  -- Unpack membership: P prime, P lies over Q.asIdeal.
  rw [IsDedekindDomain.mem_primesOverFinset_iff Q.ne_bot] at hP_mem
  obtain ⟨hP_prime, hP_lies⟩ := hP_mem
  haveI := hP_prime
  haveI := hP_lies
  have hP_ne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot Q.ne_bot P
  -- The fiber prime `P` avoids the ramified locus (contraction step).
  have hP_nd : ¬ P ∣ differentIdeal C₂.CoordinateRing C₁.CoordinateRing :=
    φ.not_dvd_differentIdeal_of_liesOver_good coordHom hfin htorsion Q hQ_good hP_prime hP_ne
      hP_lies
  -- Pieces 2 + 3 ⇒ ramificationIdx = 1.
  have hram : Ideal.ramificationIdx Q.asIdeal P = 1 :=
    φ.ramificationIdx_eq_one_of_not_dvd_differentIdeal coordHom hfin htorsion hfaithful
      hessfin hsepFF Q hP_prime hP_ne hP_lies hP_nd
  -- Piece 9 inputs: maximality, scalar tower on residue fields.
  haveI hPmax : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P Q.asIdeal
  letI : Field (C₂.CoordinateRing ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  letI : Field (C₁.CoordinateRing ⧸ P) := Ideal.Quotient.field P
  haveI : IsScalarTower F (C₂.CoordinateRing ⧸ Q.asIdeal) (C₁.CoordinateRing ⧸ P) :=
    Ideal.Quotient.isScalarTower_of_liesOver (R := F) P Q.asIdeal
  -- Apply the combined e·f = 1 witness.
  exact CurveMap.CoordHom.ef_one_of_ram_one_and_algClosed
    φ coordHom hQmax hPmax hP_lies hram ‹_›

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- **T-II-2-009 full unconditional form** (Deliverable 1):
for a separable `CurveMap` with `CoordHom` pullback over `[IsAlgClosed F]`,
there exists a height-one prime `Q` in `C₂.CoordinateRing` whose fiber
cardinality in `C₁.CoordinateRing` equals `φ.separableDegree`. -/
theorem CurveMap.exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional
    [IsAlgClosed F]
    [C₂.toAffine.IsElliptic]
    [IsIntegrallyClosed C₂.CoordinateRing]
    [IsIntegrallyClosed C₁.CoordinateRing]
    (φ : Curves.CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    (hsep : φ.IsSeparable)
    (htorsion : @Module.IsTorsionFree C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra.toModule)
    (hfaithful : @FaithfulSMul C₂.CoordinateRing C₁.CoordinateRing
      coordHom.toAlgebra.toSMul)
    (hessfin : @Algebra.EssFiniteType C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra)
    (hsepFF :
      letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
      @Algebra.IsSeparable (FractionRing C₂.CoordinateRing)
        (FractionRing C₁.CoordinateRing) _ _
        (FractionRing.liftAlgebra C₂.CoordinateRing (FractionRing C₁.CoordinateRing))) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    ∃ Q : IsDedekindDomain.HeightOneSpectrum C₂.CoordinateRing,
      (IsDedekindDomain.primesOverFinset Q.asIdeal C₁.CoordinateRing).card = φ.separableDegree := by
  -- `Module.Finite` (Pieces 1–6 input) from the coordinate-ring pullback.
  have hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra.toModule := coordHom.module_finite
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
  -- Steps 1–3 (Pieces 1 + 6): a good height-one prime `Q` exists, lying under
  -- no ramified prime of `C₁`.
  obtain ⟨Q, hQ_good⟩ :=
    φ.exists_heightOneSpectrum_not_liesUnder_ramified coordHom hfin htorsion hfaithful hsepFF
  refine ⟨Q, ?_⟩
  -- Step 4 (Piece 8): the fiber card equals the separable degree once every
  -- prime above `Q` satisfies `e · f = 1`, which Pieces 2/3 + 9 supply.
  exact φ.exists_heightOneSpectrum_fiber_card_eq_sepDegree coordHom hsep Q
    (φ.ramificationIdx_mul_inertiaDeg_eq_one_of_not_liesUnder_ramified
      coordHom hfin htorsion hfaithful hessfin hsepFF Q hQ_good)

end HasseWeil.Curves
