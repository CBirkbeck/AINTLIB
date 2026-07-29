import Mathlib.RingTheory.Extension.Presentation.Basic
import ModularCurves.ForMathlib.FinitePresentationEquiv
import ModularCurves.ForMathlib.FilteredColimitClopen

/-!
# Reflecting equivalences of finitely presented base changes

A map between finitely presented algebras that becomes an equivalence over a
filtered colimit already becomes an equivalence at a later stage. The proof
uses mathlib's finite presentations to place the two tensor-product systems in
the existing `SpreadData` framework.
-/

universe u

open TensorProduct

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}

private noncomputable def Presentation.baseChangeQuotientEquiv
    {S C : Type u} [CommRing S] [CommRing C] [Algebra S C]
    {m k : ℕ} (P : Presentation S C (Fin m) (Fin k))
    (T : Type u) [CommRing T] [Algebra S T] :
    (MvPolynomial (Fin m) T ⧸
        Ideal.span (Set.range fun q =>
          MvPolynomial.map (algebraMap S T) (P.relation q))) ≃ₐ[T]
      T ⊗[S] C :=
  (Ideal.quotientEquivAlgOfEq T
    (P.baseChange T).span_range_relation_eq_ker).trans
      ((P.baseChange T).quotientEquiv.restrictScalars T)

private theorem Presentation.baseChangeQuotientEquiv_mk
    {S C : Type u} [CommRing S] [CommRing C] [Algebra S C]
    {m k : ℕ} (P : Presentation S C (Fin m) (Fin k))
    (T : Type u) [CommRing T] [Algebra S T]
    (p : MvPolynomial (Fin m) T) :
    P.baseChangeQuotientEquiv T (Ideal.Quotient.mk _ p) =
      MvPolynomial.aeval (P.baseChange T).val p := by
  change (P.baseChange T).quotientEquiv
    (Ideal.quotientEquivAlgOfEq T
      (P.baseChange T).span_range_relation_eq_ker
      (Ideal.Quotient.mk
        (Ideal.span (Set.range (P.baseChange T).relation)) p)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, Presentation.quotientEquiv_mk,
    Generators.algebraMap_apply]

private theorem Presentation.baseChangeQuotientEquiv_mk_X
    {S C : Type u} [CommRing S] [CommRing C] [Algebra S C]
    {m k : ℕ} (P : Presentation S C (Fin m) (Fin k))
    (T : Type u) [CommRing T] [Algebra S T] (v : Fin m) :
    P.baseChangeQuotientEquiv T (Ideal.Quotient.mk _ (MvPolynomial.X v)) =
      (1 : T) ⊗ₜ[S] P.val v := by
  rw [P.baseChangeQuotientEquiv_mk, MvPolynomial.aeval_X]
  rfl

private theorem Presentation.aeval_baseChange_val
    {S C : Type u} [CommRing S] [CommRing C] [Algebra S C]
    {m k : ℕ} (P : Presentation S C (Fin m) (Fin k))
    (T : Type u) [CommRing T] [Algebra S T]
    (p : MvPolynomial (Fin m) S) :
    MvPolynomial.aeval (P.baseChange T).val p =
      (1 : T) ⊗ₜ[S] MvPolynomial.aeval P.val p := by
  induction p using MvPolynomial.induction_on with
  | C s =>
      simpa only [MvPolynomial.aeval_C, TensorProduct.algebraMap_apply] using
        (TensorProduct.tmul_one_eq_one_tmul (A := T) (B := C) s)
  | add p q hp hq => simp only [map_add, hp, hq, tmul_add]
  | mul_X p v hp =>
      simp only [map_mul, MvPolynomial.aeval_X, hp]
      change ((1 : T) ⊗ₜ[S] MvPolynomial.aeval P.val p) *
          ((1 : T) ⊗ₜ[S] P.val v) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private theorem Presentation.baseChangeQuotientEquiv_symm_tmul
    {S C : Type u} [CommRing S] [CommRing C] [Algebra S C]
    {m k : ℕ} (P : Presentation S C (Fin m) (Fin k))
    (T : Type u) [CommRing T] [Algebra S T] (c : C) :
    (P.baseChangeQuotientEquiv T).symm ((1 : T) ⊗ₜ[S] c) =
      Ideal.Quotient.mk _
        (MvPolynomial.map (algebraMap S T) (P.σ c)) := by
  apply (P.baseChangeQuotientEquiv T).injective
  rw [AlgEquiv.apply_symm_apply, P.baseChangeQuotientEquiv_mk]
  rw [MvPolynomial.aeval_map_algebraMap]
  rw [P.aeval_baseChange_val, P.aeval_val_σ]

private noncomputable def Presentation.toSpreadData
    {i : ι}
    {C : Type u} [CommRing C] [Algebra (𝒮 i) C]
    {m k : ℕ} (P : Presentation (𝒮 i) C (Fin m) (Fin k)) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    SpreadData 𝒮 uA (A ⊗[𝒮 i] C) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  exact
    { i₀ := i
      m := m
      k := k
      g := P.relation
      equiv := ⟨P.baseChangeQuotientEquiv A⟩ }

private noncomputable def Presentation.spreadStageEquiv
    {i j : ι} (hij : i ≤ j)
    {C : Type u} [CommRing C] [Algebra (𝒮 i) C]
    {m k : ℕ} (P : Presentation (𝒮 i) C (Fin m) (Fin k)) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    (P.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)).spreadStage
        (t := t) hij ≃ₐ[𝒮 j]
      𝒮 j ⊗[𝒮 i] C := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  exact P.baseChangeQuotientEquiv (𝒮 j)

private theorem Presentation.presentedU_mk_map_σ
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (hij : i ≤ j)
    {C : Type u} [CommRing C] [Algebra (𝒮 i) C]
    {m k : ℕ} (P : Presentation (𝒮 i) C (Fin m) (Fin k)) (c : C) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    presentedU t uA H P.relation ⟨j, hij⟩
        (Ideal.Quotient.mk _
          (MvPolynomial.map (t hij).toRingHom (P.σ c))) =
      (P.baseChangeQuotientEquiv A).symm ((1 : A) ⊗ₜ[𝒮 i] c) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  rw [presentedU_mk, MvPolynomial.map_map, H.u_comp,
    P.baseChangeQuotientEquiv_symm_tmul]
  simp only [RingHom.algebraMap_toAlgebra]

private theorem Presentation.spreadStageEquiv_presentedT_mk_map_σ
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (Pidx Qidx : {j : ι // i ≤ j}) (hPQ : Pidx ≤ Qidx)
    {C : Type u} [CommRing C] [Algebra (𝒮 i) C]
    {m k : ℕ} (P : Presentation (𝒮 i) C (Fin m) (Fin k)) (c : C) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 Qidx.1) := (t Qidx.2).toRingHom.toAlgebra
    P.spreadStageEquiv (A := A) (uA := uA) Qidx.2
        (presentedT t H P.relation hPQ
          (Ideal.Quotient.mk _
            (MvPolynomial.map (t Pidx.2).toRingHom (P.σ c)))) =
      (1 : 𝒮 Qidx.1) ⊗ₜ[𝒮 i] c := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 Qidx.1) := (t Qidx.2).toRingHom.toAlgebra
  change P.baseChangeQuotientEquiv (𝒮 Qidx.1)
      (presentedT t H P.relation hPQ
        (Ideal.Quotient.mk _
          (MvPolynomial.map (t Pidx.2).toRingHom (P.σ c)))) = _
  rw [presentedT_mk, MvPolynomial.map_map, H.t_comp]
  change P.baseChangeQuotientEquiv (𝒮 Qidx.1)
      (Ideal.Quotient.mk _
        (MvPolynomial.map (algebraMap (𝒮 i) (𝒮 Qidx.1)) (P.σ c))) = _
  rw [P.baseChangeQuotientEquiv_mk,
    MvPolynomial.aeval_map_algebraMap, P.aeval_baseChange_val,
    P.aeval_val_σ]

/-- A finite union of basic opens in a finitely presented algebra which becomes clopen
after base change to a filtered colimit is already clopen after base change to one later
stage. -/
theorem IsFilteredAlgColimit.exists_isClopen_iSup_basicOpen_tensorProduct
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} {C : Type u} [CommRing C] [Algebra (𝒮 i) C]
    [FinitePresentation (𝒮 i) C]
    {κ : Type u} [Finite κ] (f : κ → C)
    (hclopen :
      letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
      IsClopen
        ((↑(⨆ q, PrimeSpectrum.basicOpen
          ((1 : A) ⊗ₜ[𝒮 i] f q)) : Set (PrimeSpectrum (A ⊗[𝒮 i] C))))) :
    ∃ (j : ι) (hij : i ≤ j),
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      IsClopen
        ((↑(⨆ q, PrimeSpectrum.basicOpen
          ((1 : 𝒮 j) ⊗ₜ[𝒮 i] f q)) :
            Set (PrimeSpectrum (𝒮 j ⊗[𝒮 i] C)))) := by
  classical
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  let m := Presentation.ofFinitePresentationVars (𝒮 i) C
  let n := Presentation.ofFinitePresentationRels (𝒮 i) C
  let P : Presentation (𝒮 i) C (Fin m) (Fin n) :=
    Presentation.ofFinitePresentation (𝒮 i) C
  let Pidx : {j : ι // i ≤ j} := ⟨i, le_rfl⟩
  let fP : κ →
      MvPolynomial (Fin m) (𝒮 Pidx.1) ⧸
        Ideal.span (Set.range fun r =>
          MvPolynomial.map (t Pidx.2).toRingHom (P.relation r)) := fun q =>
    Ideal.Quotient.mk _
      (MvPolynomial.map (t Pidx.2).toRingHom (P.σ (f q)))
  have hquotient : IsClopen
      ((↑(⨆ q, PrimeSpectrum.basicOpen
        ((P.baseChangeQuotientEquiv A).symm
          ((1 : A) ⊗ₜ[𝒮 i] f q))) :
          Set (PrimeSpectrum
            (MvPolynomial (Fin m) A ⧸
              Ideal.span (Set.range fun r =>
                MvPolynomial.map (uA i).toRingHom (P.relation r)))))) :=
    PrimeSpectrum.isClopen_iSup_basicOpen_map
      (P.baseChangeQuotientEquiv A).symm.toRingHom
      (fun q => (1 : A) ⊗ₜ[𝒮 i] f q) hclopen
  have hcolimit : IsClopen
      ((↑(⨆ q, PrimeSpectrum.basicOpen
        (presentedU t uA H P.relation Pidx (fP q))) :
          Set (PrimeSpectrum
            (MvPolynomial (Fin m) A ⧸
              Ideal.span (Set.range fun r =>
                MvPolynomial.map (uA i).toRingHom (P.relation r)))))) := by
    have hgenerator (q : κ) :
        presentedU t uA H P.relation Pidx (fP q) =
          (P.baseChangeQuotientEquiv A).symm
            ((1 : A) ⊗ₜ[𝒮 i] f q) := by
      exact P.presentedU_mk_map_σ H Pidx.2 (f q)
    simpa only [hgenerator] using hquotient
  obtain ⟨Q, hPQ, hstage⟩ :=
    (isFilteredAlgColimit_presented H P.relation).exists_isClopen_iSup_basicOpen
      fP hcolimit
  refine ⟨Q.1, Q.2, ?_⟩
  letI : Algebra (𝒮 i) (𝒮 Q.1) := (t Q.2).toRingHom.toAlgebra
  have hmapped := PrimeSpectrum.isClopen_iSup_basicOpen_map
    (P.spreadStageEquiv (A := A) (uA := uA) Q.2).toRingHom
    (fun q => presentedT t H P.relation hPQ (fP q)) hstage
  have hgenerator (q : κ) :
      P.spreadStageEquiv (A := A) (uA := uA) Q.2
          (presentedT t H P.relation hPQ (fP q)) =
        (1 : 𝒮 Q.1) ⊗ₜ[𝒮 i] f q := by
    exact P.spreadStageEquiv_presentedT_mk_map_σ H Pidx Q hPQ (f q)
  change IsClopen
    ((↑(⨆ q, PrimeSpectrum.basicOpen
      (P.spreadStageEquiv (A := A) (uA := uA) Q.2
        (presentedT t H P.relation hPQ (fP q)))) :
        Set (PrimeSpectrum (𝒮 Q.1 ⊗[𝒮 i] C)))) at hmapped
  simpa only [hgenerator] using hmapped

private noncomputable def Presentation.spreadBaseChangeEquiv
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (hij : i ≤ j)
    {C : Type u} [CommRing C] [Algebra (𝒮 i) C]
    {m k : ℕ} (P : Presentation (𝒮 i) C (Fin m) (Fin k)) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    A ⊗[𝒮 j]
        (P.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)).spreadStage
          (t := t) hij ≃ₐ[A]
      A ⊗[𝒮 i] C := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  letI : IsScalarTower (𝒮 i) (𝒮 j) A :=
    IsScalarTower.of_algebraMap_eq' (H.u_comp hij).symm
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A)
    (P.spreadStageEquiv (A := A) (uA := uA) hij)).trans
      (Algebra.TensorProduct.cancelBaseChange (𝒮 i) (𝒮 j) A A C)

private def tensorProductMapOverLeft
    {S C₁ C₂ T : Type u} [CommRing S] [CommRing C₁] [CommRing C₂]
    [CommRing T] [Algebra S C₁] [Algebra S C₂] [Algebra S T]
    (f : C₁ →ₐ[S] C₂) : T ⊗[S] C₁ →ₐ[T] T ⊗[S] C₂ where
  toRingHom := (Algebra.TensorProduct.map (AlgHom.id S T) f).toRingHom
  commutes' x := by
    change Algebra.TensorProduct.map (AlgHom.id S T) f
      (x ⊗ₜ[S] (1 : C₁)) = x ⊗ₜ[S] (1 : C₂)
    rw [Algebra.TensorProduct.map_tmul]
    simp

private theorem tensorProductMapOverLeft_tmul
    {S C₁ C₂ T : Type u} [CommRing S] [CommRing C₁] [CommRing C₂]
    [CommRing T] [Algebra S C₁] [Algebra S C₂] [Algebra S T]
    (f : C₁ →ₐ[S] C₂) (x : T) (c : C₁) :
    tensorProductMapOverLeft f (x ⊗ₜ[S] c) = x ⊗ₜ[S] f c := by
  change Algebra.TensorProduct.map (AlgHom.id S T) f (x ⊗ₜ[S] c) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

private theorem tensorProductMapOverLeft_cancelBaseChange
    {S U T C₁ C₂ : Type u}
    [CommRing S] [CommRing U] [CommRing T] [CommRing C₁] [CommRing C₂]
    [Algebra S U] [Algebra S T] [Algebra U T]
    [Algebra S C₁] [Algebra S C₂] [IsScalarTower S U T]
    (f : C₁ →ₐ[S] C₂) :
    (Algebra.TensorProduct.cancelBaseChange S U T T C₂).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id T T)
          (tensorProductMapOverLeft (T := U) f)) =
      (tensorProductMapOverLeft (T := T) f).comp
        (Algebra.TensorProduct.cancelBaseChange S U T T C₁).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a x
  induction x with
  | zero => simp only [tmul_zero, map_zero]
  | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]
  | tmul s c =>
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, tensorProductMapOverLeft_tmul]
      have h₂ : Algebra.TensorProduct.cancelBaseChange S U T T C₂
          (a ⊗ₜ[U] (s ⊗ₜ[S] f c)) = (s • a) ⊗ₜ[S] f c :=
        Algebra.TensorProduct.cancelBaseChange_tmul
          (R := S) (S := U) (T := T) (A := T) (B := C₂) a s (f c)
      have h₁ : Algebra.TensorProduct.cancelBaseChange S U T T C₁
          (a ⊗ₜ[U] (s ⊗ₜ[S] c)) = (s • a) ⊗ₜ[S] c :=
        Algebra.TensorProduct.cancelBaseChange_tmul
          (R := S) (S := U) (T := T) (A := T) (B := C₁) a s c
      calc
        _ = (s • a) ⊗ₜ[S] f c := h₂
        _ = tensorProductMapOverLeft f ((s • a) ⊗ₜ[S] c) :=
          (tensorProductMapOverLeft_tmul f (s • a) c).symm
        _ = _ := congrArg (tensorProductMapOverLeft f) h₁.symm

private theorem Presentation.baseChangeTensorMap_mk_X
    {S C₁ C₂ T : Type u} [CommRing S] [CommRing C₁] [CommRing C₂]
    [CommRing T] [Algebra S C₁] [Algebra S C₂] [Algebra S T]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation S C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation S C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[S] C₂) (v : Fin m₁) :
    (P₂.baseChangeQuotientEquiv T).symm
        (tensorProductMapOverLeft f
          (P₁.baseChangeQuotientEquiv T
            (Ideal.Quotient.mk _ (MvPolynomial.X v)))) =
      Ideal.Quotient.mk _
        (MvPolynomial.map (algebraMap S T) (P₂.σ (f (P₁.val v)))) := by
  rw [P₁.baseChangeQuotientEquiv_mk_X, tensorProductMapOverLeft_tmul,
    P₂.baseChangeQuotientEquiv_symm_tmul]

private noncomputable def Presentation.spreadTensorMap
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    (P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)).spreadStage
        (t := t) hij →ₐ[𝒮 j]
      (P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)).spreadStage
        (t := t) hij := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  exact (P₂.spreadStageEquiv (A := A) (uA := uA) hij).symm.toAlgHom.comp
    ((tensorProductMapOverLeft f).comp
      (P₁.spreadStageEquiv (A := A) (uA := uA) hij).toAlgHom)

private theorem Presentation.spreadStageEquiv_spreadTensorMap
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂)
    (x : (P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)).spreadStage
      (t := t) hij) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    P₂.spreadStageEquiv (A := A) (uA := uA) hij
        (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
          hij P₂ f x) =
      tensorProductMapOverLeft f
        (P₁.spreadStageEquiv (A := A) (uA := uA) hij x) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  change P₂.spreadStageEquiv (A := A) (uA := uA) hij
      ((P₂.spreadStageEquiv (A := A) (uA := uA) hij).symm
        (tensorProductMapOverLeft f
          (P₁.spreadStageEquiv (A := A) (uA := uA) hij x))) = _
  exact (P₂.spreadStageEquiv (A := A) (uA := uA) hij).apply_symm_apply _

private theorem Presentation.spreadTensorMap_bijective_iff
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    Function.Bijective
        (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
          hij P₂ f) ↔
      Function.Bijective (tensorProductMapOverLeft (T := 𝒮 j) f) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let E₁ := P₁.spreadStageEquiv (𝒮 := 𝒮) (t := t) (A := A) (uA := uA) hij
  let E₂ := P₂.spreadStageEquiv (𝒮 := 𝒮) (t := t) (A := A) (uA := uA) hij
  let F := P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
    hij P₂ f
  let G := tensorProductMapOverLeft (T := 𝒮 j) f
  have hcomm : E₂.toAlgHom.comp F = G.comp E₁.toAlgHom := by
    ext x
    exact P₁.spreadStageEquiv_spreadTensorMap hij P₂ f x
  constructor
  · intro hF
    have hleft : Function.Bijective (E₂.toAlgHom.comp F) :=
      E₂.bijective.comp hF
    have hright : Function.Bijective (G.comp E₁.toAlgHom) := hcomm ▸ hleft
    exact (Function.Bijective.of_comp_iff G E₁.bijective).mp hright
  · intro hG
    have hright : Function.Bijective (G.comp E₁.toAlgHom) :=
      hG.comp E₁.bijective
    have hleft : Function.Bijective (E₂.toAlgHom.comp F) := hcomm.symm ▸ hright
    exact (E₂.bijective.of_comp_iff' F).mp hleft

private theorem Presentation.spreadTensorMap_surjective_iff
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    Function.Surjective
        (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
          hij P₂ f) ↔
      Function.Surjective (tensorProductMapOverLeft (T := 𝒮 j) f) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let E₁ := P₁.spreadStageEquiv (𝒮 := 𝒮) (t := t) (A := A) (uA := uA) hij
  let E₂ := P₂.spreadStageEquiv (𝒮 := 𝒮) (t := t) (A := A) (uA := uA) hij
  let F := P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
    hij P₂ f
  let G := tensorProductMapOverLeft (T := 𝒮 j) f
  have hcomm : E₂.toAlgHom.comp F = G.comp E₁.toAlgHom := by
    ext x
    exact P₁.spreadStageEquiv_spreadTensorMap hij P₂ f x
  constructor
  · intro hF
    have hleft : Function.Surjective (E₂.toAlgHom.comp F) :=
      E₂.surjective.comp hF
    have hright : Function.Surjective (G.comp E₁.toAlgHom) := hcomm ▸ hleft
    exact (Function.Surjective.of_comp_iff G E₁.surjective).mp hright
  · intro hG
    have hright : Function.Surjective (G.comp E₁.toAlgHom) :=
      hG.comp E₁.surjective
    have hleft : Function.Surjective (E₂.toAlgHom.comp F) := hcomm.symm ▸ hright
    exact (Function.Surjective.of_comp_iff' E₂.bijective F).mp hleft

private theorem Presentation.spreadBaseChangeEquiv_map
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    (P₂.spreadBaseChangeEquiv H hij).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id A A)
          (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
            hij P₂ f)) =
      (tensorProductMapOverLeft f).comp
        (P₁.spreadBaseChangeEquiv H hij).toAlgHom := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  letI : IsScalarTower (𝒮 i) (𝒮 j) A :=
    IsScalarTower.of_algebraMap_eq' (H.u_comp hij).symm
  apply Algebra.TensorProduct.ext'
  intro a x
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change Algebra.TensorProduct.cancelBaseChange (𝒮 i) (𝒮 j) A A C₂
      (a ⊗ₜ[𝒮 j]
        P₂.spreadStageEquiv (A := A) (uA := uA) hij
          (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
            hij P₂ f x)) =
    tensorProductMapOverLeft f
      (Algebra.TensorProduct.cancelBaseChange (𝒮 i) (𝒮 j) A A C₁
        (a ⊗ₜ[𝒮 j] P₁.spreadStageEquiv (A := A) (uA := uA) hij x))
  rw [P₁.spreadStageEquiv_spreadTensorMap hij P₂ f x]
  exact AlgHom.congr_fun (tensorProductMapOverLeft_cancelBaseChange f)
    (a ⊗ₜ[𝒮 j] P₁.spreadStageEquiv (A := A) (uA := uA) hij x)

private theorem Presentation.baseChange_spreadTensorMap_bijective
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂)
    (hf :
      letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
      Function.Bijective (tensorProductMapOverLeft (T := A) f)) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id A A)
        (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
          hij P₂ f)) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let E₁ := P₁.spreadBaseChangeEquiv H hij
  let E₂ := P₂.spreadBaseChangeEquiv H hij
  let F := Algebra.TensorProduct.map (AlgHom.id A A)
    (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA) hij P₂ f)
  have hcomp : Function.Bijective (E₂.toAlgHom.comp F) := by
    rw [P₁.spreadBaseChangeEquiv_map H hij P₂ f]
    exact hf.comp E₁.bijective
  exact (E₂.bijective.of_comp_iff' F).mp hcomp

private theorem Presentation.baseChange_spreadTensorMap_surjective
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂)
    (hf :
      letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
      Function.Surjective (tensorProductMapOverLeft (T := A) f)) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id A A)
        (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
          hij P₂ f)) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let E₁ := P₁.spreadBaseChangeEquiv H hij
  let E₂ := P₂.spreadBaseChangeEquiv H hij
  let F := Algebra.TensorProduct.map (AlgHom.id A A)
    (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA) hij P₂ f)
  have hcomp : Function.Surjective (E₂.toAlgHom.comp F) := by
    rw [P₁.spreadBaseChangeEquiv_map H hij P₂ f]
    exact hf.comp E₁.surjective
  exact (Function.Surjective.of_comp_iff' E₂.bijective F).mp hcomp

private noncomputable def Presentation.spreadTensorMapColimitEquiv
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂)
    (hf :
      letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
      Function.Bijective (tensorProductMapOverLeft (T := A) f)) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    A ⊗[𝒮 i] C₁ ≃ₐ[A] A ⊗[𝒮 i] C₂ := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let D₁ := P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let F := Algebra.TensorProduct.map (AlgHom.id A A)
    (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
      hij P₂ f)
  exact (D₁.baseChangeColimEquiv hij H).symm.trans
    ((AlgEquiv.ofBijective F
      (P₁.baseChange_spreadTensorMap_bijective H hij P₂ f hf)).trans
        (D₂.baseChangeColimEquiv hij H))

private theorem Presentation.spreadTensorMapColimitEquiv_compat
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂)
    (hf :
      letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
      Function.Bijective (tensorProductMapOverLeft (T := A) f))
    (x : (P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)).spreadStage
      (t := t) hij) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    let D₁ := P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
    let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
    D₂.stageToColimit H ⟨j, hij⟩
        (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
          hij P₂ f x) =
      P₁.spreadTensorMapColimitEquiv H hij P₂ f hf
        (D₁.stageToColimit H ⟨j, hij⟩ x) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let D₁ := P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let f_j := P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
    hij P₂ f
  let F := Algebra.TensorProduct.map (AlgHom.id A A) f_j
  let e := P₁.spreadTensorMapColimitEquiv H hij P₂ f hf
  calc
    D₂.stageToColimit H ⟨j, hij⟩ (f_j x) =
        D₂.baseChangeColimEquiv hij H (1 ⊗ₜ[𝒮 j] f_j x) :=
      (D₂.baseChangeColimEquiv_tmul hij H (f_j x)).symm
    _ = D₂.baseChangeColimEquiv hij H (F (1 ⊗ₜ[𝒮 j] x)) := by
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    _ = e (D₁.baseChangeColimEquiv hij H (1 ⊗ₜ[𝒮 j] x)) := by
      change D₂.baseChangeColimEquiv hij H (F (1 ⊗ₜ[𝒮 j] x)) =
        D₂.baseChangeColimEquiv hij H
          (F ((D₁.baseChangeColimEquiv hij H).symm
            (D₁.baseChangeColimEquiv hij H (1 ⊗ₜ[𝒮 j] x))))
      rw [AlgEquiv.symm_apply_apply]
    _ = e (D₁.stageToColimit H ⟨j, hij⟩ x) := by
      rw [D₁.baseChangeColimEquiv_tmul hij H x]

private noncomputable def Presentation.spreadTensorMapColimitHom
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    A ⊗[𝒮 i] C₁ →ₐ[A] A ⊗[𝒮 i] C₂ := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let D₁ := P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let f_j := P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
    hij P₂ f
  exact (D₂.baseChangeColimEquiv hij H).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id A A) f_j).comp
      (D₁.baseChangeColimEquiv hij H).symm.toAlgHom)

private theorem Presentation.spreadTensorMapColimitHom_surjective
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂)
    (hf :
      letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
      Function.Surjective (tensorProductMapOverLeft (T := A) f)) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    Function.Surjective (P₁.spreadTensorMapColimitHom H hij P₂ f) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let D₁ := P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let f_j := P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
    hij P₂ f
  have hbase : Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id A A) f_j) :=
    P₁.baseChange_spreadTensorMap_surjective H hij P₂ f hf
  exact (D₂.baseChangeColimEquiv hij H).surjective.comp
    (hbase.comp (D₁.baseChangeColimEquiv hij H).symm.surjective)

private theorem Presentation.spreadTensorMapColimitHom_compat
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂)
    (x : (P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)).spreadStage
      (t := t) hij) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    let D₁ := P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
    let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
    D₂.stageToColimit H ⟨j, hij⟩
        (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
          hij P₂ f x) =
      P₁.spreadTensorMapColimitHom H hij P₂ f
        (D₁.stageToColimit H ⟨j, hij⟩ x) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let D₁ := P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let f_j := P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
    hij P₂ f
  let F := Algebra.TensorProduct.map (AlgHom.id A A) f_j
  let e := P₁.spreadTensorMapColimitHom H hij P₂ f
  calc
    D₂.stageToColimit H ⟨j, hij⟩ (f_j x) =
        D₂.baseChangeColimEquiv hij H (1 ⊗ₜ[𝒮 j] f_j x) :=
      (D₂.baseChangeColimEquiv_tmul hij H (f_j x)).symm
    _ = D₂.baseChangeColimEquiv hij H (F (1 ⊗ₜ[𝒮 j] x)) := by
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    _ = e (D₁.baseChangeColimEquiv hij H (1 ⊗ₜ[𝒮 j] x)) := by
      change D₂.baseChangeColimEquiv hij H (F (1 ⊗ₜ[𝒮 j] x)) =
        D₂.baseChangeColimEquiv hij H
          (F ((D₁.baseChangeColimEquiv hij H).symm
            (D₁.baseChangeColimEquiv hij H (1 ⊗ₜ[𝒮 j] x))))
      rw [AlgEquiv.symm_apply_apply]
    _ = e (D₁.stageToColimit H ⟨j, hij⟩ x) := by
      rw [D₁.baseChangeColimEquiv_tmul hij H x]

private theorem SpreadData.stageTransition_mk_X
    {B : Type u} [CommRing B] [Algebra A B]
    (D : SpreadData 𝒮 uA B) (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h : D.i₀ ≤ i) (hij : i ≤ j) (v : Fin D.m) :
    D.stageTransition H
        (show (⟨i, h⟩ : {q : ι // D.i₀ ≤ q}) ≤
          ⟨j, h.trans hij⟩ from hij)
        (Ideal.Quotient.mk _ (MvPolynomial.X v)) =
      Ideal.Quotient.mk _ (MvPolynomial.X v) := by
  rw [D.stageTransition_apply, presentedT_mk, MvPolynomial.map_X]

private theorem SpreadData.stageTransition_mk_map
    {B : Type u} [CommRing B] [Algebra A B]
    (D : SpreadData 𝒮 uA B) (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h : D.i₀ ≤ i) (hij : i ≤ j)
    (p : MvPolynomial (Fin D.m) (𝒮 D.i₀)) :
    D.stageTransition H
        (show (⟨i, h⟩ : {q : ι // D.i₀ ≤ q}) ≤
          ⟨j, h.trans hij⟩ from hij)
        (Ideal.Quotient.mk _ (MvPolynomial.map (t h).toRingHom p)) =
      Ideal.Quotient.mk _
        (MvPolynomial.map (t (h.trans hij)).toRingHom p) := by
  rw [D.stageTransition_apply, presentedT_mk, MvPolynomial.map_map,
    H.t_comp]

private theorem Presentation.spreadTensorMap_mk_X
    {i j : ι} (hij : i ≤ j)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂) (v : Fin m₁) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA) hij P₂ f
        (Ideal.Quotient.mk _ (MvPolynomial.X v)) =
      (@Ideal.Quotient.mk _ _ _ (Ideal.instIsTwoSided _))
        (MvPolynomial.map (algebraMap (𝒮 i) (𝒮 j))
          (P₂.σ (f (P₁.val v)))) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  change (P₂.baseChangeQuotientEquiv (𝒮 j)).symm
      (tensorProductMapOverLeft f
        (P₁.baseChangeQuotientEquiv (𝒮 j)
          (Ideal.Quotient.mk _ (MvPolynomial.X v)))) = _
  exact P₁.baseChangeTensorMap_mk_X P₂ f v

private theorem Presentation.stageTransition_spreadTensorMap_mk_X
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂) (v : Fin m₁) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    letI : Algebra (𝒮 i) (𝒮 k) := (t (hij.trans hjk)).toRingHom.toAlgebra
    let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
    D₂.stageTransition H
        (show (⟨j, (show D₂.i₀ ≤ j from hij)⟩ :
            {q : ι // D₂.i₀ ≤ q}) ≤
          ⟨k, (show D₂.i₀ ≤ j from hij).trans hjk⟩ from hjk)
        (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
          hij P₂ f (Ideal.Quotient.mk _ (MvPolynomial.X v))) =
      P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
        (hij.trans hjk) P₂ f (Ideal.Quotient.mk _ (MvPolynomial.X v)) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 k) := (t (hij.trans hjk)).toRingHom.toAlgebra
  let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  rw [P₁.spreadTensorMap_mk_X hij P₂ f v,
    P₁.spreadTensorMap_mk_X (hij.trans hjk) P₂ f v]
  exact D₂.stageTransition_mk_map H hij hjk
    (P₂.σ (f (P₁.val v)))

private theorem SpreadData.mapAtLaterStage_apply_X
    {B₁ B₂ : Type u} [CommRing B₁] [Algebra A B₁]
    [CommRing B₂] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i) (hij : i ≤ j)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂) (v : Fin D₁.m) :
    D₁.mapAtLaterStage D₂ H h₁ h₂ hij f
        (Ideal.Quotient.mk _ (MvPolynomial.X v)) =
      D₂.stageTransition H
        (show (⟨i, h₂⟩ : {q : ι // D₂.i₀ ≤ q}) ≤
          ⟨j, h₂.trans hij⟩ from hij)
        (f (Ideal.Quotient.mk _ (MvPolynomial.X v))) := by
  rw [← D₁.stageTransition_mk_X H h₁ hij v]
  exact D₁.mapAtLaterStage_stageTransition D₂ H h₁ h₂ hij f
    (Ideal.Quotient.mk _ (MvPolynomial.X v))

private theorem SpreadData.mapAtLaterStage_eq_of_generator_transition
    {B₁ B₂ : Type u} [CommRing B₁] [Algebra A B₁]
    [CommRing B₂] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i) (hij : i ≤ j)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (g : D₁.spreadStage (t := t) (h₁.trans hij) →ₐ[𝒮 j]
      D₂.spreadStage (t := t) (h₂.trans hij))
    (hg : ∀ v : Fin D₁.m,
      D₂.stageTransition H
          (show (⟨i, h₂⟩ : {q : ι // D₂.i₀ ≤ q}) ≤
            ⟨j, h₂.trans hij⟩ from hij)
          (f (Ideal.Quotient.mk _ (MvPolynomial.X v))) =
        g (Ideal.Quotient.mk _ (MvPolynomial.X v))) :
    D₁.mapAtLaterStage D₂ H h₁ h₂ hij f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [D₁.mapAtLaterStage_apply_X D₂ H h₁ h₂ hij f v]
  exact hg v

private noncomputable def Presentation.mapAtLaterStageSpreadTensorMapProp
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂) : Prop := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 k) := (t (hij.trans hjk)).toRingHom.toAlgebra
  let D₁ := P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  exact D₁.mapAtLaterStage D₂ H hij hij hjk
      (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
        hij P₂ f) =
    P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
      (hij.trans hjk) P₂ f

private theorem Presentation.mapAtLaterStage_spreadTensorMap
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    {m₁ k₁ m₂ k₂ : ℕ}
    (P₁ : Presentation (𝒮 i) C₁ (Fin m₁) (Fin k₁))
    (P₂ : Presentation (𝒮 i) C₂ (Fin m₂) (Fin k₂))
    (f : C₁ →ₐ[𝒮 i] C₂) :
    P₁.mapAtLaterStageSpreadTensorMapProp H hij hjk P₂ f := by
  unfold Presentation.mapAtLaterStageSpreadTensorMapProp
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 k) := (t (hij.trans hjk)).toRingHom.toAlgebra
  let D₁ := P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  apply D₁.mapAtLaterStage_eq_of_generator_transition D₂ H
    hij hij hjk
    (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
      hij P₂ f)
    (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
      (hij.trans hjk) P₂ f)
  intro v
  exact P₁.stageTransition_spreadTensorMap_mk_X H hij hjk P₂ f v

/-- A map between finitely presented algebras whose scalar extension to a
filtered colimit is surjective is already surjective after a later scalar
extension in the system. -/
theorem IsFilteredAlgColimit.exists_tensorProductMap_surjective
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    [FinitePresentation (𝒮 i) C₁] [FinitePresentation (𝒮 i) C₂]
    (f : C₁ →ₐ[𝒮 i] C₂)
    (hf :
      letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
      Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 i) A) f)) :
    ∃ (j : ι) (hij : i ≤ j),
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 i) (𝒮 j)) f) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  haveI := H.directed
  obtain ⟨j, hij, _⟩ := directed_of (· ≤ ·) i i
  letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let P₁ := Presentation.ofFinitePresentation (𝒮 i) C₁
  let P₂ := Presentation.ofFinitePresentation (𝒮 i) C₂
  let D₁ := P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let f_j := P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
    hij P₂ f
  have hf' : Function.Surjective (tensorProductMapOverLeft (T := A) f) := hf
  let F := P₁.spreadTensorMapColimitHom H hij P₂ f
  have hcompat : ∀ x, D₂.stageToColimit H ⟨j, hij⟩ (f_j x) =
      F (D₁.stageToColimit H ⟨j, hij⟩ x) :=
    P₁.spreadTensorMapColimitHom_compat H hij P₂ f
  have hF : Function.Surjective F :=
    P₁.spreadTensorMapColimitHom_surjective H hij P₂ f hf'
  obtain ⟨k, hjk, hsurj⟩ :=
    D₁.exists_surjective_mapAtLaterStage D₂ H hij hij f_j F hcompat hF
  letI : Algebra (𝒮 i) (𝒮 k) :=
    (t (hij.trans hjk)).toRingHom.toAlgebra
  have hspread : Function.Surjective
      (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
        (hij.trans hjk) P₂ f) := by
    rw [← P₁.mapAtLaterStage_spreadTensorMap H hij hjk P₂ f]
    exact hsurj
  refine ⟨k, hij.trans hjk, ?_⟩
  exact (P₁.spreadTensorMap_surjective_iff
    (𝒮 := 𝒮) (t := t) (A := A) (uA := uA) (hij.trans hjk) P₂ f).mp hspread

/-- A map between finitely presented algebras whose scalar extension to a
filtered colimit is bijective is already bijective after a later scalar
extension in the system. -/
theorem IsFilteredAlgColimit.exists_tensorProductMap_bijective
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} {C₁ C₂ : Type u} [CommRing C₁] [CommRing C₂]
    [Algebra (𝒮 i) C₁] [Algebra (𝒮 i) C₂]
    [FinitePresentation (𝒮 i) C₁] [FinitePresentation (𝒮 i) C₂]
    (f : C₁ →ₐ[𝒮 i] C₂)
    (hf :
      letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
      Function.Bijective
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 i) A) f)) :
    ∃ (j : ι) (hij : i ≤ j),
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      Function.Bijective
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 i) (𝒮 j)) f) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  haveI := H.directed
  obtain ⟨j, hij, _⟩ := directed_of (· ≤ ·) i i
  letI : Algebra (𝒮 j) A := (uA j).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  let P₁ := Presentation.ofFinitePresentation (𝒮 i) C₁
  let P₂ := Presentation.ofFinitePresentation (𝒮 i) C₂
  let D₁ := P₁.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let D₂ := P₂.toSpreadData (𝒮 := 𝒮) (A := A) (uA := uA)
  let f_j := P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
    hij P₂ f
  have hf' : Function.Bijective (tensorProductMapOverLeft (T := A) f) := by
    exact hf
  let e := P₁.spreadTensorMapColimitEquiv H hij P₂ f hf'
  have hcompat : ∀ x, D₂.stageToColimit H ⟨j, hij⟩ (f_j x) =
      e (D₁.stageToColimit H ⟨j, hij⟩ x) :=
    P₁.spreadTensorMapColimitEquiv_compat H hij P₂ f hf'
  obtain ⟨k, hjk, hbij⟩ :=
    D₁.exists_mapAtLaterStage_bijective D₂ H rfl hij hij f_j e hcompat
  letI : Algebra (𝒮 i) (𝒮 k) :=
    (t (hij.trans hjk)).toRingHom.toAlgebra
  have hspread : Function.Bijective
      (P₁.spreadTensorMap (𝒮 := 𝒮) (t := t) (A := A) (uA := uA)
        (hij.trans hjk) P₂ f) := by
    rw [← P₁.mapAtLaterStage_spreadTensorMap H hij hjk P₂ f]
    exact hbij
  refine ⟨k, hij.trans hjk, ?_⟩
  exact (P₁.spreadTensorMap_bijective_iff
    (𝒮 := 𝒮) (t := t) (A := A) (uA := uA) (hij.trans hjk) P₂ f).mp hspread

end Algebra
