import ModularCurves.ForMathlib.HomologicalComplexExactRetract
import ModularCurves.ForMathlib.SheafOrderedCechAlternating

/-!
# Chain compatibility of ordered sheaf Cech alternating extension

The degreewise alternating extension from ordered to native sheaf Cech
cochains commutes with the Cech differentials. Consequently, the ordered
complex is a chain-level retract of the native complex.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
  TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

open AlgebraicGeometry.Scheme.Modules

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} [LinearOrder ι] (U : ι → Opens X)

omit [LinearOrder ι] in
private theorem cechPermutationF_eq_map (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    cechPermutationF F U n σ =
      ((FormalCoproduct.evalOp (Opens X)
        (Sheaf AddCommGrpCat.{u} X)).obj
          (cechFactorPresheaf F)).map
        (((FormalCoproduct.mk _ U).mapPower σ).op) :=
  rfl

omit [LinearOrder ι] in
private theorem cechPermutationF_comp (n : ℕ)
    (σ τ : Equiv.Perm (Fin (n + 1))) :
    cechPermutationF F U n σ ≫ cechPermutationF F U n τ =
      cechPermutationF F U n (σ.trans τ) := by
  let G := ((FormalCoproduct.evalOp (Opens X)
    (Sheaf AddCommGrpCat.{u} X)).obj (cechFactorPresheaf F))
  rw [cechPermutationF_eq_map, cechPermutationF_eq_map,
    cechPermutationF_eq_map]
  change G.map _ ≫ G.map _ = G.map _
  rw [← G.map_comp, ← op_comp]
  congr 1

omit [LinearOrder ι] in
private noncomputable def cechCofaceProductF (n : ℕ)
    (k : Fin (n + 2)) :
    (∏ᶜ cechTermFactor F U n) ⟶
      ∏ᶜ cechTermFactor F U (n + 1) :=
  Pi.lift (fun i : Fin (n + 2) → ι =>
    Pi.π (cechTermFactor F U n) (i ∘ k.succAbove) ≫
      cechTermFactorRestriction F
        (leOfHom (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i)))

omit [LinearOrder ι] in
private theorem cechCoface_eq_productF (n : ℕ) (k : Fin (n + 2)) :
    cechCoface F U n k = cechCofaceProductF F U n k :=
  rfl

omit [LinearOrder ι] in
private theorem cechCoface_eq_map (n : ℕ) (r : Fin (n + 2)) :
    cechCofaceProductF F U n r =
      ((FormalCoproduct.evalOp (Opens X)
        (Sheaf AddCommGrpCat.{u} X)).obj
          (cechFactorPresheaf F)).map
        (((FormalCoproduct.mk _ U).mapPower r.succAbove).op) :=
  rfl

omit [LinearOrder ι] in
private theorem cechCoface_comp_permutation (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    cechCofaceProductF F U n r ≫ cechPermutationF F U (n + 1) σ =
      cechPermutationF F U n (cechPermDelete σ r) ≫
        cechCofaceProductF F U n (σ r) := by
  let V := FormalCoproduct.mk _ U
  let G := ((FormalCoproduct.evalOp (Opens X)
    (Sheaf AddCommGrpCat.{u} X)).obj (cechFactorPresheaf F))
  rw [cechCoface_eq_map, cechPermutationF_eq_map,
    cechPermutationF_eq_map, cechCoface_eq_map]
  change G.map (V.mapPower r.succAbove).op ≫
      G.map (V.mapPower σ).op =
    G.map (V.mapPower (cechPermDelete σ r)).op ≫
      G.map (V.mapPower (σ r).succAbove).op
  rw [← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp]
  congr 1
  rw [← FormalCoproduct.mapPower_comp,
    ← FormalCoproduct.mapPower_comp]
  have hfun : σ ∘ r.succAbove =
      (σ r).succAbove ∘ cechPermDelete σ r := by
    funext x
    exact (succAbove_cechPermDelete σ r x).symm
  exact congrArg (fun q => q.op) (congrArg
    (fun f : Fin (n + 1) → Fin (n + 2) => V.mapPower f) hfun)

/-- Alternating extension is alternating under permutation of tuple positions. -/
theorem orderedToCechAlternatingF_comp_permutation (n : ℕ)
    (τ : Equiv.Perm (Fin (n + 1))) :
    orderedToCechAlternatingF F U n ≫ cechPermutationF F U n τ =
      (Equiv.Perm.sign τ : ℤ) • orderedToCechAlternatingF F U n := by
  rw [orderedToCechAlternatingF, sum_comp, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [zsmul_comp, Category.assoc, cechPermutationF_comp,
    Equiv.coe_mulLeft, Equiv.Perm.sign_mul, smul_smul]
  rw [show σ.trans τ = τ * σ by rfl]
  rw [Units.val_mul, ← mul_assoc, Int.units_coe_mul_self, one_mul]

omit [LinearOrder ι] in
private theorem cechProjection_comp_restriction_eq_of_eq
    (n : ℕ) (j k : Fin (n + 1) → ι) (hjk : j = k)
    {V : Opens X}
    (a : V ≤ ∏ᶜ fun x : Fin (n + 1) => U (j x))
    (b : V ≤ ∏ᶜ fun x : Fin (n + 1) => U (k x)) :
    Pi.π (cechTermFactor F U n) j ≫
        cechTermFactorRestriction F a =
      Pi.π (cechTermFactor F U n) k ≫
        cechTermFactorRestriction F b := by
  subst k
  rw [Subsingleton.elim a b]

private theorem orderedToCechAlternatingF_comp_coface_π_pair
    (n : ℕ) (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hki : i k = i l) :
    orderedToCechAlternatingF F U n ≫
        Pi.π (cechTermFactor F U n) (i ∘ k.succAbove) ≫
        cechTermFactorRestriction F
          (leOfHom (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i)) =
      (Equiv.Perm.sign (cechDeleteSwapPerm k l) : ℤ) •
        (orderedToCechAlternatingF F U n ≫
          Pi.π (cechTermFactor F U n) (i ∘ l.succAbove) ≫
          cechTermFactorRestriction F
            (leOfHom
              (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i))) := by
  let ρ := cechDeleteSwapPerm k l
  let p : (∏ᶜ cechTermFactor F U n) ⟶
      cechTermFactor F U n (i ∘ l.succAbove) :=
    Pi.π (cechTermFactor F U n) (i ∘ l.succAbove)
  let r : cechTermFactor F U n (i ∘ l.succAbove) ⟶
      cechTermFactor F U (n + 1) i :=
    cechTermFactorRestriction F
      (leOfHom (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i))
  let pk : (∏ᶜ cechTermFactor F U n) ⟶
      cechTermFactor F U n (i ∘ k.succAbove) :=
    Pi.π (cechTermFactor F U n) (i ∘ k.succAbove)
  let rk : cechTermFactor F U n (i ∘ k.succAbove) ⟶
      cechTermFactor F U (n + 1) i :=
    cechTermFactorRestriction F
      (leOfHom (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i))
  have htuple : (i ∘ l.succAbove) ∘ ρ = i ∘ k.succAbove :=
    comp_succAbove_cechDeleteSwapPerm_of_eq i k l hki
  let pρ : (∏ᶜ cechTermFactor F U n) ⟶
      cechTermFactor F U n ((i ∘ l.succAbove) ∘ ρ) :=
    Pi.π (cechTermFactor F U n) ((i ∘ l.succAbove) ∘ ρ)
  let rρ : cechTermFactor F U n ((i ∘ l.succAbove) ∘ ρ) ⟶
      cechTermFactor F U n (i ∘ l.succAbove) :=
    cechTermFactorRestriction F
      (leOfHom (((FormalCoproduct.mk _ U).mapPower ρ).φ
        (i ∘ l.succAbove)))
  have hρp : cechPermutationF F U n ρ ≫ p = pρ ≫ rρ := by
    dsimp only [p, pρ, rρ]
    exact cechPermutationF_comp_π F U n ρ (i ∘ l.succAbove)
  let a : (∏ᶜ fun x : Fin (n + 2) => U (i x)) ⟶
      ∏ᶜ fun x : Fin (n + 1) => U (((i ∘ l.succAbove) ∘ ρ) x) :=
    ((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i ≫
      ((FormalCoproduct.mk _ U).mapPower ρ).φ (i ∘ l.succAbove)
  let b : (∏ᶜ fun x : Fin (n + 2) => U (i x)) ⟶
      ∏ᶜ fun x : Fin (n + 1) => U ((i ∘ k.succAbove) x) :=
    ((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i
  have hrmaps : rρ ≫ r = cechTermFactorRestriction F (leOfHom a) := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
    rw [← F.obj.map_comp]
    exact congrArg F.obj.map (Subsingleton.elim _ _)
  have hproj :
      pρ ≫ cechTermFactorRestriction F (leOfHom a) =
        pk ≫ cechTermFactorRestriction F (leOfHom b) := by
    dsimp only [pρ, pk]
    exact cechProjection_comp_restriction_eq_of_eq F U n
      ((i ∘ l.succAbove) ∘ ρ) (i ∘ k.succAbove) htuple
      (leOfHom a) (leOfHom b)
  have hrest : (pρ ≫ rρ) ≫ r = pk ≫ rk := by
    calc
      (pρ ≫ rρ) ≫ r = pρ ≫ (rρ ≫ r) := Category.assoc _ _ _
      _ = pρ ≫ cechTermFactorRestriction F (leOfHom a) := by rw [hrmaps]
      _ = pk ≫ cechTermFactorRestriction F (leOfHom b) := hproj
      _ = pk ≫ rk := by rfl
  have hface : cechPermutationF F U n ρ ≫ p ≫ r = pk ≫ rk := by
    calc
      cechPermutationF F U n ρ ≫ p ≫ r = (pρ ≫ rρ) ≫ r := by
        exact congrArg (fun f => f ≫ r) hρp
      _ = pk ≫ rk := hrest
  have hperm := orderedToCechAlternatingF_comp_permutation F U n ρ
  change orderedToCechAlternatingF F U n ≫ pk ≫ rk =
    (Equiv.Perm.sign ρ : ℤ) •
      (orderedToCechAlternatingF F U n ≫ p ≫ r)
  calc
    orderedToCechAlternatingF F U n ≫ pk ≫ rk =
        orderedToCechAlternatingF F U n ≫
          ((cechPermutationF F U n ρ ≫ p) ≫ r) := by
      simp only [Category.assoc]
      rw [hface]
    _ = (orderedToCechAlternatingF F U n ≫ cechPermutationF F U n ρ) ≫
        (p ≫ r) := by
      simp only [Category.assoc]
    _ = ((Equiv.Perm.sign ρ : ℤ) •
        orderedToCechAlternatingF F U n) ≫ (p ≫ r) := by
      rw [hperm]
    _ = (Equiv.Perm.sign ρ : ℤ) •
        (orderedToCechAlternatingF F U n ≫ p ≫ r) := by
      rw [zsmul_comp]

private theorem orderedToCechAlternatingF_comp_coface_π_pair_cancel
    (n : ℕ) (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hki : i k = i l) (hkl : k ≠ l) :
    (-1 : ℤ) ^ (k : ℕ) •
        (orderedToCechAlternatingF F U n ≫
          Pi.π (cechTermFactor F U n) (i ∘ k.succAbove) ≫
          cechTermFactorRestriction F
            (leOfHom
              (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i))) +
      (-1 : ℤ) ^ (l : ℕ) •
        (orderedToCechAlternatingF F U n ≫
          Pi.π (cechTermFactor F U n) (i ∘ l.succAbove) ≫
          cechTermFactorRestriction F
            (leOfHom
              (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i))) = 0 := by
  let t := orderedToCechAlternatingF F U n ≫
    Pi.π (cechTermFactor F U n) (i ∘ l.succAbove) ≫
    cechTermFactorRestriction F
      (leOfHom (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i))
  have hpair := orderedToCechAlternatingF_comp_coface_π_pair
    F U n i k l hki
  change (-1 : ℤ) ^ (k : ℕ) • _ + (-1 : ℤ) ^ (l : ℕ) • t = 0
  rw [hpair, smul_smul, cechDeleteSwapPerm_sign k l hkl]
  have hcoef :
      (-1 : ℤ) ^ (k : ℕ) *
          -((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (l : ℕ)) =
        -((-1 : ℤ) ^ (l : ℕ)) := by
    rw [mul_neg, ← mul_assoc, ← pow_add,
      (Even.add_self (k : ℕ)).neg_one_pow, one_mul]
  rw [hcoef, neg_smul, neg_add_cancel]

/-- An alternating extension vanishes on every noninjective tuple component. -/
theorem orderedToCechAlternatingF_comp_π_of_not_injective
    (n : ℕ) (i : Fin (n + 1) → ι) (hi : ¬ Function.Injective i) :
    orderedToCechAlternatingF F U n ≫
        Pi.π (cechTermFactor F U n) i = 0 := by
  let e : cechTerm F U n ⟶ cechTermFactor F U n i :=
    Pi.π (cechTermFactor F U n) i
  change orderedToCechAlternatingF F U n ≫ e = 0
  rw [orderedToCechAlternatingF, sum_comp]
  apply Finset.sum_eq_zero
  intro σ _
  rw [zsmul_comp, Category.assoc, cechPermutationF_comp_π]
  let p : cechTerm F U n ⟶ cechTermFactor F U n (i ∘ σ) :=
    Pi.π (cechTermFactor F U n) (i ∘ σ)
  let r : cechTermFactor F U n (i ∘ σ) ⟶ cechTermFactor F U n i :=
    cechTermFactorRestriction F
      (leOfHom (((FormalCoproduct.mk _ U).mapPower σ).φ i))
  change (Equiv.Perm.sign σ : ℤ) •
    (orderedToCechZeroExtensionF F U n ≫ p ≫ r) = 0
  have hmono : ¬ StrictMono (i ∘ σ) := by
    intro h
    apply hi
    intro a b hab
    apply σ.symm.injective
    apply h.injective
    simpa using hab
  have hz : orderedToCechZeroExtensionF F U n ≫ p = 0 := by
    dsimp only [p]
    exact orderedToCechZeroExtensionF_comp_π_of_not_strictMono
      F U n (i ∘ σ) hmono
  have hpost :
      orderedToCechZeroExtensionF F U n ≫ (p ≫ r) = 0 := by
    calc
      orderedToCechZeroExtensionF F U n ≫ (p ≫ r) =
          (orderedToCechZeroExtensionF F U n ≫ p) ≫ r :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [hz, zero_comp]
  rw [hpost, smul_zero]

private theorem orderedToCechAlternatingF_comp_π_of_strictMono
    (n : ℕ) (i : Fin (n + 1) → ι) (hi : StrictMono i) :
    orderedToCechAlternatingF F U n ≫
        Pi.π (cechTermFactor F U n) i =
      Pi.π (orderedCechTermFactor F U n) ⟨i, hi⟩ := by
  let p : (∏ᶜ cechTermFactor F U n) ⟶ cechTermFactor F U n i :=
    Pi.π (cechTermFactor F U n) i
  let q : (∏ᶜ orderedCechTermFactor F U n) ⟶ cechTermFactor F U n i :=
    Pi.π (orderedCechTermFactor F U n) ⟨i, hi⟩
  have hp : cechToOrderedF F U n ≫ q = p := by
    dsimp only [p, q]
    exact cechToOrderedF_comp_π F U n ⟨i, hi⟩
  change orderedToCechAlternatingF F U n ≫ p = q
  calc
    orderedToCechAlternatingF F U n ≫ p =
        orderedToCechAlternatingF F U n ≫ (cechToOrderedF F U n ≫ q) :=
      congrArg (orderedToCechAlternatingF F U n ≫ ·) hp.symm
    _ = (orderedToCechAlternatingF F U n ≫ cechToOrderedF F U n) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = q := by
      have hret :=
        orderedToCechAlternatingF_comp_cechToOrderedF F U n
      change orderedToCechAlternatingF F U n ≫
        cechToOrderedF F U n =
          𝟙 (∏ᶜ orderedCechTermFactor F U n) at hret
      rw [hret]
      exact Category.id_comp q

private theorem orderedToCechAlternatingF_comp_π_of_injective
    (n : ℕ) (i : Fin (n + 1) → ι) (hi : Function.Injective i) :
    orderedToCechAlternatingF F U n ≫
        Pi.π (cechTermFactor F U n) i =
      (Equiv.Perm.sign (Tuple.sort i) : ℤ) •
        (Pi.π (orderedCechTermFactor F U n)
            ⟨i ∘ Tuple.sort i,
              (Tuple.monotone_sort i).strictMono_of_injective
                (hi.comp (Tuple.sort i).injective)⟩ ≫
          cechTermFactorRestriction F
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (Tuple.sort i)).φ i))) := by
  let s := Tuple.sort i
  have hs : StrictMono (i ∘ s) :=
    (Tuple.monotone_sort i).strictMono_of_injective
      (hi.comp s.injective)
  let p : (∏ᶜ cechTermFactor F U n) ⟶ cechTermFactor F U n i :=
    Pi.π (cechTermFactor F U n) i
  let q : (∏ᶜ orderedCechTermFactor F U n) ⟶
      cechTermFactor F U n (i ∘ s) :=
    Pi.π (orderedCechTermFactor F U n) ⟨i ∘ s, hs⟩
  let r : cechTermFactor F U n (i ∘ s) ⟶ cechTermFactor F U n i :=
    cechTermFactorRestriction F
      (leOfHom (((FormalCoproduct.mk _ U).mapPower s).φ i))
  change orderedToCechAlternatingF F U n ≫ p =
    (Equiv.Perm.sign s : ℤ) • (q ≫ r)
  rw [orderedToCechAlternatingF, sum_comp]
  rw [Finset.sum_eq_single s]
  · rw [zsmul_comp, Category.assoc, cechPermutationF_comp_π]
    let ps : (∏ᶜ cechTermFactor F U n) ⟶
        cechTermFactor F U n (i ∘ s) :=
      Pi.π (cechTermFactor F U n) (i ∘ s)
    have hz : orderedToCechZeroExtensionF F U n ≫ ps = q := by
      dsimp only [ps, q]
      exact orderedToCechZeroExtensionF_comp_π_of_strictMono
        F U n (i ∘ s) hs
    change (Equiv.Perm.sign s : ℤ) •
      (orderedToCechZeroExtensionF F U n ≫ (ps ≫ r)) =
        (Equiv.Perm.sign s : ℤ) • (q ≫ r)
    have hpost :
        orderedToCechZeroExtensionF F U n ≫ (ps ≫ r) = q ≫ r := by
      calc
        orderedToCechZeroExtensionF F U n ≫ (ps ≫ r) =
            (orderedToCechZeroExtensionF F U n ≫ ps) ≫ r :=
          (Category.assoc _ _ _).symm
        _ = q ≫ r := congrArg (· ≫ r) hz
    exact congrArg ((Equiv.Perm.sign s : ℤ) • ·) hpost
  · intro σ _ hne
    rw [zsmul_comp, Category.assoc, cechPermutationF_comp_π]
    have hmono : ¬ StrictMono (i ∘ σ) := by
      intro h
      apply hne
      apply Equiv.ext
      intro x
      apply hi
      exact congrFun
        (Tuple.comp_sort_eq_comp_iff_monotone.mpr h.monotone) x
    have hz := orderedToCechZeroExtensionF_comp_π_of_not_strictMono
      F U n (i ∘ σ) hmono
    let rσ : cechTermFactor F U n (i ∘ σ) ⟶ cechTermFactor F U n i :=
      cechTermFactorRestriction F
        (leOfHom (((FormalCoproduct.mk _ U).mapPower σ).φ i))
    let pσ : (∏ᶜ cechTermFactor F U n) ⟶
        cechTermFactor F U n (i ∘ σ) :=
      Pi.π (cechTermFactor F U n) (i ∘ σ)
    change (Equiv.Perm.sign σ : ℤ) •
      (orderedToCechZeroExtensionF F U n ≫ (pσ ≫ rσ)) = 0
    have hpost :
        orderedToCechZeroExtensionF F U n ≫ (pσ ≫ rσ) = 0 := by
      calc
        orderedToCechZeroExtensionF F U n ≫ (pσ ≫ rσ) =
            (orderedToCechZeroExtensionF F U n ≫ pσ) ≫ rσ :=
          (Category.assoc _ _ _).symm
        _ = 0 := by
          dsimp only [pσ]
          rw [hz, zero_comp]
    rw [hpost, smul_zero]
  · simp

omit [LinearOrder ι] in
private theorem cechCoface_comp_π (n : ℕ) (k : Fin (n + 2))
    (i : Fin (n + 2) → ι) :
    cechCofaceProductF F U n k ≫
        Pi.π (cechTermFactor F U (n + 1)) i =
      Pi.π (cechTermFactor F U n) (i ∘ k.succAbove) ≫
        cechTermFactorRestriction F
          (leOfHom (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i)) := by
  unfold cechCofaceProductF
  change
    Pi.lift (fun j : Fin (n + 2) → ι =>
      Pi.π (cechTermFactor F U n) (j ∘ k.succAbove) ≫
        cechTermFactorRestriction F
          (leOfHom (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ j))) ≫
      Pi.π (cechTermFactor F U (n + 1)) i = _
  exact Pi.lift_π _ i

private noncomputable def cechDifferentialProductF (n : ℕ) :
    (∏ᶜ cechTermFactor F U n) ⟶
      ∏ᶜ cechTermFactor F U (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    cechCofaceProductF F U n k

omit [LinearOrder ι] in
private theorem cechDifferential_eq_productF (n : ℕ) :
    cechDifferential F U n = cechDifferentialProductF F U n :=
  rfl

omit [LinearOrder ι] in
private theorem cechDifferential_comp_π (n : ℕ)
    (i : Fin (n + 2) → ι) :
    cechDifferentialProductF F U n ≫
        Pi.π (cechTermFactor F U (n + 1)) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (Pi.π (cechTermFactor F U n) (i ∘ k.succAbove) ≫
          cechTermFactorRestriction F
            (leOfHom
              (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i))) := by
  unfold cechDifferentialProductF
  rw [sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [zsmul_comp]
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
    (cechCoface_comp_π F U n k i)

private theorem orderedToCechAlternatingF_comp_d_comp_permutation
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    orderedToCechAlternatingF F U n ≫ cechDifferentialProductF F U n ≫
        cechPermutationF F U (n + 1) σ =
      (Equiv.Perm.sign σ : ℤ) •
        (orderedToCechAlternatingF F U n ≫
          cechDifferentialProductF F U n) := by
  unfold cechDifferentialProductF
  simp only [comp_sum, sum_comp, comp_zsmul, zsmul_comp,
    Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv σ _ _ fun r => ?_
  rw [cechCoface_comp_permutation]
  rw [← Category.assoc, orderedToCechAlternatingF_comp_permutation]
  simp only [zsmul_comp, smul_smul]
  rw [cechPermDelete_signed_coefficient]

end TopCat.Sheaf
