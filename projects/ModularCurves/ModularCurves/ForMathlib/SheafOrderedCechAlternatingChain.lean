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

private theorem orderedToCechAlternatingF_comp_d_comp_π_of_not_injective
    (n : ℕ) (i : Fin (n + 2) → ι) (hi : ¬ Function.Injective i) :
    orderedToCechAlternatingF F U n ≫ cechDifferentialProductF F U n ≫
        Pi.π (cechTermFactor F U (n + 1)) i = 0 := by
  let p : (∏ᶜ cechTermFactor F U (n + 1)) ⟶
      cechTermFactor F U (n + 1) i :=
    Pi.π (cechTermFactor F U (n + 1)) i
  change orderedToCechAlternatingF F U n ≫
    (cechDifferentialProductF F U n ≫ p) = 0
  let G : Fin (n + 2) →
      ((∏ᶜ cechTermFactor F U n) ⟶ cechTermFactor F U (n + 1) i) :=
    fun k => (-1 : ℤ) ^ (k : ℕ) •
      (Pi.π (cechTermFactor F U n) (i ∘ k.succAbove) ≫
        cechTermFactorRestriction F
          (leOfHom
            (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i)))
  let T : Fin (n + 2) →
      ((∏ᶜ orderedCechTermFactor F U n) ⟶
        cechTermFactor F U (n + 1) i) :=
    fun k => (-1 : ℤ) ^ (k : ℕ) •
      (orderedToCechAlternatingF F U n ≫
        Pi.π (cechTermFactor F U n) (i ∘ k.succAbove) ≫
        cechTermFactorRestriction F
          (leOfHom
            (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i)))
  have hd : cechDifferentialProductF F U n ≫ p = ∑ k, G k := by
    dsimp only [p, G]
    exact cechDifferential_comp_π F U n i
  have hcomp :
      orderedToCechAlternatingF F U n ≫ (∑ k, G k) =
        ∑ k, orderedToCechAlternatingF F U n ≫ G k := by
    simpa using comp_sum (Finset.univ : Finset (Fin (n + 2)))
      (orderedToCechAlternatingF F U n) G
  have hterms :
      (∑ k, orderedToCechAlternatingF F U n ≫ G k) =
        ∑ k, T k := by
    apply Finset.sum_congr rfl
    intro k _
    let q : (∏ᶜ cechTermFactor F U n) ⟶
        cechTermFactor F U (n + 1) i :=
      Pi.π (cechTermFactor F U n) (i ∘ k.succAbove) ≫
        cechTermFactorRestriction F
          (leOfHom
            (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i))
    change orderedToCechAlternatingF F U n ≫
      ((-1 : ℤ) ^ (k : ℕ) • q) =
        (-1 : ℤ) ^ (k : ℕ) •
          (orderedToCechAlternatingF F U n ≫ q)
    exact comp_zsmul _ _ ((-1 : ℤ) ^ (k : ℕ))
  rw [hd, hcomp, hterms]
  by_cases hall : ∀ k : Fin (n + 2),
      ¬ Function.Injective (i ∘ k.succAbove)
  · apply Finset.sum_eq_zero
    intro k _
    let q : (∏ᶜ orderedCechTermFactor F U n) ⟶
        cechTermFactor F U n (i ∘ k.succAbove) :=
      orderedToCechAlternatingF F U n ≫
        Pi.π (cechTermFactor F U n) (i ∘ k.succAbove)
    let r : cechTermFactor F U n (i ∘ k.succAbove) ⟶
        cechTermFactor F U (n + 1) i :=
      cechTermFactorRestriction F
        (leOfHom
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i))
    have hk := orderedToCechAlternatingF_comp_π_of_not_injective
      F U n (i ∘ k.succAbove) (hall k)
    change (-1 : ℤ) ^ (k : ℕ) • (q ≫ r) = 0
    change q = 0 at hk
    rw [hk, zero_comp, smul_zero]
  · have hex : ∃ k : Fin (n + 2),
        Function.Injective (i ∘ k.succAbove) := by
      by_contra h
      apply hall
      intro k hk
      exact h ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hex
    obtain ⟨l, hlk, hil⟩ :=
      exists_partner_of_delete_injective i hi k hk
    have hkl : k ≠ l := hlk.symm
    have hother (m : Fin (n + 2)) (hmk : m ≠ k) (hml : m ≠ l) :
        T m = 0 := by
      let q : (∏ᶜ orderedCechTermFactor F U n) ⟶
          cechTermFactor F U n (i ∘ m.succAbove) :=
        orderedToCechAlternatingF F U n ≫
          Pi.π (cechTermFactor F U n) (i ∘ m.succAbove)
      let r : cechTermFactor F U n (i ∘ m.succAbove) ⟶
          cechTermFactor F U (n + 1) i :=
        cechTermFactorRestriction F
          (leOfHom
            (((FormalCoproduct.mk _ U).mapPower m.succAbove).φ i))
      have hm := delete_not_injective_of_ne
        i k l m hkl hmk.symm hml.symm hil
      have hz := orderedToCechAlternatingF_comp_π_of_not_injective
        F U n (i ∘ m.succAbove) hm
      change (-1 : ℤ) ^ (m : ℕ) • (q ≫ r) = 0
      change q = 0 at hz
      rw [hz, zero_comp, smul_zero]
    have hrem : ((Finset.univ.erase l).erase k).sum T = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hmk : m ≠ k := (Finset.mem_erase.mp hm).1
      have hml : m ≠ l :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
      exact hother m hmk hml
    have hk_mem : k ∈ Finset.univ.erase l :=
      Finset.mem_erase.mpr ⟨hkl, Finset.mem_univ k⟩
    calc
      ∑ m, T m = (Finset.univ.erase l).sum T + T l :=
        (Finset.sum_erase_add Finset.univ T (Finset.mem_univ l)).symm
      _ = (((Finset.univ.erase l).erase k).sum T + T k) + T l := by
        rw [Finset.sum_erase_add (Finset.univ.erase l) T hk_mem]
      _ = T k + T l := by rw [hrem, zero_add]
      _ = 0 := by
        dsimp only [T]
        exact orderedToCechAlternatingF_comp_coface_π_pair_cancel
          F U n i k l hil.symm hkl

private noncomputable def orderedCechCofaceProductF (n : ℕ)
    (k : Fin (n + 2)) :
    (∏ᶜ orderedCechTermFactor F U n) ⟶
      ∏ᶜ orderedCechTermFactor F U (n + 1) :=
  Pi.lift (fun i : OrderedCechIndex ι (n + 1) =>
    Pi.π (orderedCechTermFactor F U n) (i.delete k) ≫
      cechTermFactorRestriction F
        (leOfHom (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i.1)))

private theorem orderedCechCoface_eq_productF (n : ℕ)
    (k : Fin (n + 2)) :
    orderedCechCoface F U n k = orderedCechCofaceProductF F U n k :=
  rfl

private noncomputable def orderedCechDifferentialProductF (n : ℕ) :
    (∏ᶜ orderedCechTermFactor F U n) ⟶
      ∏ᶜ orderedCechTermFactor F U (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    orderedCechCofaceProductF F U n k

private theorem orderedCechDifferential_eq_productF (n : ℕ) :
    orderedCechDifferential F U n =
      orderedCechDifferentialProductF F U n :=
  rfl

private theorem cechDifferentialProductF_comp_cechToOrderedF (n : ℕ) :
    cechDifferentialProductF F U n ≫
        (cechToOrderedF F U (n + 1) :
          (∏ᶜ cechTermFactor F U (n + 1)) ⟶
            ∏ᶜ orderedCechTermFactor F U (n + 1)) =
      (cechToOrderedF F U n :
          (∏ᶜ cechTermFactor F U n) ⟶
            ∏ᶜ orderedCechTermFactor F U n) ≫
        orderedCechDifferentialProductF F U n := by
  have h := cechToOrderedF_comp_d F U n
  change cechDifferentialProductF F U n ≫ cechToOrderedF F U (n + 1) =
    cechToOrderedF F U n ≫ orderedCechDifferentialProductF F U n at h
  exact h

private theorem orderedToCechAlternatingF_comp_d_comp_π_of_strictMono
    (n : ℕ) (i : Fin (n + 2) → ι) (hi : StrictMono i) :
    orderedToCechAlternatingF F U n ≫ cechDifferentialProductF F U n ≫
        Pi.π (cechTermFactor F U (n + 1)) i =
      orderedCechDifferentialProductF F U n ≫
        orderedToCechAlternatingF F U (n + 1) ≫
          Pi.π (cechTermFactor F U (n + 1)) i := by
  let p : (∏ᶜ cechTermFactor F U (n + 1)) ⟶
      cechTermFactor F U (n + 1) i :=
    Pi.π (cechTermFactor F U (n + 1)) i
  let q : (∏ᶜ orderedCechTermFactor F U (n + 1)) ⟶
      cechTermFactor F U (n + 1) i :=
    Pi.π (orderedCechTermFactor F U (n + 1)) ⟨i, hi⟩
  let Cn : (∏ᶜ cechTermFactor F U n) ⟶
      ∏ᶜ orderedCechTermFactor F U n :=
    cechToOrderedF F U n
  let Csucc : (∏ᶜ cechTermFactor F U (n + 1)) ⟶
      ∏ᶜ orderedCechTermFactor F U (n + 1) :=
    cechToOrderedF F U (n + 1)
  have hp : Csucc ≫ q = p := by
    dsimp only [Csucc]
    dsimp only [p, q]
    exact cechToOrderedF_comp_π F U (n + 1) ⟨i, hi⟩
  have ha : orderedToCechAlternatingF F U (n + 1) ≫ p = q := by
    dsimp only [p, q]
    exact orderedToCechAlternatingF_comp_π_of_strictMono
      F U (n + 1) i hi
  have hdc : cechDifferentialProductF F U n ≫ Csucc =
      Cn ≫ orderedCechDifferentialProductF F U n := by
    dsimp only [Cn, Csucc]
    exact cechDifferentialProductF_comp_cechToOrderedF F U n
  change orderedToCechAlternatingF F U n ≫
      cechDifferentialProductF F U n ≫ p =
    orderedCechDifferentialProductF F U n ≫
      orderedToCechAlternatingF F U (n + 1) ≫ p
  calc
    orderedToCechAlternatingF F U n ≫
        cechDifferentialProductF F U n ≫ p =
      orderedToCechAlternatingF F U n ≫
        (cechDifferentialProductF F U n ≫
          Csucc) ≫ q := by
        rw [Category.assoc, hp]
    _ = orderedToCechAlternatingF F U n ≫
        (Cn ≫
          orderedCechDifferentialProductF F U n) ≫ q := by
      exact congrArg
        (fun t => orderedToCechAlternatingF F U n ≫ t ≫ q) hdc
    _ = (orderedToCechAlternatingF F U n ≫
          Cn) ≫
        orderedCechDifferentialProductF F U n ≫ q := by
      simp only [Category.assoc]
    _ = orderedCechDifferentialProductF F U n ≫ q := by
      have hret : orderedToCechAlternatingF F U n ≫ Cn =
          𝟙 (∏ᶜ orderedCechTermFactor F U n) := by
        dsimp only [Cn]
        have h :=
          orderedToCechAlternatingF_comp_cechToOrderedF F U n
        change orderedToCechAlternatingF F U n ≫
          cechToOrderedF F U n =
            𝟙 (∏ᶜ orderedCechTermFactor F U n) at h
        exact h
      rw [hret]
      exact Category.id_comp
        (orderedCechDifferentialProductF F U n ≫ q)
    _ = orderedCechDifferentialProductF F U n ≫
        orderedToCechAlternatingF F U (n + 1) ≫ p := by
      rw [ha]

private theorem orderedToCechAlternatingF_comp_d_comp_π_of_injective
    (n : ℕ) (i : Fin (n + 2) → ι) (hi : Function.Injective i) :
    orderedToCechAlternatingF F U n ≫ cechDifferentialProductF F U n ≫
        Pi.π (cechTermFactor F U (n + 1)) i =
      orderedCechDifferentialProductF F U n ≫
        orderedToCechAlternatingF F U (n + 1) ≫
          Pi.π (cechTermFactor F U (n + 1)) i := by
  let σ := Tuple.sort i
  let j := i ∘ σ
  have hj : StrictMono j :=
    (Tuple.monotone_sort i).strictMono_of_injective
      (hi.comp σ.injective)
  let A : (∏ᶜ orderedCechTermFactor F U n) ⟶
      ∏ᶜ cechTermFactor F U (n + 1) :=
    orderedToCechAlternatingF F U n ≫ cechDifferentialProductF F U n
  let B := orderedToCechAlternatingF F U (n + 1)
  let D := orderedCechDifferentialProductF F U n
  let P := cechPermutationF F U (n + 1) σ
  let p : (∏ᶜ cechTermFactor F U (n + 1)) ⟶
      cechTermFactor F U (n + 1) i :=
    Pi.π (cechTermFactor F U (n + 1)) i
  let pj : (∏ᶜ cechTermFactor F U (n + 1)) ⟶
      cechTermFactor F U (n + 1) j :=
    Pi.π (cechTermFactor F U (n + 1)) j
  let q : (∏ᶜ orderedCechTermFactor F U (n + 1)) ⟶
      cechTermFactor F U (n + 1) j :=
    Pi.π (orderedCechTermFactor F U (n + 1)) ⟨j, hj⟩
  let r : cechTermFactor F U (n + 1) j ⟶
      cechTermFactor F U (n + 1) i :=
    cechTermFactorRestriction F
      (leOfHom (((FormalCoproduct.mk _ U).mapPower σ).φ i))
  let s : ℤ := Equiv.Perm.sign σ
  have hPp : P ≫ p = pj ≫ r := by
    dsimp only [P, p, pj, r, j]
    exact cechPermutationF_comp_π F U (n + 1) σ i
  have hAperm :=
    orderedToCechAlternatingF_comp_d_comp_permutation F U n σ
  change A ≫ P = s • A at hAperm
  have hrel : A ≫ pj ≫ r = s • (A ≫ p) := by
    calc
      A ≫ pj ≫ r = A ≫ (P ≫ p) := by rw [hPp]
      _ = (A ≫ P) ≫ p := by simp only [Category.assoc]
      _ = (s • A) ≫ p := by rw [hAperm]
      _ = s • (A ≫ p) := by rw [zsmul_comp]
  have hs : s * s = 1 := by
    dsimp only [s]
    exact Int.units_coe_mul_self (Equiv.Perm.sign σ)
  have hrel' : A ≫ p = s • (A ≫ pj ≫ r) := by
    calc
      A ≫ p = s • (s • (A ≫ p)) := by
        rw [smul_smul, hs, one_smul]
      _ = s • (A ≫ pj ≫ r) := congrArg (s • ·) hrel.symm
  have hstrict :=
    orderedToCechAlternatingF_comp_d_comp_π_of_strictMono
      F U n j hj
  change A ≫ pj = D ≫ B ≫ pj at hstrict
  have hBj := orderedToCechAlternatingF_comp_π_of_strictMono
    F U (n + 1) j hj
  change B ≫ pj = q at hBj
  have hBi := orderedToCechAlternatingF_comp_π_of_injective
    F U (n + 1) i hi
  change B ≫ p = s • (q ≫ r) at hBi
  have hstrict_r : (A ≫ pj) ≫ r = (D ≫ B ≫ pj) ≫ r :=
    congrArg (fun f => f ≫ r) hstrict
  have hDj : D ≫ B ≫ pj = D ≫ q :=
    congrArg (D ≫ ·) hBj
  have hDj_r : (D ≫ B ≫ pj) ≫ r = (D ≫ q) ≫ r :=
    congrArg (fun f => f ≫ r) hDj
  change A ≫ p = D ≫ B ≫ p
  calc
    A ≫ p = s • (A ≫ pj ≫ r) := hrel'
    _ = s • ((D ≫ B ≫ pj) ≫ r) := congrArg (s • ·) hstrict_r
    _ = s • ((D ≫ q) ≫ r) := congrArg (s • ·) hDj_r
    _ = D ≫ (s • (q ≫ r)) := by
      calc
        s • ((D ≫ q) ≫ r) = s • (D ≫ (q ≫ r)) :=
          congrArg (s • ·) (Category.assoc D q r)
        _ = D ≫ (s • (q ≫ r)) :=
          (comp_zsmul D (q ≫ r) s).symm
    _ = D ≫ (B ≫ p) := by rw [hBi]
    _ = D ≫ B ≫ p := by rfl

private theorem orderedToCechAlternatingF_comp_product_d (n : ℕ) :
    orderedToCechAlternatingF F U n ≫ cechDifferentialProductF F U n =
      orderedCechDifferentialProductF F U n ≫
        orderedToCechAlternatingF F U (n + 1) := by
  apply Pi.hom_ext
  intro i
  let p : (∏ᶜ cechTermFactor F U (n + 1)) ⟶
      cechTermFactor F U (n + 1) i :=
    Pi.π (cechTermFactor F U (n + 1)) i
  change (orderedToCechAlternatingF F U n ≫
      cechDifferentialProductF F U n) ≫ p =
    (orderedCechDifferentialProductF F U n ≫
      orderedToCechAlternatingF F U (n + 1)) ≫ p
  by_cases hi : Function.Injective i
  · exact orderedToCechAlternatingF_comp_d_comp_π_of_injective
      F U n i hi
  · have hleft :=
      orderedToCechAlternatingF_comp_d_comp_π_of_not_injective
        F U n i hi
    change (orderedToCechAlternatingF F U n ≫
      cechDifferentialProductF F U n) ≫ p = 0 at hleft
    have hright := orderedToCechAlternatingF_comp_π_of_not_injective
      F U (n + 1) i hi
    change orderedToCechAlternatingF F U (n + 1) ≫ p = 0 at hright
    rw [hleft, Category.assoc, hright, comp_zero]

/-- The alternating extension from ordered to native sheaf Cech cochains
commutes with the Cech differentials. -/
theorem orderedToCechAlternatingF_comp_d (n : ℕ) :
    orderedToCechAlternatingF F U n ≫ cechDifferential F U n =
      orderedCechDifferential F U n ≫
        orderedToCechAlternatingF F U (n + 1) := by
  change orderedToCechAlternatingF F U n ≫
      cechDifferentialProductF F U n =
    orderedCechDifferentialProductF F U n ≫
      orderedToCechAlternatingF F U (n + 1)
  exact orderedToCechAlternatingF_comp_product_d F U n

/-- Alternating extension from the ordered sheaf Cech complex to the native
sheaf Cech complex. -/
noncomputable def orderedToCechAlternating :
    orderedCechComplex F U ⟶ cechComplex F U :=
  CochainComplex.ofHom (orderedToCechAlternatingF F U) fun n => by
    rw [orderedCechComplex_d, cechComplex_d]
    exact orderedToCechAlternatingF_comp_d F U n

@[simp]
theorem orderedToCechAlternating_f (n : ℕ) :
    (orderedToCechAlternating F U).f n =
      orderedToCechAlternatingF F U n :=
  rfl

/-- Alternating extension followed by projection is the identity chain map on
the ordered sheaf Cech complex. -/
theorem orderedToCechAlternating_comp_cechToOrdered :
    orderedToCechAlternating F U ≫ cechToOrdered F U =
      𝟙 (orderedCechComplex F U) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact orderedToCechAlternatingF_comp_cechToOrderedF F U n

/-- Exactness of the native sheaf Cech complex descends to the ordered complex. -/
theorem orderedCechComplex_exactAt_of_cechComplex_exactAt (n : ℕ)
    (h : (cechComplex F U).ExactAt n) :
    (orderedCechComplex F U).ExactAt n :=
  h.of_retract
    (orderedToCechAlternating F U)
    (cechToOrdered F U)
    (orderedToCechAlternating_comp_cechToOrdered F U)

end TopCat.Sheaf
