/-
Copyright (c) 2026 AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!
# Hilbert's syzygy theorem

For a field `K` and `n : ℕ`, every module over the polynomial ring `MvPolynomial (Fin n) K` has
projective dimension `≤ n`.  This is Hilbert's syzygy theorem (finite global dimension of a
polynomial ring over a field).

The main result is `HilbertSyzygy.hasProjectiveDimensionLE_of_field`.  We prove the bound for
**all** modules (not merely finitely generated ones); the finitely-generated case
`hasProjectiveDimensionLE_of_field_of_finite` and the `projectiveDimension`-valued statement
`projectiveDimension_le_of_field` are immediate corollaries.

## Strategy

Induction on `n`, using mathlib's projective-dimension machinery
(`Mathlib.CategoryTheory.Abelian.Projective.Dimension`,
`Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension`):

* **Base case** (`n = 0`): `MvPolynomial (Fin 0) K ≃+* K` (`MvPolynomial.isEmptyRingEquiv`), and
  every module over a field is free, hence projective, hence has projective dimension `≤ 0`.  The
  bound is transported across the ring isomorphism via `hasProjectiveDimensionLE_of_semiLinearEquiv`
  (packaged here as `hasProjectiveDimensionLE_of_ringEquiv`).

* **Inductive step** (`n → n + 1`): `MvPolynomial (Fin (n+1)) K ≃ₐ[K] (MvPolynomial (Fin n) K)[X]`
  (`MvPolynomial.finSuccEquiv`).  We transport a module over `MvPolynomial (Fin (n+1)) K` to a
  module over `R[X]` (`R := MvPolynomial (Fin n) K`), apply the polynomial change-of-rings bound
  `polynomialChangeOfRings`, and transport the dimension bound back.

## The change-of-rings step

`polynomialChangeOfRings` (`pd_{R[X]} M ≤ (sup over R-modules of pd) + 1`) is the classical first
change-of-rings theorem for the polynomial extension `R ↪ R[X]`.  It is proved here from two
ingredients:

* `hasProjectiveDimensionLE_extendScalars` (**fully proved**): extension of scalars
  `R[X] ⊗_R (-)` preserves the bound `pd ≤ d`, because `R[X]` is free (hence flat) over `R`, so
  `extendScalars` is exact (`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`), and it
  preserves projective objects (it is a left adjoint whose right adjoint `restrictScalars` preserves
  epimorphisms).

* `exists_characteristicShortExact` (**now fully proved**): the *characteristic short exact
  sequence* of `R[X]`-modules `0 → R[X] ⊗_R M → R[X] ⊗_R M → M → 0`, whose surjection is the counit
  of `extendScalars ⊣ restrictScalars` (`ModuleCat.extendRestrictScalarsAdj`) and whose injection is
  `s ⊗ m ↦ sX ⊗ m - s ⊗ (X • m)`.  This is standard mathematics; via
  `PolynomialModule.polynomialTensorProductLEquivPolynomialModule` it becomes an explicit `Finsupp`
  exactness computation (a leading-coefficient injectivity argument and a downward-induction
  `range = ker` argument), carried out below.

Feeding the short exact sequence (both outer terms `R[X] ⊗_R M`, of `pd ≤ d`) into
`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃` yields the `d + 1` bound.

**Validation conclusion.**  The projective-dimension route to Hilbert's syzygy theorem — and hence
the Tor-free flat-locus development (DEV-1) — goes through with mathlib's present machinery: the
entire theorem reduces to the classical `exists_characteristicShortExact`, now proved from existing
mathlib ingredients.  No Buchsbaum–Eisenbud criterion is required.
-/

universe u

open CategoryTheory Abelian Module ModuleCat Limits

namespace HilbertSyzygy

noncomputable section

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- The ring homomorphism `R → R[X]`. -/
abbrev polyAlg (R : Type u) [CommRing R] : R →+* Polynomial R := algebraMap R (Polynomial R)

/-- The identity map, viewed as a semilinear equivalence from the `restrictScalars`-transported
module back to the original module along a ring isomorphism `e`. -/
def restrictScalarsSemilinearEquiv {R R' : Type u} [CommRing R] [CommRing R'] (e : R ≃+* R')
    (M : ModuleCat.{u} R') :
    ((ModuleCat.restrictScalars (e : R →+* R')).obj M) ≃ₛₗ[(e : R →+* R')] M where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transport a projective-dimension bound across a ring isomorphism: if the `R`-module obtained
from `M` by restricting scalars along `e : R ≃+* R'` has projective dimension `≤ n`, then so does
the `R'`-module `M`. -/
lemma hasProjectiveDimensionLE_of_ringEquiv {R R' : Type u} [CommRing R] [CommRing R']
    (e : R ≃+* R') (M : ModuleCat.{u} R') (n : ℕ)
    [HasProjectiveDimensionLE ((ModuleCat.restrictScalars (e : R →+* R')).obj M) n] :
    HasProjectiveDimensionLE M n :=
  ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e (restrictScalarsSemilinearEquiv e M) n

/-- Extension of scalars along `R → R[X]` preserves the bound `projective dimension ≤ n`:
if the `R`-module `N` has projective dimension `≤ n`, then the `R[X]`-module `R[X] ⊗_R N` does too.

`R[X]` is free, hence flat, over `R`, so `extendScalars` is exact; and it preserves projective
objects, being a left adjoint whose right adjoint `restrictScalars` preserves epimorphisms.  The
proof then mirrors `ModuleCat.localizedModule_hasProjectiveDimensionLE`. -/
lemma hasProjectiveDimensionLE_extendScalars (R : Type u) [CommRing R] (n : ℕ)
    (N : ModuleCat.{u} R) [HasProjectiveDimensionLE N n] :
    HasProjectiveDimensionLE ((extendScalars (polyAlg R)).obj N) n := by
  haveI hepi : (restrictScalars.{u} (polyAlg R)).PreservesEpimorphisms :=
    { preserves := fun g h => by rw [ModuleCat.epi_iff_surjective] at h ⊢; exact h }
  haveI plim : PreservesFiniteLimits (extendScalars.{u, u, u} (polyAlg R)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr Module.Flat.of_free)
  haveI padd : (extendScalars.{u, u, u} (polyAlg R)).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI pproj : (extendScalars.{u, u, u} (polyAlg R)).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj (polyAlg R))
  induction n generalizing N with
  | zero =>
    have projle : HasProjectiveDimensionLE N 0 := ‹_›
    simp only [HasProjectiveDimensionLE, zero_add] at projle ⊢
    rw [← projective_iff_hasProjectiveDimensionLT_one] at projle ⊢
    exact (extendScalars.{u, u, u} (polyAlg R)).projective_obj_of_projective projle
  | succ n ih =>
    rcases ModuleCat.enoughProjectives.1 N with ⟨⟨P, g⟩⟩
    let T := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
    have T_exact : T.ShortExact := { exact := ShortComplex.exact_kernel g }
    let TS := T.map (extendScalars.{u, u, u} (polyAlg R))
    have TS_exact : TS.ShortExact := T_exact.map_of_exact (extendScalars.{u, u, u} (polyAlg R))
    have hp2 : Projective TS.X₂ := (extendScalars.{u, u, u} (polyAlg R)).projective_obj _
    have := (T_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›).mp ‹_›
    exact (TS_exact.hasProjectiveDimensionLT_X₃_iff n hp2).mpr (ih (kernel g))

section Char
open Polynomial TensorProduct
open scoped ChangeOfRings
variable (R : Type u) [CommRing R] (M : ModuleCat.{u} (Polynomial R))

/-- `M` restricted to an `R`-module. -/
abbrev Mr : ModuleCat.{u} R := (restrictScalars (polyAlg R)).obj M
/-- Left tensor factor `S` as an `R`-module (via `restrictScalars`). -/
abbrev SL := ((restrictScalars (polyAlg R)).obj (ModuleCat.of (Polynomial R) (Polynomial R)))
/-- The extended module `R[X] ⊗_R Mᵣ`. -/
abbrev X2 : ModuleCat.{u} (Polynomial R) := (extendScalars (polyAlg R)).obj (Mr R M)
/-- The concrete `R[X]`-module `PolynomialModule R Mᵣ ≅ ℕ →₀ M`. -/
abbrev P := PolynomialModule R (Mr R M)

/-- `Module R` on `↑X2` (the tensor's base `R`-module), needed to bridge instances. -/
instance instModuleRX2 : Module R (X2 R M) :=
  inferInstanceAs (Module R (TensorProduct R (SL R) (Mr R M)))

/-! ### The bridge `P ≃ₗ[R[X]] X2` -/

def Lequiv : (Polynomial R) ⊗[R] (Mr R M) ≃ₗ[Polynomial R] P R M :=
  PolynomialModule.polynomialTensorProductLEquivPolynomialModule R (Mr R M)

def leftBridge : (Polynomial R) ≃ₗ[R] (SL R) where
  toFun s := s
  invFun s := s
  map_add' _ _ := rfl
  map_smul' r s := by
    simp only [RingHom.id_apply]
    show (r • s : Polynomial R) = polyAlg R r • (s : SL R)
    rw [Algebra.smul_def, smul_eq_mul]
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma leftBridge_apply (s : Polynomial R) : leftBridge R s = s := rfl

def bridgeR : (Polynomial R) ⊗[R] (Mr R M) ≃ₗ[R] (X2 R M) :=
  TensorProduct.congr (leftBridge R) (LinearEquiv.refl R (Mr R M))

@[simp] lemma bridgeR_tmul (s : Polynomial R) (m : Mr R M) :
    bridgeR R M (s ⊗ₜ[R] m) = (s ⊗ₜ[R, polyAlg R] m : X2 R M) := rfl

def bridgeS : (Polynomial R) ⊗[R] (Mr R M) ≃ₗ[Polynomial R] (X2 R M) where
  toFun := bridgeR R M
  invFun := (bridgeR R M).symm
  map_add' := map_add _
  map_smul' s x := by
    simp only [RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul a m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, bridgeR_tmul, bridgeR_tmul]
      exact (ExtendScalars.smul_tmul (polyAlg R) s a m).symm
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  left_inv := (bridgeR R M).left_inv
  right_inv := (bridgeR R M).right_inv

def eLin : P R M ≃ₗ[Polynomial R] (X2 R M) := (Lequiv R M).symm.trans (bridgeS R M)

lemma Lequiv_Xpow_tmul (i : ℕ) (m : Mr R M) :
    Lequiv R M (((X:Polynomial R)^i) ⊗ₜ[R] m) = PolynomialModule.single R i m := by
  change LinearMap.liftBaseChange (Polynomial R)
    (PolynomialModule.lsingle R 0) (((X:Polynomial R)^i) ⊗ₜ[R] m) = _
  rw [LinearMap.liftBaseChange_tmul, ← Polynomial.monomial_one_right_eq_X_pow]
  show monomial i (1:R) • PolynomialModule.single R 0 m = PolynomialModule.single R i m
  rw [PolynomialModule.monomial_smul_single, one_smul, Nat.add_zero]

lemma eLin_single (i : ℕ) (m : Mr R M) :
    eLin R M (PolynomialModule.single R i m)
      = (((X:Polynomial R)^i) ⊗ₜ[R, polyAlg R] m : X2 R M) := by
  rw [eLin, LinearEquiv.trans_apply, ← Lequiv_Xpow_tmul, LinearEquiv.symm_apply_apply]
  exact bridgeR_tmul R M _ m

/-! ### The counit surjection `ε` -/

lemma counit_tmul (s : Polynomial R) (m : Mr R M) :
    (ExtendRestrictScalarsAdj.Counit.map (polyAlg R)).hom
      (s ⊗ₜ[R, polyAlg R] m : X2 R M) = s • m := by
  erw [ExtendRestrictScalarsAdj.Counit.map_hom_apply]
  rfl

/-- `ε : P → M`, the counit transported along the bridge. -/
def epsP : P R M →ₗ[Polynomial R] (M : Type u) :=
  (ExtendRestrictScalarsAdj.Counit.map (polyAlg R)).hom ∘ₗ (eLin R M).toLinearMap

lemma epsP_single (i : ℕ) (m : Mr R M) :
    epsP R M (PolynomialModule.single R i m) = ((X:Polynomial R)^i) • m := by
  show (ExtendRestrictScalarsAdj.Counit.map (polyAlg R)).hom
    (eLin R M (PolynomialModule.single R i m)) = _
  rw [eLin_single, counit_tmul]

/-! ### The injection `φ` -/

def xAction : (Mr R M) →ₗ[R] (Mr R M) where
  toFun x := (X : Polynomial R) • x
  map_add' := smul_add _
  map_smul' r x := by
    show (X : Polynomial R) • ((polyAlg R r) • x) = (polyAlg R r) • ((X : Polynomial R) • x)
    rw [smul_smul, smul_smul, mul_comm]

@[simp] lemma xAction_apply (x : Mr R M) : xAction R M x = (X : Polynomial R) • x := rfl

/-- `mapψ : P → P`, applying the `X`-action degreewise; `R[X]`-linear. -/
def mapPsi : P R M →ₗ[Polynomial R] P R M where
  toFun := PolynomialModule.map R (xAction R M)
  map_add' := map_add _
  map_smul' p q := by
    simp only [RingHom.id_apply]
    rw [PolynomialModule.map_smul, Algebra.algebraMap_self, Polynomial.map_id]

@[simp] lemma mapPsi_single (i : ℕ) (m : Mr R M) :
    mapPsi R M (PolynomialModule.single R i m)
      = PolynomialModule.single R i ((X:Polynomial R) • m) := by
  show PolynomialModule.map R (xAction R M) (PolynomialModule.single R i m) = _
  rw [PolynomialModule.map_single, xAction_apply]

lemma X_smul_single (i : ℕ) (m : Mr R M) :
    (X : Polynomial R) • PolynomialModule.single R i m = PolynomialModule.single R (i+1) m := by
  rw [← Polynomial.monomial_one_one_eq_X, PolynomialModule.monomial_smul_single, one_smul,
    Nat.add_comm]

/-- `φ : P → P`, the injection `single i m ↦ single (i+1) m − single i (X • m)`. -/
def phiP : P R M →ₗ[Polynomial R] P R M :=
  LinearMap.lsmul (Polynomial R) (P R M) (X : Polynomial R) - mapPsi R M

@[simp] lemma phiP_single (i : ℕ) (m : Mr R M) :
    phiP R M (PolynomialModule.single R i m)
      = PolynomialModule.single R (i+1) m - PolynomialModule.single R i ((X:Polynomial R) • m) := by
  rw [phiP, LinearMap.sub_apply, mapPsi_single, LinearMap.lsmul_apply, X_smul_single]

/-! ### Exactness -/

set_option backward.isDefEq.respectTransparency false in
/-- `ε ∘ φ = 0`. -/
lemma epsP_phiP (q : P R M) : epsP R M (phiP R M q) = 0 := by
  induction q using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | single i m =>
    rw [phiP_single, map_sub, epsP_single, epsP_single, smul_smul, ← pow_succ, sub_self]

set_option backward.isDefEq.respectTransparency false in
/-- `ε` is surjective. -/
lemma epsP_surjective : Function.Surjective (epsP R M) :=
  fun m => ⟨PolynomialModule.single R 0 m, by rw [epsP_single, pow_zero, one_smul]⟩

/-- The `(n+1)`-coefficient of `φ q`. -/
lemma phiP_coeff_succ (q : P R M) (n : ℕ) :
    (phiP R M q).coeff (n+1) = q.coeff n - (X:Polynomial R) • (q.coeff (n+1)) := by
  show ((LinearMap.lsmul (Polynomial R) (P R M) (X:Polynomial R) - mapPsi R M) q).coeff (n+1) = _
  rw [LinearMap.sub_apply, LinearMap.lsmul_apply]
  change ((X:Polynomial R) • q).coeff (n+1) - (mapPsi R M q).coeff (n+1)
    = q.coeff n - (X:Polynomial R) • (q.coeff (n+1))
  congr 1
  rw [← Polynomial.monomial_one_one_eq_X, PolynomialModule.monomial_smul_apply]
  simp

lemma Pcoe_sub (a b : P R M) (i : ℕ) : (a - b).coeff i = a.coeff i - b.coeff i := by
  have : (a - b).coeff = a.coeff - b.coeff := map_sub PolynomialModule.coeffAddEquiv a b
  rw [this, Finsupp.sub_apply]
lemma Pcoe_single (k : ℕ) (a : Mr R M) (i : ℕ) :
    (PolynomialModule.single R k a).coeff i = if k = i then a else 0 := by
  rw [PolynomialModule.coeff_single, Finsupp.single_apply]

/-- `φ` is injective. -/
lemma phiP_injective : Function.Injective (phiP R M) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  by_contra h
  have hcne : q.coeff ≠ 0 := fun hc => h (PolynomialModule.coeff_injective (by simp [hc]))
  have hne : q.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr hcne
  set N := q.coeff.support.max' hne with hN
  have hNmem : N ∈ q.coeff.support := q.coeff.support.max'_mem hne
  have hqN : q.coeff N ≠ 0 := Finsupp.mem_support_iff.mp hNmem
  have hqN1 : q.coeff (N+1) = 0 := by
    by_contra hc
    have : N+1 ∈ q.coeff.support := Finsupp.mem_support_iff.mpr hc
    have := q.coeff.support.le_max' _ this
    omega
  have : (phiP R M q).coeff (N+1) = q.coeff N := by
    rw [phiP_coeff_succ, hqN1, smul_zero, sub_zero]
  rw [hq] at this
  exact hqN this.symm

/-- `ker ε ⊆ range φ`, by downward induction on the degree bound `n`. -/
lemma ker_le_range_aux : ∀ (n : ℕ) (q : P R M),
    (∀ i, n < i → q.coeff i = 0) → epsP R M q = 0 → q ∈ LinearMap.range (phiP R M) := by
  intro n
  induction n with
  | zero =>
    intro q hq he
    have hq0 : q = PolynomialModule.single R 0 (q.coeff 0) := by
      refine PolynomialModule.ext ?_
      refine Finsupp.ext fun j => ?_
      rw [Pcoe_single]
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp
      · rw [hq j hj, if_neg (by omega)]
    have hval : epsP R M q = q.coeff 0 := by
      conv_lhs => rw [hq0]
      rw [epsP_single, pow_zero, one_smul]
    rw [hval] at he
    refine ⟨0, ?_⟩
    rw [map_zero, hq0, he]
    exact (PolynomialModule.single_zero (R := R) 0).symm
  | succ n ih =>
    intro q hq he
    set m := q.coeff (n+1) with hm
    set q' := q - phiP R M (PolynomialModule.single R n m) with hq'
    have hbound : ∀ i, n < i → q'.coeff i = 0 := by
      intro i hi
      rw [hq', Pcoe_sub, phiP_single, Pcoe_sub, Pcoe_single, Pcoe_single]
      rcases Nat.lt_or_ge (n+1) i with h1 | h1
      · rw [hq i h1, if_neg (by omega), if_neg (by omega)]; simp
      · have : i = n+1 := by omega
        subst this
        rw [if_pos rfl, if_neg (by omega), ← hm]; simp
    have he' : epsP R M q' = 0 := by rw [hq', map_sub, he, epsP_phiP, sub_zero]
    obtain ⟨p', hp'⟩ := ih q' hbound he'
    refine ⟨p' + PolynomialModule.single R n m, ?_⟩
    rw [map_add, hp', hq']
    abel

/-- The sequence `P --φ--> P --ε--> M` is exact. -/
lemma phiP_epsP_exact : Function.Exact (phiP R M) (epsP R M) := by
  intro q
  constructor
  · intro he
    refine ker_le_range_aux R M (q.coeff.support.sup id) q (fun i hi => ?_) he
    by_contra hc
    have hle := Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr hc)
    simp only [id_eq] at hle
    omega
  · rintro ⟨p, rfl⟩
    exact epsP_phiP R M p

/-! ### Assembly -/

lemma of_coe_X2 : ModuleCat.of (Polynomial R) (X2 R M : Type u) = X2 R M := rfl
lemma of_coe_M : ModuleCat.of (Polynomial R) (M : Type u) = M := rfl

/-- The characteristic short complex `P --φ--> P --ε--> M`. -/
def charSES : ShortComplex (ModuleCat.{u} (Polynomial R)) :=
  ModuleCat.shortComplexOfCompEqZero (phiP R M) (epsP R M)
    (by ext q; exact epsP_phiP R M q)

lemma charSES_shortExact : (charSES R M).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (phiP_epsP_exact R M)
    (phiP_injective R M) (epsP_surjective R M)

end Char

/-- **The characteristic short exact sequence** of an `R[X]`-module `M`:
`0 → R[X] ⊗_R M → R[X] ⊗_R M → M → 0` (restriction of scalars is left implicit in the tensor
factors).  The surjection is the counit of `extendScalars ⊣ restrictScalars`; the injection is
`s ⊗ m ↦ sX ⊗ m - s ⊗ (X • m)`.

It is proved as a standard `Finsupp` exactness computation, transporting the concrete
`PolynomialModule R Mᵣ` model to `R[X] ⊗_R Mᵣ` through
`PolynomialModule.polynomialTensorProductLEquivPolynomialModule`; see the module docstring and the
`charSES` helpers above. -/
lemma exists_characteristicShortExact (R : Type u) [CommRing R]
    (M : ModuleCat.{u} (Polynomial R)) :
    ∃ S : ShortComplex (ModuleCat.{u} (Polynomial R)), S.ShortExact ∧
      Nonempty (S.X₁ ≅ (extendScalars (polyAlg R)).obj ((restrictScalars (polyAlg R)).obj M)) ∧
      Nonempty (S.X₂ ≅ (extendScalars (polyAlg R)).obj ((restrictScalars (polyAlg R)).obj M)) ∧
      Nonempty (S.X₃ ≅ M) := by
  exact ⟨charSES R M, charSES_shortExact R M,
    ⟨(eLin R M).toModuleIso⟩, ⟨(eLin R M).toModuleIso⟩, ⟨Iso.refl _⟩⟩

/-- **Polynomial change of rings for projective dimension.**  If every `R`-module has projective
dimension `≤ d`, then every `R[X]`-module has projective dimension `≤ d + 1`.

Proved from `hasProjectiveDimensionLE_extendScalars` and `exists_characteristicShortExact`: the
characteristic sequence `0 → R[X] ⊗_R M → R[X] ⊗_R M → M → 0` has both outer terms of projective
dimension `≤ d`, so `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃` bounds `M` by `d + 1`. -/
lemma polynomialChangeOfRings (R : Type u) [CommRing R] (d : ℕ)
    (hd : ∀ (N : ModuleCat.{u} R), HasProjectiveDimensionLE N d)
    (M : ModuleCat.{u} (Polynomial R)) :
    HasProjectiveDimensionLE M (d + 1) := by
  haveI hMdown : HasProjectiveDimensionLE ((restrictScalars (polyAlg R)).obj M) d := hd _
  haveI hP : HasProjectiveDimensionLE
      ((extendScalars (polyAlg R)).obj ((restrictScalars (polyAlg R)).obj M)) d :=
    hasProjectiveDimensionLE_extendScalars R d _
  obtain ⟨S, hSE, ⟨e1⟩, ⟨e2⟩, ⟨e3⟩⟩ := exists_characteristicShortExact R M
  have hX3 : HasProjectiveDimensionLT S.X₃ (d + 2) := by
    have h1 : HasProjectiveDimensionLT S.X₁ (d + 1) := by
      have : HasProjectiveDimensionLT ((extendScalars (polyAlg R)).obj
          ((restrictScalars (polyAlg R)).obj M)) (d + 1) := hP
      exact hasProjectiveDimensionLT_of_iso e1.symm (d + 1)
    have h2 : HasProjectiveDimensionLT S.X₂ (d + 2) := by
      have : HasProjectiveDimensionLE ((extendScalars (polyAlg R)).obj
          ((restrictScalars (polyAlg R)).obj M)) (d + 1) :=
        hasProjectiveDimensionLT_of_ge _ (d + 1) (d + 2) (by omega)
      exact hasProjectiveDimensionLT_of_iso e2.symm (d + 2)
    exact hSE.hasProjectiveDimensionLT_X₃ (d + 1) h1 h2
  exact hasProjectiveDimensionLT_of_iso e3 (d + 2)

/-- Base case of Hilbert's syzygy theorem: every module over `MvPolynomial (Fin 0) K` (which is
isomorphic to the field `K`) has projective dimension `≤ 0`, i.e. is projective. -/
lemma hasProjectiveDimensionLE_of_field_zero (K : Type u) [Field K]
    (M : ModuleCat.{u} (MvPolynomial (Fin 0) K)) :
    HasProjectiveDimensionLE M 0 := by
  -- `MvPolynomial (Fin 0) K ≃+* K`, so restricting scalars turns `M` into a `K`-vector space.
  let e : K ≃+* MvPolynomial (Fin 0) K := (MvPolynomial.isEmptyRingEquiv K (Fin 0)).symm
  let Msrc := (ModuleCat.restrictScalars (e : K →+* MvPolynomial (Fin 0) K)).obj M
  -- A `K`-vector space is free, hence projective, hence has projective dimension `≤ 0`.
  have : HasProjectiveDimensionLE Msrc 0 :=
    (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero Msrc).mp
      (ModuleCat.projective_of_free (Module.Free.chooseBasis K Msrc))
  exact hasProjectiveDimensionLE_of_ringEquiv e M 0

/-- **Hilbert's syzygy theorem.**  For a field `K`, every module over the polynomial ring
`MvPolynomial (Fin n) K` has projective dimension `≤ n`.  (The bound holds for all modules, not
merely finitely generated ones.) -/
theorem hasProjectiveDimensionLE_of_field (K : Type u) [Field K] (n : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin n) K)) :
    HasProjectiveDimensionLE M n := by
  induction n with
  | zero => exact hasProjectiveDimensionLE_of_field_zero K M
  | succ n hn =>
    -- `MvPolynomial (Fin (n+1)) K ≃+* (MvPolynomial (Fin n) K)[X]`.
    let e : Polynomial (MvPolynomial (Fin n) K) ≃+* MvPolynomial (Fin (n + 1)) K :=
      (MvPolynomial.finSuccEquiv K n).toRingEquiv.symm
    -- Restrict `M` to an `R[X]`-module and apply the polynomial change-of-rings bound with the IH.
    have hstep : HasProjectiveDimensionLE
        ((ModuleCat.restrictScalars (e : _ →+* _)).obj M) (n + 1) :=
      polynomialChangeOfRings (MvPolynomial (Fin n) K) n hn _
    exact hasProjectiveDimensionLE_of_ringEquiv e M (n + 1)

/-- Hilbert's syzygy theorem, in the requested finitely-generated form: a finitely generated module
over `MvPolynomial (Fin n) K` has projective dimension `≤ n`. -/
theorem hasProjectiveDimensionLE_of_field_of_finite (K : Type u) [Field K] (n : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin n) K)) [Module.Finite (MvPolynomial (Fin n) K) M] :
    HasProjectiveDimensionLE M n :=
  hasProjectiveDimensionLE_of_field K n M

/-- Hilbert's syzygy theorem, phrased with `projectiveDimension`:
`projectiveDimension M ≤ n` for every module over `MvPolynomial (Fin n) K`. -/
theorem projectiveDimension_le_of_field (K : Type u) [Field K] (n : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin n) K)) :
    projectiveDimension M ≤ (n : WithBot ℕ∞) :=
  (CategoryTheory.projectiveDimension_le_iff M n).mpr (hasProjectiveDimensionLE_of_field K n M)

end

end HilbertSyzygy
