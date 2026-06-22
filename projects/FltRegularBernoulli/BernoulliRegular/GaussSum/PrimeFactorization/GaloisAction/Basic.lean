module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import BernoulliRegular.CyclotomicEmbedding
public import BernoulliRegular.GaussSum.PrimeFactorization.PrimesAboveP

/-!
# Exponent-indexed Galois actions in the Stickelberger field

Let

`L = ℚ(ζ_{p(p-1)})`.

This file packages the cyclotomic Galois action on `L` in the form needed for
the Stickelberger prime-factorization argument.

For `T027d3c`, we work with the standard equivalence

`Gal(L/ℚ) ≃* (ZMod (p * (p - 1)))ˣ`

and use it to define the automorphism indexed by a unit exponent. We then
record the action of this automorphism on the distinguished primitive
`p(p-1)`-th root of unity and on the derived primitive `p`- and `(p-1)`-th
roots that underlie the Gauss-sum lift.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped Pointwise

namespace BernoulliRegular

section GaloisAction

variable (p : ℕ) [hp : Fact p.Prime]
  (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {p * (p - 1)} ℚ L]

local notation "N" => p * (p - 1)
local notation "𝔭" => (Ideal.span ({(p : ℤ)} : Set ℤ))
local instance : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩

lemma stickelbergerN_pos : 0 < N := by
  refine Nat.mul_pos hp.out.pos ?_
  have hp_one_lt : 1 < p := hp.out.one_lt
  omega

instance : NeZero N :=
  ⟨(stickelbergerN_pos (p := p)).ne'⟩

lemma prime_coprime_pred : p.Coprime (p - 1) :=
  hp.out.coprime_iff_not_dvd.mpr <|
    Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.out.one_lt) (Nat.pred_lt hp.out.ne_zero)

/-- The standard cyclotomic description of `Gal(L/ℚ)` by unit exponents modulo
`p (p - 1)`. -/
noncomputable abbrev stickelbergerGalEquivZMod : Gal(L / ℚ) ≃* (ZMod N)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod N L

/-- The Galois automorphism indexed by the unit exponent `u`. -/
noncomputable def sigmaOfExponent (u : (ZMod N)ˣ) : Gal(L / ℚ) :=
  (stickelbergerGalEquivZMod (p := p) L).symm u

@[simp]
lemma stickelbergerGalEquivZMod_sigmaOfExponent (u : (ZMod N)ˣ) :
    stickelbergerGalEquivZMod (p := p) L (sigmaOfExponent (p := p) L u) = u :=
  (stickelbergerGalEquivZMod (p := p) L).apply_symm_apply u

/-- The distinguished primitive `N`-th root of unity in the Stickelberger
field, viewed in the ring of integers. -/
noncomputable abbrev stickelbergerZetaInteger : 𝓞 L :=
  (IsCyclotomicExtension.zeta_spec N ℚ L).toInteger

lemma stickelbergerZetaInteger_isPrimitiveRoot :
    IsPrimitiveRoot (stickelbergerZetaInteger (p := p) L) N := by
  simpa [stickelbergerZetaInteger] using
    (IsCyclotomicExtension.zeta_spec N ℚ L).toInteger_isPrimitiveRoot

@[simp]
lemma sigmaOfExponent_apply_zeta (u : (ZMod N)ˣ) :
    sigmaOfExponent (p := p) L u (IsCyclotomicExtension.zeta N ℚ L) =
      (IsCyclotomicExtension.zeta N ℚ L) ^ u.val.val := by
  let σ := sigmaOfExponent (p := p) L u
  have h :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (n := N) (K := L) (σ := σ)
      (x := IsCyclotomicExtension.zeta N ℚ L)
      ((IsCyclotomicExtension.zeta_spec N ℚ L).pow_eq_one)
  rw [show IsCyclotomicExtension.Rat.galEquivZMod N L σ = u by
      exact stickelbergerGalEquivZMod_sigmaOfExponent (p := p) (L := L) u] at h
  exact h

@[simp]
lemma sigmaOfExponent_smul_stickelbergerZetaInteger (u : (ZMod N)ˣ) :
    sigmaOfExponent (p := p) L u • stickelbergerZetaInteger (p := p) L =
      stickelbergerZetaInteger (p := p) L ^ u.val.val := by
  let σ := sigmaOfExponent (p := p) L u
  have h :=
    IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq
      (n := N) (K := L) (σ := σ)
      (x := stickelbergerZetaInteger (p := p) L)
      ((stickelbergerZetaInteger_isPrimitiveRoot (p := p) (L := L)).pow_eq_one)
  rw [show IsCyclotomicExtension.Rat.galEquivZMod N L σ = u by
      exact stickelbergerGalEquivZMod_sigmaOfExponent (p := p) (L := L) u] at h
  exact h

/-- The primitive `p`-th root extracted from the distinguished `N`-th root.
This is the additive root occurring in the Gauss-sum lift. -/
noncomputable abbrev gaussSumLiftAdditiveRoot : 𝓞 L :=
  stickelbergerZetaInteger (p := p) L ^ (p - 1)

lemma gaussSumLiftAdditiveRoot_isPrimitiveRoot :
    IsPrimitiveRoot (gaussSumLiftAdditiveRoot (p := p) L) p := by
  simpa [gaussSumLiftAdditiveRoot] using
    (stickelbergerZetaInteger_isPrimitiveRoot (p := p) (L := L)).pow
      (stickelbergerN_pos (p := p)) (by ring)

@[simp]
lemma sigmaOfExponent_smul_gaussSumLiftAdditiveRoot (u : (ZMod N)ˣ) :
    sigmaOfExponent (p := p) L u • gaussSumLiftAdditiveRoot (p := p) L =
      gaussSumLiftAdditiveRoot (p := p) L ^ u.val.val := by
  calc
    sigmaOfExponent (p := p) L u • gaussSumLiftAdditiveRoot (p := p) L
        = (sigmaOfExponent (p := p) L u • stickelbergerZetaInteger (p := p) L) ^ (p - 1) := by
            simp [gaussSumLiftAdditiveRoot]
    _ = (stickelbergerZetaInteger (p := p) L ^ u.val.val) ^ (p - 1) := by
          rw [sigmaOfExponent_smul_stickelbergerZetaInteger (p := p) (L := L) u]
    _ = (stickelbergerZetaInteger (p := p) L ^ (p - 1)) ^ u.val.val := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = gaussSumLiftAdditiveRoot (p := p) L ^ u.val.val := by
          simp [gaussSumLiftAdditiveRoot]

/-- The primitive `(p - 1)`-th root extracted from the distinguished `N`-th
root. This is the multiplicative-character root occurring in the lift. -/
noncomputable abbrev gaussSumLiftCharacterRoot : 𝓞 L :=
  stickelbergerZetaInteger (p := p) L ^ p

lemma gaussSumLiftCharacterRoot_isPrimitiveRoot :
    IsPrimitiveRoot (gaussSumLiftCharacterRoot (p := p) L) (p - 1) := by
  simpa [gaussSumLiftCharacterRoot] using
    (stickelbergerZetaInteger_isPrimitiveRoot (p := p) (L := L)).pow
      (stickelbergerN_pos (p := p)) rfl

@[simp]
lemma sigmaOfExponent_smul_gaussSumLiftCharacterRoot (u : (ZMod N)ˣ) :
    sigmaOfExponent (p := p) L u • gaussSumLiftCharacterRoot (p := p) L =
      gaussSumLiftCharacterRoot (p := p) L ^ u.val.val := by
  calc
    sigmaOfExponent (p := p) L u • gaussSumLiftCharacterRoot (p := p) L
        = (sigmaOfExponent (p := p) L u • stickelbergerZetaInteger (p := p) L) ^ p := by
            simp [gaussSumLiftCharacterRoot]
    _ = (stickelbergerZetaInteger (p := p) L ^ u.val.val) ^ p := by
          rw [sigmaOfExponent_smul_stickelbergerZetaInteger (p := p) (L := L) u]
    _ = (stickelbergerZetaInteger (p := p) L ^ p) ^ u.val.val := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = gaussSumLiftCharacterRoot (p := p) L ^ u.val.val := by
          simp [gaussSumLiftCharacterRoot]

/-- The unit-level CRT description of exponents mod `p (p - 1)`. -/
noncomputable abbrev stickelbergerUnitsEquivProd :
    (ZMod N)ˣ ≃* (ZMod p)ˣ × (ZMod (p - 1))ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder (prime_coprime_pred (p := p))).toMulEquiv).trans
    MulEquiv.prodUnits

/-- The exponent whose image under the unit-level CRT equivalence is `(a, 1)`. -/
noncomputable def unitExponentOfUnit (a : (ZMod p)ˣ) : (ZMod N)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder (prime_coprime_pred (p := p))).toMulEquiv).symm
    (MulEquiv.prodUnits.symm (a, 1))

@[simp]
lemma stickelbergerUnitsEquivProd_unitExponentOfUnit (a : (ZMod p)ˣ) :
    stickelbergerUnitsEquivProd (p := p) (unitExponentOfUnit (p := p) a) =
      (a, 1) :=
  (stickelbergerUnitsEquivProd (p := p)).apply_symm_apply (a, 1)

/-- The CRT image of the exponent `(Units.mapEquiv …).symm (prodUnits.symm q)` is the
componentwise coercion of the pair `q`. Shared core of the `cast`/`modEq` lemmas below. -/
private lemma chineseRemainder_coe_mapEquiv_symm_prodUnits_symm
    (q : (ZMod p)ˣ × (ZMod (p - 1))ˣ) :
    ZMod.chineseRemainder (prime_coprime_pred (p := p))
        (((Units.mapEquiv (ZMod.chineseRemainder (prime_coprime_pred (p := p))).toMulEquiv).symm
            (MulEquiv.prodUnits.symm q) : (ZMod N)ˣ) : ZMod N) =
      ((q.1 : ZMod p), (q.2 : ZMod (p - 1))) := by
  rw [Units.mapEquiv_symm, Units.coe_mapEquiv,
    show ((MulEquiv.prodUnits.symm q : (ZMod p × ZMod (p - 1))ˣ) : ZMod p × ZMod (p - 1)) =
        ((q.1 : ZMod p), (q.2 : ZMod (p - 1))) from rfl]
  exact (ZMod.chineseRemainder (prime_coprime_pred (p := p))).apply_symm_apply _

lemma unitExponentOfUnit_cast_p (a : (ZMod p)ˣ) :
    (((unitExponentOfUnit (p := p) a : (ZMod N)ˣ) : ZMod N).cast : ZMod p) = a := by
  simpa [ZMod.chineseRemainder, unitExponentOfUnit] using
    congrArg Prod.fst (chineseRemainder_coe_mapEquiv_symm_prodUnits_symm (p := p) (a, 1))

lemma unitExponentOfUnit_cast_pred (a : (ZMod p)ˣ) :
    (((unitExponentOfUnit (p := p) a : (ZMod N)ˣ) : ZMod N).cast : ZMod (p - 1)) = 1 := by
  simpa [ZMod.chineseRemainder, unitExponentOfUnit] using
    congrArg Prod.snd (chineseRemainder_coe_mapEquiv_symm_prodUnits_symm (p := p) (a, 1))

lemma unitExponentOfUnit_modEq_val (a : (ZMod p)ˣ) :
    (unitExponentOfUnit (p := p) a).val.val ≡ (a : ZMod p).val [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_val]
  simpa using unitExponentOfUnit_cast_p (p := p) a

lemma unitExponentOfUnit_modEq_one (a : (ZMod p)ˣ) :
    (unitExponentOfUnit (p := p) a).val.val ≡ 1 [MOD p - 1] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val]
  simpa using unitExponentOfUnit_cast_pred (p := p) a

/-- The Galois automorphism indexed by `a : (ZMod p)ˣ`, acting by `a` on the
additive `p`-root and trivially on the `(p - 1)`-root. -/
noncomputable def sigmaOfUnit (a : (ZMod p)ˣ) : Gal(L / ℚ) :=
  sigmaOfExponent (p := p) L (unitExponentOfUnit (p := p) a)

lemma sigmaOfUnit_smul_gaussSumLiftAdditiveRoot (a : (ZMod p)ˣ) :
    sigmaOfUnit (p := p) L a • gaussSumLiftAdditiveRoot (p := p) L =
      gaussSumLiftAdditiveRoot (p := p) L ^ (a : ZMod p).val := by
  calc
    sigmaOfUnit (p := p) L a • gaussSumLiftAdditiveRoot (p := p) L
        = gaussSumLiftAdditiveRoot (p := p) L ^
            (unitExponentOfUnit (p := p) a).val.val :=
              sigmaOfExponent_smul_gaussSumLiftAdditiveRoot
                (p := p) (L := L) (unitExponentOfUnit (p := p) a)
    _ = gaussSumLiftAdditiveRoot (p := p) L ^ (a : ZMod p).val :=
          pow_eq_pow_of_modEq
            (unitExponentOfUnit_modEq_val (p := p) a)
            ((gaussSumLiftAdditiveRoot_isPrimitiveRoot (p := p) (L := L)).pow_eq_one)

lemma sigmaOfUnit_smul_gaussSumLiftCharacterRoot (a : (ZMod p)ˣ) :
    sigmaOfUnit (p := p) L a • gaussSumLiftCharacterRoot (p := p) L =
      gaussSumLiftCharacterRoot (p := p) L := by
  calc
    sigmaOfUnit (p := p) L a • gaussSumLiftCharacterRoot (p := p) L
        = gaussSumLiftCharacterRoot (p := p) L ^
            (unitExponentOfUnit (p := p) a).val.val :=
              sigmaOfExponent_smul_gaussSumLiftCharacterRoot
                (p := p) (L := L) (unitExponentOfUnit (p := p) a)
    _ = gaussSumLiftCharacterRoot (p := p) L ^ 1 :=
          pow_eq_pow_of_modEq
            (unitExponentOfUnit_modEq_one (p := p) a)
            ((gaussSumLiftCharacterRoot_isPrimitiveRoot (p := p) (L := L)).pow_eq_one)
    _ = gaussSumLiftCharacterRoot (p := p) L := by simp

/-- The exponent whose image under the unit-level CRT equivalence is `(1, b)`. -/
noncomputable def characterExponentOfUnit (b : (ZMod (p - 1))ˣ) : (ZMod N)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder (prime_coprime_pred (p := p))).toMulEquiv).symm
    (MulEquiv.prodUnits.symm (1, b))

@[simp]
lemma stickelbergerUnitsEquivProd_characterExponentOfUnit (b : (ZMod (p - 1))ˣ) :
    stickelbergerUnitsEquivProd (p := p) (characterExponentOfUnit (p := p) b) =
      (1, b) :=
  (stickelbergerUnitsEquivProd (p := p)).apply_symm_apply (1, b)

lemma characterExponentOfUnit_cast_p (b : (ZMod (p - 1))ˣ) :
    (((characterExponentOfUnit (p := p) b : (ZMod N)ˣ) : ZMod N).cast : ZMod p) = 1 := by
  simpa [ZMod.chineseRemainder, characterExponentOfUnit] using
    congrArg Prod.fst (chineseRemainder_coe_mapEquiv_symm_prodUnits_symm (p := p) (1, b))

lemma characterExponentOfUnit_cast_pred (b : (ZMod (p - 1))ˣ) :
    (((characterExponentOfUnit (p := p) b : (ZMod N)ˣ) : ZMod N).cast : ZMod (p - 1)) = b := by
  simpa [ZMod.chineseRemainder, characterExponentOfUnit] using
    congrArg Prod.snd (chineseRemainder_coe_mapEquiv_symm_prodUnits_symm (p := p) (1, b))

lemma characterExponentOfUnit_modEq_one (b : (ZMod (p - 1))ˣ) :
    (characterExponentOfUnit (p := p) b).val.val ≡ 1 [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val]
  simpa using characterExponentOfUnit_cast_p (p := p) b

lemma characterExponentOfUnit_modEq_val (b : (ZMod (p - 1))ˣ) :
    (characterExponentOfUnit (p := p) b).val.val ≡ (b : ZMod (p - 1)).val [MOD p - 1] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_val]
  simpa using characterExponentOfUnit_cast_pred (p := p) b

/-- The Galois automorphism indexed by `b : (ZMod (p - 1))ˣ`, acting trivially
on the additive `p`-root and by `b` on the character `(p - 1)`-root. -/
noncomputable def sigmaOfCharacterUnit (b : (ZMod (p - 1))ˣ) : Gal(L / ℚ) :=
  sigmaOfExponent (p := p) L (characterExponentOfUnit (p := p) b)

lemma sigmaOfCharacterUnit_smul_gaussSumLiftAdditiveRoot (b : (ZMod (p - 1))ˣ) :
    sigmaOfCharacterUnit (p := p) L b • gaussSumLiftAdditiveRoot (p := p) L =
      gaussSumLiftAdditiveRoot (p := p) L := by
  calc
    sigmaOfCharacterUnit (p := p) L b • gaussSumLiftAdditiveRoot (p := p) L
        = gaussSumLiftAdditiveRoot (p := p) L ^
            (characterExponentOfUnit (p := p) b).val.val :=
              sigmaOfExponent_smul_gaussSumLiftAdditiveRoot
                (p := p) (L := L) (characterExponentOfUnit (p := p) b)
    _ = gaussSumLiftAdditiveRoot (p := p) L ^ 1 :=
          pow_eq_pow_of_modEq
            (characterExponentOfUnit_modEq_one (p := p) b)
            ((gaussSumLiftAdditiveRoot_isPrimitiveRoot (p := p) (L := L)).pow_eq_one)
    _ = gaussSumLiftAdditiveRoot (p := p) L := by simp

lemma sigmaOfCharacterUnit_smul_gaussSumLiftCharacterRoot (b : (ZMod (p - 1))ˣ) :
    sigmaOfCharacterUnit (p := p) L b • gaussSumLiftCharacterRoot (p := p) L =
      gaussSumLiftCharacterRoot (p := p) L ^ (b : ZMod (p - 1)).val := by
  calc
    sigmaOfCharacterUnit (p := p) L b • gaussSumLiftCharacterRoot (p := p) L
        = gaussSumLiftCharacterRoot (p := p) L ^
            (characterExponentOfUnit (p := p) b).val.val :=
              sigmaOfExponent_smul_gaussSumLiftCharacterRoot
                (p := p) (L := L) (characterExponentOfUnit (p := p) b)
    _ = gaussSumLiftCharacterRoot (p := p) L ^ (b : ZMod (p - 1)).val :=
          pow_eq_pow_of_modEq
            (characterExponentOfUnit_modEq_val (p := p) b)
            ((gaussSumLiftCharacterRoot_isPrimitiveRoot (p := p) (L := L)).pow_eq_one)

/-- The complex primitive root obtained by applying the character-side lift. -/
noncomputable def characterSideComplexRoot (b : (ZMod (p - 1))ˣ) : ℂ :=
  stickelbergerComplexRoot p ^ (characterExponentOfUnit (p := p) b).val.val

lemma characterSideComplexRoot_isPrimitiveRoot (b : (ZMod (p - 1))ˣ) :
    IsPrimitiveRoot (characterSideComplexRoot (p := p) b) N := by
  simpa [characterSideComplexRoot] using
    (stickelbergerComplexRoot_isPrimitiveRoot (p := p)).pow_of_coprime
      (characterExponentOfUnit (p := p) b).val.val
      (ZMod.val_coe_unit_coprime (characterExponentOfUnit (p := p) b))

/-- The complex embedding corresponding to the character-side lift. -/
noncomputable def characterSideEmbedding (b : (ZMod (p - 1))ˣ) : L →ₐ[ℚ] ℂ :=
  complexEmbedding_of_primitiveRoot N L
    (characterSideComplexRoot_isPrimitiveRoot (p := p) b)

lemma stickelbergerEmbedding_comp_sigmaOfCharacterUnit_apply_zeta (b : (ZMod (p - 1))ˣ) :
    ((stickelbergerEmbedding p L).comp (sigmaOfCharacterUnit (p := p) L b))
        (IsCyclotomicExtension.zeta N ℚ L) =
      characterSideComplexRoot (p := p) b := by
  have h_sigma :
      (sigmaOfCharacterUnit (p := p) L b) (IsCyclotomicExtension.zeta N ℚ L) =
        (IsCyclotomicExtension.zeta N ℚ L) ^
          (characterExponentOfUnit (p := p) b).val.val := by
    rw [sigmaOfCharacterUnit]
    exact sigmaOfExponent_apply_zeta (p := p) (L := L)
      (u := characterExponentOfUnit (p := p) b)
  calc
    ((stickelbergerEmbedding p L).comp (sigmaOfCharacterUnit (p := p) L b))
        (IsCyclotomicExtension.zeta N ℚ L)
        = stickelbergerEmbedding p L
            ((sigmaOfCharacterUnit (p := p) L b) (IsCyclotomicExtension.zeta N ℚ L)) := by
              rfl
    _ = stickelbergerEmbedding p L
          ((IsCyclotomicExtension.zeta N ℚ L) ^
            (characterExponentOfUnit (p := p) b).val.val) := by rw [h_sigma]
    _ = characterSideComplexRoot (p := p) b := by
          simp [characterSideComplexRoot, map_pow, stickelbergerEmbedding_apply_zeta]

lemma stickelbergerEmbedding_comp_sigmaOfCharacterUnit_eq_characterSideEmbedding
    (b : (ZMod (p - 1))ˣ) :
    (stickelbergerEmbedding p L).comp (sigmaOfCharacterUnit (p := p) L b) =
      characterSideEmbedding (p := p) (L := L) b := by
  let hirr : Irreducible (Polynomial.cyclotomic N ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (stickelbergerN_pos (p := p))
  let hζL : IsPrimitiveRoot (IsCyclotomicExtension.zeta N ℚ L) N :=
    IsCyclotomicExtension.zeta_spec N ℚ L
  apply (hζL.embeddingsEquivPrimitiveRoots (K := ℚ) (L := L) ℂ hirr).injective
  ext
  simp only [IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe, characterSideEmbedding]
  rw [stickelbergerEmbedding_comp_sigmaOfCharacterUnit_apply_zeta]
  exact (complexEmbedding_of_primitiveRoot_apply_zeta N L
    (characterSideComplexRoot_isPrimitiveRoot (p := p) b)).symm

/-- A chosen generator of the unit group `(ZMod p)ˣ`. -/
noncomputable def characterUnitGenerator : (ZMod p)ˣ :=
  Classical.choose (IsCyclic.exists_generator (α := (ZMod p)ˣ))

theorem characterUnitGenerator_zpowers :
    ∀ u : (ZMod p)ˣ, u ∈ Subgroup.zpowers (characterUnitGenerator (p := p)) := by
  simpa [characterUnitGenerator] using
    Classical.choose_spec (IsCyclic.exists_generator (α := (ZMod p)ˣ))

/-- The distinguished complex `(p - 1)`-th root used to encode multiplicative
character values in the Stickelberger field. -/
noncomputable def stickelbergerComplexCharacterRoot : ℂ :=
  stickelbergerComplexRoot p ^ p

lemma stickelbergerComplexCharacterRoot_isPrimitiveRoot :
    IsPrimitiveRoot (stickelbergerComplexCharacterRoot (p := p)) (p - 1) := by
  simpa [stickelbergerComplexCharacterRoot] using
    (stickelbergerComplexRoot_isPrimitiveRoot (p := p)).pow
      (stickelbergerN_pos (p := p)) rfl

/-- The distinguished unit whose value is the complex `(p - 1)`-th root used
to encode character values. -/
noncomputable def stickelbergerComplexCharacterRootUnit : ℂˣ :=
  ((stickelbergerComplexCharacterRoot_isPrimitiveRoot (p := p)).isUnit
    (Nat.sub_ne_zero_of_lt hp.out.one_lt)).unit

@[simp]
lemma coe_stickelbergerComplexCharacterRootUnit :
    (stickelbergerComplexCharacterRootUnit (p := p) : ℂ) =
      stickelbergerComplexCharacterRoot (p := p) :=
  ((stickelbergerComplexCharacterRoot_isPrimitiveRoot (p := p)).isUnit
    (Nat.sub_ne_zero_of_lt hp.out.one_lt)).unit_spec

lemma stickelbergerComplexCharacterRootUnit_mem_rootsOfUnity :
    stickelbergerComplexCharacterRootUnit (p := p) ∈ rootsOfUnity (Fintype.card (ZMod p)ˣ) ℂ := by
  refine (mem_rootsOfUnity _ _).2 ?_
  rw [ZMod.card_units]
  ext
  simp [coe_stickelbergerComplexCharacterRootUnit,
    (stickelbergerComplexCharacterRoot_isPrimitiveRoot (p := p)).pow_eq_one]

/-- The complex Dirichlet-character generator whose value on the chosen unit
generator is the distinguished root `stickelbergerComplexRoot p ^ p`. -/
noncomputable def stickelbergerComplexCharacterGenerator : DirichletCharacter ℂ p :=
  MulChar.ofRootOfUnity (M := ZMod p) (R := ℂ)
    (stickelbergerComplexCharacterRootUnit_mem_rootsOfUnity (p := p))
    (characterUnitGenerator_zpowers (p := p))

lemma stickelbergerComplexCharacterGenerator_apply_characterUnitGenerator :
    stickelbergerComplexCharacterGenerator (p := p)
        (((characterUnitGenerator (p := p)) : (ZMod p)ˣ) : ZMod p) =
      stickelbergerComplexCharacterRoot (p := p) := by
  simpa [stickelbergerComplexCharacterGenerator, coe_stickelbergerComplexCharacterRootUnit] using
    (MulChar.ofRootOfUnity_spec (M := ZMod p) (R := ℂ)
      (stickelbergerComplexCharacterRootUnit_mem_rootsOfUnity (p := p))
      (characterUnitGenerator_zpowers (p := p)))

lemma exists_stickelbergerCharacterExponent (χ : DirichletCharacter ℂ p) :
    ∃ j < p - 1,
      stickelbergerComplexCharacterRoot (p := p) ^ j =
        χ (((characterUnitGenerator (p := p)) : (ZMod p)ˣ) : ZMod p) := by
  have hpow : χ ^ (p - 1) = 1 := by
    have h := MulChar.pow_card_eq_one χ (M := ZMod p)
    rwa [ZMod.card_units_eq_totient, Nat.totient_prime hp.out] at h
  have hval_pow :
      χ (((characterUnitGenerator (p := p)) : (ZMod p)ˣ) : ZMod p) ^ (p - 1) = 1 := by
    have h := congrArg
      (fun ψ : DirichletCharacter ℂ p =>
        ψ (((characterUnitGenerator (p := p)) : (ZMod p)ˣ) : ZMod p)) hpow
    simpa [MulChar.pow_apply_coe] using h
  obtain ⟨j, hj_lt, hj_eq⟩ :=
    (stickelbergerComplexCharacterRoot_isPrimitiveRoot (p := p)).eq_pow_of_pow_eq_one hval_pow
  exact ⟨j, hj_lt, hj_eq⟩

noncomputable def stickelbergerCharacterExponent (χ : DirichletCharacter ℂ p) : Fin (p - 1) :=
  ⟨Classical.choose (exists_stickelbergerCharacterExponent (p := p) χ),
    (Classical.choose_spec (exists_stickelbergerCharacterExponent (p := p) χ)).1⟩

lemma stickelbergerCharacterExponent_spec (χ : DirichletCharacter ℂ p) :
    stickelbergerComplexCharacterRoot (p := p) ^
        (stickelbergerCharacterExponent (p := p) χ : ℕ) =
      χ (((characterUnitGenerator (p := p)) : (ZMod p)ˣ) : ZMod p) :=
  (Classical.choose_spec (exists_stickelbergerCharacterExponent (p := p) χ)).2

lemma stickelbergerComplexCharacter_eq_pow (χ : DirichletCharacter ℂ p) :
    stickelbergerComplexCharacterGenerator (p := p) ^
        (stickelbergerCharacterExponent (p := p) χ : ℕ) = χ :=
  (MulChar.eq_iff (g := characterUnitGenerator (p := p))
    (hg := characterUnitGenerator_zpowers (p := p))
    _ _).2 <| by
    rw [MulChar.pow_apply_coe,
      stickelbergerComplexCharacterGenerator_apply_characterUnitGenerator,
      stickelbergerCharacterExponent_spec]

lemma stickelbergerCharacterExponent_stickelbergerComplexCharacterGenerator_pow
    (j : Fin (p - 1)) :
    stickelbergerCharacterExponent (p := p)
        (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)) = j :=
  Fin.ext <| (stickelbergerComplexCharacterRoot_isPrimitiveRoot (p := p)).pow_inj
    (stickelbergerCharacterExponent (p := p)
      (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ))).is_lt
    j.is_lt
    (by
      simpa [MulChar.pow_apply_coe,
        stickelbergerComplexCharacterGenerator_apply_characterUnitGenerator] using
        stickelbergerCharacterExponent_spec (p := p)
          (stickelbergerComplexCharacterGenerator (p := p) ^ (j : ℕ)))

lemma stickelbergerComplexCharacterGenerator_pow_sub_one_eq_one :
    stickelbergerComplexCharacterGenerator (p := p) ^ (p - 1) = 1 :=
  (MulChar.eq_iff (g := characterUnitGenerator (p := p))
    (hg := characterUnitGenerator_zpowers (p := p))
    _ _).2 <| by
      rw [MulChar.pow_apply_coe,
        stickelbergerComplexCharacterGenerator_apply_characterUnitGenerator,
        MulChar.one_apply_coe]
      exact (stickelbergerComplexCharacterRoot_isPrimitiveRoot (p := p)).pow_eq_one

/-- The classical Stickelberger parameter attached to the generator power
`stickelbergerComplexCharacterGenerator ^ j`. Our chosen generator is the
`ω`-convention character, while Washington's Gauss-sum factorization is
written for `ω⁻¹`, so the relevant index is `-j mod (p - 1)`. -/
noncomputable def stickelbergerGeneratorPowerParameter (j : ZMod (p - 1)) : ℕ :=
  (-j).val

lemma stickelbergerGeneratorPowerParameter_lt (j : ZMod (p - 1)) :
    stickelbergerGeneratorPowerParameter (p := p) j < p - 1 := by
  simpa [stickelbergerGeneratorPowerParameter] using ZMod.val_lt (-j)

lemma stickelbergerGeneratorPowerParameter_eq_if
    (j : Fin (p - 1)) :
    stickelbergerGeneratorPowerParameter (p := p) (j : ZMod (p - 1)) =
      if j = 0 then 0 else p - 1 - j := by
  by_cases hj : j = 0
  · subst hj
    simp [stickelbergerGeneratorPowerParameter]
  · have hjz : (j : ZMod (p - 1)) ≠ 0 := by
      intro hz
      apply hj
      apply Fin.ext
      simpa [Nat.mod_eq_of_lt j.is_lt] using
        (ZMod.val_eq_zero (j : ZMod (p - 1))).2 hz
    rw [stickelbergerGeneratorPowerParameter, ZMod.neg_val]
    simp [hj, hjz, Nat.mod_eq_of_lt j.is_lt]

theorem orderOf_characterUnitGenerator :
    orderOf (characterUnitGenerator (p := p)) = p - 1 := by
  calc
    orderOf (characterUnitGenerator (p := p)) = Nat.card ((ZMod p)ˣ) :=
      orderOf_eq_card_of_forall_mem_zpowers (characterUnitGenerator_zpowers (p := p))
    _ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units]

lemma characterUnitGenerator_isPrimitiveRoot :
    IsPrimitiveRoot (characterUnitGenerator (p := p)) (p - 1) := by
  simpa [orderOf_characterUnitGenerator (p := p)] using
    IsPrimitiveRoot.orderOf (characterUnitGenerator (p := p))

theorem characterUnitGenerator_pow_eq_iff_of_lt {m n : ℕ}
    (hm : m < p - 1) (hn : n < p - 1) :
    characterUnitGenerator (p := p) ^ m = characterUnitGenerator (p := p) ^ n ↔ m = n := by
  constructor
  · intro hmn
    have hmod :
        m ≡ n [MOD orderOf (characterUnitGenerator (p := p))] := by
      simpa using
        (pow_eq_pow_iff_modEq (x := characterUnitGenerator (p := p)) (n := m) (m := n)).mp hmn
    have hmod' : m ≡ n [MOD p - 1] := by
      simpa [orderOf_characterUnitGenerator (p := p)] using hmod
    have hEq : m % (p - 1) = n := Nat.mod_eq_of_modEq hmod' hn
    simpa [Nat.mod_eq_of_lt hm] using hEq
  · rintro rfl
    rfl

theorem characterUnitGenerator_pow_bijective :
    Function.Bijective fun m : Fin (p - 1) => characterUnitGenerator (p := p) ^ (m : ℕ) := by
  let f : Fin (p - 1) → (ZMod p)ˣ := fun m => characterUnitGenerator (p := p) ^ (m : ℕ)
  refine (Fintype.bijective_iff_injective_and_card f).mpr ?_
  refine ⟨?_, ?_⟩
  · intro m n hmn
    exact Fin.ext <| (characterUnitGenerator_pow_eq_iff_of_lt (p := p) m.is_lt n.is_lt).mp hmn
  · rw [Fintype.card_fin, ZMod.card_units]

/-- The powers of `characterUnitGenerator` enumerate all units of `ZMod p`. -/
noncomputable def characterUnitGeneratorPowEquiv : Fin (p - 1) ≃ (ZMod p)ˣ :=
  Equiv.ofBijective (fun m : Fin (p - 1) => characterUnitGenerator (p := p) ^ (m : ℕ))
    (characterUnitGenerator_pow_bijective (p := p))

/-- The discrete logarithm of a unit with respect to the chosen generator
`characterUnitGenerator`. -/
noncomputable def characterUnitGeneratorExponent (a : (ZMod p)ˣ) : Fin (p - 1) :=
  (characterUnitGeneratorPowEquiv (p := p)).symm a

lemma characterUnitGenerator_pow_characterUnitGeneratorExponent (a : (ZMod p)ˣ) :
    characterUnitGenerator (p := p) ^
        (characterUnitGeneratorExponent (p := p) a : ℕ) = a :=
  (characterUnitGeneratorPowEquiv (p := p)).apply_symm_apply a

theorem sum_zmod_eq_sum_characterUnitGeneratorPowers
    {R : Type*} [AddCommMonoid R] (F : ZMod p → R) (hF0 : F 0 = 0) :
    ∑ a : ZMod p, F a =
      ∑ m : Fin (p - 1),
        F (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p) := by
  have hsplit :
      ∑ a : ZMod p, F a = F 0 + ∑ a : {a : ZMod p // a ≠ 0}, F a.1 := by
    simpa using Fintype.sum_eq_add_sum_subtype_ne F (0 : ZMod p)
  have hnonzero :
      ∑ a : {a : ZMod p // a ≠ 0}, F a.1 =
        ∑ u : (ZMod p)ˣ, F (u : ZMod p) := by
    simpa using
      (Fintype.sum_equiv unitsEquivNeZero
        (fun u : (ZMod p)ˣ => F (u : ZMod p))
        (fun a : {a : ZMod p // a ≠ 0} => F a.1)
        (fun u => rfl)).symm
  have hpowers :
      ∑ u : (ZMod p)ˣ, F (u : ZMod p) =
        ∑ m : Fin (p - 1),
          F (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p) := by
    simpa using
      (Fintype.sum_equiv (characterUnitGeneratorPowEquiv (p := p))
        (fun m : Fin (p - 1) =>
          F (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p))
        (fun u : (ZMod p)ˣ => F (u : ZMod p))
        (fun m => rfl)).symm
  calc
    ∑ a : ZMod p, F a = F 0 + ∑ a : {a : ZMod p // a ≠ 0}, F a.1 := hsplit
    _ = ∑ a : {a : ZMod p // a ≠ 0}, F a.1 := by rw [hF0, zero_add]
    _ = ∑ u : (ZMod p)ˣ, F (u : ZMod p) := hnonzero
    _ = ∑ m : Fin (p - 1),
          F (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p) := hpowers

lemma stdAddChar_one_eq_stickelbergerAdditiveRoot :
    (ZMod.stdAddChar : AddChar (ZMod p) ℂ) 1 = stickelbergerComplexRoot p ^ (p - 1) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hpm1_ne : ((p - 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.sub_ne_zero_of_lt hp.out.one_lt)
  have h1 : ((1 : ZMod p)) = ((1 : ℤ) : ZMod p) := by norm_cast
  set ζ : ℂ := stickelbergerComplexRoot p with hζ_def
  rw [h1, ZMod.stdAddChar_coe, hζ_def, stickelbergerComplexRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp [hp_ne, hpm1_ne]

lemma stdAddChar_eq_stickelbergerAdditiveRootPow (a : ZMod p) :
    (ZMod.stdAddChar : AddChar (ZMod p) ℂ) a =
      (stickelbergerComplexRoot p ^ (p - 1)) ^ a.val := by
  have h_val : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) a =
      (ZMod.stdAddChar : AddChar (ZMod p) ℂ) 1 ^ a.val := by
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rw [h_val, stdAddChar_one_eq_stickelbergerAdditiveRoot (p := p)]

lemma stdAddChar_mulShift_eq_stickelbergerAdditiveRootPow_mul
    (a x : ZMod p) :
    (ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift a x =
      ((stickelbergerComplexRoot p ^ (p - 1)) ^ a.val) ^ x.val := by
  rw [AddChar.mulShift_apply, stdAddChar_eq_stickelbergerAdditiveRootPow (p := p)]
  conv_rhs => rw [← pow_mul]
  refine pow_eq_pow_of_modEq (x := stickelbergerComplexRoot p ^ (p - 1)) (n := p) ?_ ?_
  · rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, Nat.cast_mul,
      ZMod.natCast_val, ZMod.natCast_val]
    simp
  · calc
      (stickelbergerComplexRoot p ^ (p - 1)) ^ p
          = stickelbergerComplexRoot p ^ ((p - 1) * p) := by rw [pow_mul]
      _ = stickelbergerComplexRoot p ^ (p * (p - 1)) := by
            congr 1
            exact Nat.mul_comm (p - 1) p
      _ = 1 := by
            simpa using (stickelbergerComplexRoot_isPrimitiveRoot (p := p)).pow_eq_one

theorem stickelbergerComplexCharacterGenerator_apply_characterUnitGeneratorPow (m : ℕ) :
    stickelbergerComplexCharacterGenerator (p := p)
        (((characterUnitGenerator (p := p)) ^ m : (ZMod p)ˣ) : ZMod p) =
      stickelbergerComplexCharacterRoot (p := p) ^ m := by
  change stickelbergerComplexCharacterGenerator (p := p)
      ((((characterUnitGenerator (p := p) : (ZMod p)ˣ) : ZMod p) ^ m)) =
    stickelbergerComplexCharacterRoot (p := p) ^ m
  rw [map_pow, stickelbergerComplexCharacterGenerator_apply_characterUnitGenerator]

lemma stickelbergerComplexCharacter_apply_characterUnitGeneratorPow
    (χ : DirichletCharacter ℂ p) (m : ℕ) :
    χ (((characterUnitGenerator (p := p)) ^ m : (ZMod p)ˣ) : ZMod p) =
      stickelbergerComplexCharacterRoot (p := p) ^
        ((stickelbergerCharacterExponent (p := p) χ : ℕ) * m) := by
  let j : ℕ := stickelbergerCharacterExponent (p := p) χ
  have hχ :
      χ = stickelbergerComplexCharacterGenerator (p := p) ^ j := by
    simpa [j] using (stickelbergerComplexCharacter_eq_pow (p := p) χ).symm
  calc
    χ (((characterUnitGenerator (p := p)) ^ m : (ZMod p)ˣ) : ZMod p)
        = (stickelbergerComplexCharacterGenerator (p := p) ^ j)
            (((characterUnitGenerator (p := p)) ^ m : (ZMod p)ˣ) : ZMod p) := by rw [hχ]
    _ = (stickelbergerComplexCharacterRoot (p := p) ^ m) ^ j := by
          rw [MulChar.pow_apply_coe,
            stickelbergerComplexCharacterGenerator_apply_characterUnitGeneratorPow]
    _ = stickelbergerComplexCharacterRoot (p := p) ^ (j * m) := by
          rw [← pow_mul, Nat.mul_comm]
    _ = stickelbergerComplexCharacterRoot (p := p) ^
          ((stickelbergerCharacterExponent (p := p) χ : ℕ) * m) := by
          simp [j]

lemma stickelbergerComplexCharacter_apply_unit
    (χ : DirichletCharacter ℂ p) (a : (ZMod p)ˣ) :
    χ (a : ZMod p) =
      stickelbergerComplexCharacterRoot (p := p) ^
        ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
          (characterUnitGeneratorExponent (p := p) a : ℕ)) := by
  simpa [characterUnitGenerator_pow_characterUnitGeneratorExponent (p := p) a] using
    (stickelbergerComplexCharacter_apply_characterUnitGeneratorPow (p := p) χ
      (characterUnitGeneratorExponent (p := p) a : ℕ))

lemma stickelbergerEmbedding_gaussSumLiftAdditiveRoot :
    stickelbergerEmbedding p L (((gaussSumLiftAdditiveRoot (p := p) L : 𝓞 L) : L)) =
      stickelbergerComplexRoot p ^ (p - 1) := by
  simp [gaussSumLiftAdditiveRoot, stickelbergerZetaInteger, map_pow,
    stickelbergerEmbedding_apply_zeta]

lemma stickelbergerEmbedding_gaussSumLiftCharacterRoot :
    stickelbergerEmbedding p L (((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L)) =
      stickelbergerComplexCharacterRoot (p := p) := by
  simp [gaussSumLiftCharacterRoot, stickelbergerComplexCharacterRoot, stickelbergerZetaInteger,
    map_pow, stickelbergerEmbedding_apply_zeta]

/-- The explicit complex root-expression corresponding to the Gauss sum of `χ`. -/
noncomputable def gaussSumComplexRootSum (χ : DirichletCharacter ℂ p) : ℂ :=
  ∑ m : Fin (p - 1),
    stickelbergerComplexCharacterRoot (p := p) ^
        ((stickelbergerCharacterExponent (p := p) χ : ℕ) * (m : ℕ)) *
      (stickelbergerComplexRoot p ^ (p - 1)) ^
        ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val)

lemma gaussSumComplexRootSum_eq_gaussSum (χ : DirichletCharacter ℂ p) :
    gaussSumComplexRootSum (p := p) χ =
      gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) := by
  have hF0 :
      (fun a : ZMod p => χ a * (ZMod.stdAddChar : AddChar (ZMod p) ℂ) a) 0 = 0 := by
    change χ (0 : ZMod p) * (ZMod.stdAddChar : AddChar (ZMod p) ℂ) 0 = 0
    rw [MulChar.map_nonunit _ (by simp), zero_mul]
  calc
    gaussSumComplexRootSum (p := p) χ
        = ∑ m : Fin (p - 1),
            χ (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p) *
              (ZMod.stdAddChar : AddChar (ZMod p) ℂ)
                ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p)) := by
              unfold gaussSumComplexRootSum
              apply Finset.sum_congr rfl
              intro m _
              rw [stickelbergerComplexCharacter_apply_characterUnitGeneratorPow (p := p),
                stdAddChar_eq_stickelbergerAdditiveRootPow (p := p)]
    _ = ∑ a : ZMod p, χ a * (ZMod.stdAddChar : AddChar (ZMod p) ℂ) a := by
          symm
          exact sum_zmod_eq_sum_characterUnitGeneratorPowers (p := p)
            (F := fun a : ZMod p => χ a * (ZMod.stdAddChar : AddChar (ZMod p) ℂ) a) hF0
    _ = gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) := by
          rfl

/-- The explicit root-expression in the Stickelberger field lifting the Gauss sum of `χ`. -/
noncomputable def gaussSumLiftRootSum (χ : DirichletCharacter ℂ p) : L :=
  ∑ m : Fin (p - 1),
    (((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L) ^
        ((stickelbergerCharacterExponent (p := p) χ : ℕ) * (m : ℕ))) *
      (((gaussSumLiftAdditiveRoot (p := p) L : 𝓞 L) : L) ^
        ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val))

/-- The canonical lift in `𝓞_L` of the complex character value `χ(a)` for a
unit `a : (ZMod p)ˣ`. -/
noncomputable def gaussSumLiftCharacterValue
    (χ : DirichletCharacter ℂ p) (a : (ZMod p)ˣ) : 𝓞 L :=
  gaussSumLiftCharacterRoot (p := p) L ^
    ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
      (characterUnitGeneratorExponent (p := p) a : ℕ))

lemma gaussSumLiftCharacterValue_isUnit
    (χ : DirichletCharacter ℂ p) (a : (ZMod p)ˣ) :
    IsUnit (gaussSumLiftCharacterValue (p := p) (L := L) χ a) := by
  unfold gaussSumLiftCharacterValue
  exact ((gaussSumLiftCharacterRoot_isPrimitiveRoot (p := p) (L := L)).isUnit
    (Nat.sub_ne_zero_of_lt hp.out.one_lt)).pow _

lemma stickelbergerEmbedding_gaussSumLiftCharacterValue
    (χ : DirichletCharacter ℂ p) (a : (ZMod p)ˣ) :
    stickelbergerEmbedding p L
        (((gaussSumLiftCharacterValue (p := p) (L := L) χ a : 𝓞 L) : L)) =
      χ (a : ZMod p) := by
  unfold gaussSumLiftCharacterValue
  calc
    stickelbergerEmbedding p L
        (((gaussSumLiftCharacterRoot (p := p) L ^
            ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
              (characterUnitGeneratorExponent (p := p) a : ℕ)) : 𝓞 L) : L))
        =
        (stickelbergerEmbedding p L (((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L))) ^
          ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
            (characterUnitGeneratorExponent (p := p) a : ℕ)) :=
              map_pow (stickelbergerEmbedding p L)
                (((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L))
                ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
                  (characterUnitGeneratorExponent (p := p) a : ℕ))
    _ = stickelbergerComplexCharacterRoot (p := p) ^
          ((stickelbergerCharacterExponent (p := p) χ : ℕ) *
            (characterUnitGeneratorExponent (p := p) a : ℕ)) := by
          rw [stickelbergerEmbedding_gaussSumLiftCharacterRoot]
    _ = χ (a : ZMod p) :=
          (stickelbergerComplexCharacter_apply_unit (p := p) χ a).symm

lemma stickelbergerEmbedding_gaussSumLiftRootSum (χ : DirichletCharacter ℂ p) :
    stickelbergerEmbedding p L (gaussSumLiftRootSum (p := p) (L := L) χ) =
      gaussSumComplexRootSum (p := p) χ := by
  unfold gaussSumLiftRootSum gaussSumComplexRootSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_mul, map_pow, map_pow,
    stickelbergerEmbedding_gaussSumLiftCharacterRoot (p := p) (L := L),
    stickelbergerEmbedding_gaussSumLiftAdditiveRoot (p := p) (L := L)]

lemma gaussSumLift_eq_gaussSumLiftRootSum (χ : DirichletCharacter ℂ p) :
    gaussSumLift p L χ = gaussSumLiftRootSum (p := p) (L := L) χ := by
  apply (stickelbergerEmbedding p L).injective
  change stickelbergerEmbedding p L (gaussSumLift p L χ) =
      stickelbergerEmbedding p L (gaussSumLiftRootSum (p := p) (L := L) χ)
  rw [stickelbergerEmbedding_gaussSumLift, stickelbergerEmbedding_gaussSumLiftRootSum,
    gaussSumComplexRootSum_eq_gaussSum]

lemma characterSideEmbedding_gaussSumLiftAdditiveRoot (b : (ZMod (p - 1))ˣ) :
    characterSideEmbedding (p := p) (L := L) b
        (((gaussSumLiftAdditiveRoot (p := p) L : 𝓞 L) : L)) =
      stickelbergerComplexRoot p ^ (p - 1) := by
  rw [← stickelbergerEmbedding_comp_sigmaOfCharacterUnit_eq_characterSideEmbedding
    (p := p) (L := L) b]
  change
    stickelbergerEmbedding p L
      (((sigmaOfCharacterUnit (p := p) L b • gaussSumLiftAdditiveRoot (p := p) L : 𝓞 L) : L)) =
      stickelbergerComplexRoot p ^ (p - 1)
  rw [sigmaOfCharacterUnit_smul_gaussSumLiftAdditiveRoot,
    stickelbergerEmbedding_gaussSumLiftAdditiveRoot]

lemma characterSideEmbedding_gaussSumLiftCharacterRoot (b : (ZMod (p - 1))ˣ) :
    characterSideEmbedding (p := p) (L := L) b
        (((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L)) =
      stickelbergerComplexCharacterRoot (p := p) ^ (b : ZMod (p - 1)).val := by
  rw [← stickelbergerEmbedding_comp_sigmaOfCharacterUnit_eq_characterSideEmbedding
    (p := p) (L := L) b]
  change
    stickelbergerEmbedding p L
      (((sigmaOfCharacterUnit (p := p) L b • gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L)) =
      stickelbergerComplexCharacterRoot (p := p) ^ (b : ZMod (p - 1)).val
  rw [sigmaOfCharacterUnit_smul_gaussSumLiftCharacterRoot]
  calc
    stickelbergerEmbedding p L
        (((gaussSumLiftCharacterRoot (p := p) L ^ (b : ZMod (p - 1)).val : 𝓞 L) : L))
        =
        (stickelbergerEmbedding p L
          (((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L))) ^
          (b : ZMod (p - 1)).val :=
            map_pow (stickelbergerEmbedding p L)
                (((gaussSumLiftCharacterRoot (p := p) L : 𝓞 L) : L))
                ((b : ZMod (p - 1)).val)
    _ = stickelbergerComplexCharacterRoot (p := p) ^ (b : ZMod (p - 1)).val := by
          rw [stickelbergerEmbedding_gaussSumLiftCharacterRoot]

lemma characterSideEmbedding_gaussSumLiftRootSum
    (b : (ZMod (p - 1))ˣ) (χ : DirichletCharacter ℂ p) :
    characterSideEmbedding (p := p) (L := L) b
        (gaussSumLiftRootSum (p := p) (L := L) χ) =
      gaussSum (χ ^ (b : ZMod (p - 1)).val) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) := by
  have hF0 :
      (fun a : ZMod p =>
        (χ ^ (b : ZMod (p - 1)).val) a * (ZMod.stdAddChar : AddChar (ZMod p) ℂ) a) 0 = 0 := by
    change
      (χ ^ (b : ZMod (p - 1)).val) (0 : ZMod p) *
        (ZMod.stdAddChar : AddChar (ZMod p) ℂ) 0 = 0
    rw [MulChar.map_nonunit _ (by simp), zero_mul]
  calc
    characterSideEmbedding (p := p) (L := L) b (gaussSumLiftRootSum (p := p) (L := L) χ)
        = ∑ m : Fin (p - 1),
            (χ ^ (b : ZMod (p - 1)).val)
                (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p) *
              (ZMod.stdAddChar : AddChar (ZMod p) ℂ)
                ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p)) := by
              unfold gaussSumLiftRootSum
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro m _
              rw [map_mul, map_pow, map_pow,
                characterSideEmbedding_gaussSumLiftCharacterRoot (p := p) (L := L),
                characterSideEmbedding_gaussSumLiftAdditiveRoot (p := p) (L := L)]
              have hchar :
                  (χ ^ (b : ZMod (p - 1)).val)
                      (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p) =
                    (stickelbergerComplexCharacterRoot (p := p) ^ (b : ZMod (p - 1)).val) ^
                      ((stickelbergerCharacterExponent (p := p) χ : ℕ) * (m : ℕ)) := by
                calc
                  (χ ^ (b : ZMod (p - 1)).val)
                      (((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p)
                      =
                      (stickelbergerComplexCharacterRoot (p := p) ^
                        ((stickelbergerCharacterExponent (p := p) χ : ℕ) * (m : ℕ))) ^
                        (b : ZMod (p - 1)).val := by
                          rw [MulChar.pow_apply_coe]
                          rw [stickelbergerComplexCharacter_apply_characterUnitGeneratorPow
                            (p := p) χ m]
                  _ = stickelbergerComplexCharacterRoot (p := p) ^
                        (((stickelbergerCharacterExponent (p := p) χ : ℕ) * (m : ℕ)) *
                          (b : ZMod (p - 1)).val) := by
                            rw [← pow_mul, pow_mul]
                  _ = stickelbergerComplexCharacterRoot (p := p) ^
                        ((b : ZMod (p - 1)).val *
                          ((stickelbergerCharacterExponent (p := p) χ : ℕ) * (m : ℕ))) := by
                            congr 1
                            simp [Nat.mul_assoc, Nat.mul_comm]
                  _ = (stickelbergerComplexCharacterRoot (p := p) ^ (b : ZMod (p - 1)).val) ^
                        ((stickelbergerCharacterExponent (p := p) χ : ℕ) * (m : ℕ)) := by
                            rw [pow_mul]
              rw [← hchar, ← stdAddChar_eq_stickelbergerAdditiveRootPow (p := p)
                ((((characterUnitGenerator (p := p)) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p))]
    _ = ∑ a : ZMod p,
          (χ ^ (b : ZMod (p - 1)).val) a * (ZMod.stdAddChar : AddChar (ZMod p) ℂ) a := by
          symm
          exact sum_zmod_eq_sum_characterUnitGeneratorPowers (p := p)
            (F := fun a : ZMod p =>
              (χ ^ (b : ZMod (p - 1)).val) a * (ZMod.stdAddChar : AddChar (ZMod p) ℂ) a) hF0
    _ = gaussSum (χ ^ (b : ZMod (p - 1)).val) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) := by
          rfl

lemma characterSideEmbedding_gaussSumLift
    (b : (ZMod (p - 1))ˣ) (χ : DirichletCharacter ℂ p) :
    characterSideEmbedding (p := p) (L := L) b (gaussSumLift p L χ) =
      gaussSum (χ ^ (b : ZMod (p - 1)).val) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) := by
  rw [gaussSumLift_eq_gaussSumLiftRootSum (p := p) (L := L),
    characterSideEmbedding_gaussSumLiftRootSum (p := p) (L := L)]

end GaloisAction

end BernoulliRegular
