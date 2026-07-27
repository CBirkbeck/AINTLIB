/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.HopfGalois
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Base change of a co-action along the co-invariants

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-B3]`; Stacks
`groupoids-lemma-invariants-base-change`, tag 03BK): for a co-action `ρ : B → B ⊗[R] A`
with co-invariants `C := coinvariants ρ` and a `C`-algebra `C'`, the co-action base
changes to `ρ' : C' ⊗[C] B → (C' ⊗[C] B) ⊗[R] A` — `ρ` is `C`-linear
(`coactionOverCoinvariants`), so `id_{C'} ⊗ ρ` makes sense, reassociated through the
heterobasic `Algebra.TensorProduct.assoc`.

* `coactionBaseChange` — the base-changed co-action `ρ'`;
* `coactionBaseChange_tmul` — `ρ'(c' ⊗ b) = (c' ⊗ b₍₀₎) ⊗ b₍₁₎` on expansions;
* (later increments) `IsCoaction (coactionBaseChange …)`, and — the 03BK(3) content —
  for **flat** `C → C'` the co-invariants of `ρ'` are exactly the image of `C'`
  (`AlgHom.tensorEqualizerEquiv`).

This is the gadget the `[HG-B6]` bootstrap uses at each localized invariant ring: base
change along `C → (LocalPolynomialExtension (Localization.AtPrime p))` preserves the
co-invariants, so the semi-local heart (03C1 + 03C8) applies upstairs and its conclusions
descend.
-/

open scoped TensorProduct

namespace ModularCurves

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]
variable {B : Type*} [CommRing B] [Algebra R B]
variable (ρ : B →ₐ[R] B ⊗[R] A)
variable (C' : Type*) [CommRing C'] [Algebra R C']
variable [Algebra (coinvariants ρ) C'] [IsScalarTower R (coinvariants ρ) C']

/-- The heterobasic associator specialized to the base-change situation:
`(C' ⊗[C] B) ⊗[R] A ≃ C' ⊗[C] (B ⊗[R] A)`. -/
noncomputable def baseChangeAssoc :
    ((C' ⊗[coinvariants ρ] B) ⊗[R] A) ≃ₐ[C'] C' ⊗[coinvariants ρ] (B ⊗[R] A) :=
  Algebra.TensorProduct.assoc R (coinvariants ρ) C' C' B A

/-- **The base-changed co-action**: `ρ' : C' ⊗[C] B → (C' ⊗[C] B) ⊗[R] A`, the map
`id_{C'} ⊗ ρ` (using the `C`-linearity of `ρ`) reassociated. -/
noncomputable def coactionBaseChange :
    (C' ⊗[coinvariants ρ] B) →ₐ[R] (C' ⊗[coinvariants ρ] B) ⊗[R] A :=
  ((baseChangeAssoc R A ρ C').symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id C' C') (coactionOverCoinvariants ρ))).restrictScalars R

@[simp]
theorem coactionBaseChange_tmul (c' : C') (b : B) :
    coactionBaseChange R A ρ C' (c' ⊗ₜ[coinvariants ρ] b)
      = (baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] ρ b) := rfl

/-- The associator carries the ambient left inclusion to `id ⊗ includeLeftOverCoinvariants`,
pointwise. -/
theorem baseChangeAssoc_tmul_one (x : C' ⊗[coinvariants ρ] B) :
    baseChangeAssoc R A ρ C' (x ⊗ₜ[R] (1 : A))
      = (Algebra.TensorProduct.map (AlgHom.id C' C')
          (includeLeftOverCoinvariants ρ)) x := by
  induction x with
  | zero => simp [TensorProduct.zero_tmul]
  | tmul c' b =>
    show (Algebra.TensorProduct.assoc R (coinvariants ρ) C' C' B A)
        ((c' ⊗ₜ[coinvariants ρ] b) ⊗ₜ[R] (1 : A))
      = (Algebra.TensorProduct.map (AlgHom.id C' C') (includeLeftOverCoinvariants ρ))
          (c' ⊗ₜ[coinvariants ρ] b)
    rw [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  | add x y ihx ihy =>
    rw [TensorProduct.add_tmul, map_add, ihx, ihy, map_add]

/-- Membership in the equalizer of the base-changed pair, in terms of the original data. -/
theorem coactionBaseChange_eq_includeLeft_iff (x : C' ⊗[coinvariants ρ] B) :
    coactionBaseChange R A ρ C' x = x ⊗ₜ[R] (1 : A)
      ↔ (Algebra.TensorProduct.map (AlgHom.id C' C') (coactionOverCoinvariants ρ)) x
        = (Algebra.TensorProduct.map (AlgHom.id C' C')
            (includeLeftOverCoinvariants ρ)) x := by
  constructor
  · intro h
    have h2 := congrArg (baseChangeAssoc R A ρ C') h
    rwa [show (baseChangeAssoc R A ρ C') (coactionBaseChange R A ρ C' x)
        = (Algebra.TensorProduct.map (AlgHom.id C' C') (coactionOverCoinvariants ρ)) x from
      (baseChangeAssoc R A ρ C').apply_symm_apply _, baseChangeAssoc_tmul_one] at h2
  · intro h
    have h2 := congrArg (baseChangeAssoc R A ρ C').symm h
    rwa [show (baseChangeAssoc R A ρ C').symm
        ((Algebra.TensorProduct.map (AlgHom.id C' C') (coactionOverCoinvariants ρ)) x)
        = coactionBaseChange R A ρ C' x from rfl, ← baseChangeAssoc_tmul_one,
      AlgEquiv.symm_apply_apply] at h2

omit [Algebra R C'] [IsScalarTower R (↥(coinvariants ρ)) C'] in
/-- Every element of `C' ⊗_{C^ρ} (equalizer of the two coactions)` has the form `c' ⊗ₜ 1`
(the equalizer of `coactionOverCoinvariants`/`includeLeftOverCoinvariants` is the scalars
`C^ρ`, so its tensor entries are absorbed into the `C'` factor). The induction core of the
forward direction of `mem_coinvariants_coactionBaseChange_iff`. -/
private theorem exists_tmul_one_eq_map_equalizer_val
    (y : C' ⊗[coinvariants ρ] (AlgHom.equalizer (coactionOverCoinvariants ρ)
      (includeLeftOverCoinvariants ρ))) :
    ∃ c' : C', c' ⊗ₜ[coinvariants ρ] (1 : B)
      = (Algebra.TensorProduct.map (AlgHom.id C' C')
          (AlgHom.equalizer (coactionOverCoinvariants ρ)
            (includeLeftOverCoinvariants ρ)).val) y := by
  induction y with
  | zero => exact ⟨0, by rw [map_zero, TensorProduct.zero_tmul]⟩
  | tmul c' e =>
    have he : (e : B) ∈ coinvariants ρ := by
      have h2 := e.2
      rw [AlgHom.mem_equalizer] at h2
      rw [mem_coinvariants]
      exact h2
    refine ⟨(⟨(e : B), he⟩ : coinvariants ρ) • c', ?_⟩
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def, mul_one]
    rfl
  | add y z ihy ihz =>
    obtain ⟨cy, hcy⟩ := ihy
    obtain ⟨cz, hcz⟩ := ihz
    exact ⟨cy + cz, by rw [map_add, ← hcy, ← hcz, TensorProduct.add_tmul]⟩

/-- **03BK(3), comodule form**: for a *flat* base change `C → C'` of the co-invariants, the
co-invariants of the base-changed co-action are exactly the scalars `C'`. -/
theorem mem_coinvariants_coactionBaseChange_iff [Module.Flat (coinvariants ρ) C']
    (x : C' ⊗[coinvariants ρ] B) :
    x ∈ coinvariants (coactionBaseChange R A ρ C')
      ↔ ∃ c' : C', c' ⊗ₜ[coinvariants ρ] (1 : B) = x := by
  classical
  constructor
  · intro hx
    rw [mem_coinvariants, coactionBaseChange_eq_includeLeft_iff] at hx
    -- x is in the equalizer of the base-changed pair; flat base change of equalizers
    have hxmem : x ∈ AlgHom.equalizer
        (Algebra.TensorProduct.map (AlgHom.id C' C') (coactionOverCoinvariants ρ))
        (Algebra.TensorProduct.map (AlgHom.id C' C')
          (includeLeftOverCoinvariants ρ)) := hx
    obtain ⟨y, hy⟩ := (AlgHom.tensorEqualizerEquiv C' C'
      (coactionOverCoinvariants ρ) (includeLeftOverCoinvariants ρ)).surjective ⟨x, hxmem⟩
    have hyx : (Algebra.TensorProduct.map (AlgHom.id C' C')
        (AlgHom.equalizer (coactionOverCoinvariants ρ)
          (includeLeftOverCoinvariants ρ)).val) y = x := by
      have := congrArg Subtype.val hy
      rwa [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer] at this
    clear hy
    obtain ⟨c', hc'⟩ := exists_tmul_one_eq_map_equalizer_val R A ρ C' y
    exact ⟨c', hc'.trans hyx⟩
  · rintro ⟨c', rfl⟩
    rw [mem_coinvariants]
    rw [show coactionBaseChange R A ρ C' (c' ⊗ₜ[coinvariants ρ] (1 : B))
        = (baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] ρ 1) from rfl, map_one]
    rw [show (c' ⊗ₜ[coinvariants ρ] (1 : B ⊗[R] A))
        = c' ⊗ₜ[coinvariants ρ] ((1 : B) ⊗ₜ[R] (1 : A)) from by
      rw [Algebra.TensorProduct.one_def]]
    rw [show (baseChangeAssoc R A ρ C').symm
        (c' ⊗ₜ[coinvariants ρ] ((1 : B) ⊗ₜ[R] (1 : A)))
        = (c' ⊗ₜ[coinvariants ρ] (1 : B)) ⊗ₜ[R] (1 : A) from
      Algebra.TensorProduct.assoc_symm_tmul _ _ _ _ _ _]

section IsCoactionTransport

/-- Auxiliary contraction: the counit leg computed through the associator. -/
private theorem rid_map_counit_baseChangeAssoc_symm (c' : C') (z : B ⊗[R] A) :
    (Algebra.TensorProduct.rid R R (C' ⊗[coinvariants ρ] B))
      ((Algebra.TensorProduct.map (AlgHom.id R (C' ⊗[coinvariants ρ] B))
        (Bialgebra.counitAlgHom R A))
        ((baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] z)))
      = c' ⊗ₜ[coinvariants ρ]
          ((Algebra.TensorProduct.rid R R B)
            ((Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.counitAlgHom R A)) z)) := by
  induction z with
  | zero => simp [TensorProduct.tmul_zero]
  | tmul b a =>
    rw [show (baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] (b ⊗ₜ[R] a))
        = (c' ⊗ₜ[coinvariants ρ] b) ⊗ₜ[R] a from
      Algebra.TensorProduct.assoc_symm_tmul _ _ _ _ _ _]
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.rid_tmul, Algebra.TensorProduct.rid_tmul]
    rw [AlgHom.coe_id, id_eq, AlgHom.coe_id, id_eq, TensorProduct.tmul_smul]
  | add z w ihz ihw =>
    rw [TensorProduct.tmul_add, map_add, map_add, map_add, ihz, ihw, map_add, map_add,
      TensorProduct.tmul_add]

/-- The counit law transports to the base change. -/
theorem coactionBaseChange_counit (hρ : IsCoaction ρ) :
    (Algebra.TensorProduct.rid R R (C' ⊗[coinvariants ρ] B)).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R (C' ⊗[coinvariants ρ] B))
        (Bialgebra.counitAlgHom R A)).comp (coactionBaseChange R A ρ C'))
      = AlgHom.id R (C' ⊗[coinvariants ρ] B) := by
  refine AlgHom.ext fun x => ?_
  induction x with
  | zero => simp
  | tmul c' b =>
    show (Algebra.TensorProduct.rid R R (C' ⊗[coinvariants ρ] B))
        ((Algebra.TensorProduct.map (AlgHom.id R (C' ⊗[coinvariants ρ] B))
          (Bialgebra.counitAlgHom R A))
          ((baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] ρ b)))
      = c' ⊗ₜ[coinvariants ρ] b
    rw [rid_map_counit_baseChangeAssoc_symm, hρ.counit_apply]
  | add x y ihx ihy =>
    simp only [AlgHom.comp_apply] at ihx ihy ⊢
    rw [map_add, map_add, map_add, ihx, ihy]
    simp

/-- The graft `w ↦ c' ⊗ w` on the `B`-leg, tensored with the identity on `A ⊗ A`: the
common transport both coassociativity legs factor through. -/
private noncomputable def graftMap (c' : C') :
    B ⊗[R] (A ⊗[R] A) →ₗ[R] (C' ⊗[coinvariants ρ] B) ⊗[R] (A ⊗[R] A) :=
  LinearMap.rTensor (A ⊗[R] A)
    (((TensorProduct.mk (coinvariants ρ) C' B) c').restrictScalars R)

private theorem graftMap_tmul (c' : C') (b : B) (w : A ⊗[R] A) :
    graftMap R A ρ C' c' (b ⊗ₜ[R] w) = (c' ⊗ₜ[coinvariants ρ] b) ⊗ₜ[R] w := rfl

/-- Inner aux: the two associators against the graft, on a pure trailing leg. -/
private theorem assoc_baseChangeAssoc_symm_tmul (c' : C') (w : B ⊗[R] A) (a : A) :
    (Algebra.TensorProduct.assoc R R R (C' ⊗[coinvariants ρ] B) A A)
        (((baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] w)) ⊗ₜ[R] a)
      = graftMap R A ρ C' c'
          ((TensorProduct.assoc R B A A) (w ⊗ₜ[R] a)) := by
  induction w with
  | zero => simp [TensorProduct.zero_tmul, graftMap]
  | tmul b' a'' =>
    rw [show (baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] (b' ⊗ₜ[R] a''))
        = (c' ⊗ₜ[coinvariants ρ] b') ⊗ₜ[R] a'' from
      Algebra.TensorProduct.assoc_symm_tmul _ _ _ _ _ _]
    rw [show (TensorProduct.assoc R B A A) ((b' ⊗ₜ[R] a'') ⊗ₜ[R] a)
        = b' ⊗ₜ[R] (a'' ⊗ₜ[R] a) from TensorProduct.assoc_tmul _ _ _]
    rw [graftMap_tmul]
    exact Algebra.TensorProduct.assoc_tmul _ _ _ _ _ _
  | add w₁ w₂ ih₁ ih₂ =>
    rw [TensorProduct.tmul_add, map_add, TensorProduct.add_tmul, map_add, ih₁, ih₂,
      TensorProduct.add_tmul, map_add, map_add]

/-- Left coassociativity leg, transported: `assoc ∘ (map ρ' id) ∘ bca.symm ∘ (c' ⊗ ·)`
equals the graft of `assoc ∘ (map ρ id)`. -/
private theorem assoc_map_coactionBaseChange (c' : C') (z : B ⊗[R] A) :
    (Algebra.TensorProduct.assoc R R R (C' ⊗[coinvariants ρ] B) A A)
        ((Algebra.TensorProduct.map (coactionBaseChange R A ρ C') (AlgHom.id R A))
          ((baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] z)))
      = graftMap R A ρ C' c'
          ((TensorProduct.assoc R B A A)
            ((Algebra.TensorProduct.map ρ (AlgHom.id R A)) z)) := by
  induction z with
  | zero => simp [graftMap]
  | tmul b₀ a =>
    rw [show (baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] (b₀ ⊗ₜ[R] a))
        = (c' ⊗ₜ[coinvariants ρ] b₀) ⊗ₜ[R] a from
      Algebra.TensorProduct.assoc_symm_tmul _ _ _ _ _ _,
      Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rw [show (coactionBaseChange R A ρ C') (c' ⊗ₜ[coinvariants ρ] b₀)
        = (baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] ρ b₀) from rfl]
    exact assoc_baseChangeAssoc_symm_tmul R A ρ C' c' (ρ b₀) a
  | add z₁ z₂ ih₁ ih₂ =>
    rw [TensorProduct.tmul_add, map_add, map_add, map_add, ih₁, ih₂, map_add, map_add,
      map_add]

/-- Right coassociativity leg, transported: `(map id Δ) ∘ bca.symm ∘ (c' ⊗ ·)` equals the
graft of `map id Δ`. -/
private theorem map_comul_baseChangeAssoc_symm (c' : C') (z : B ⊗[R] A) :
    (Algebra.TensorProduct.map (AlgHom.id R (C' ⊗[coinvariants ρ] B))
        (Bialgebra.comulAlgHom R A))
        ((baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] z))
      = graftMap R A ρ C' c'
          ((Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.comulAlgHom R A)) z) := by
  induction z with
  | zero => simp [graftMap]
  | tmul b₀ a =>
    rw [show (baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] (b₀ ⊗ₜ[R] a))
        = (c' ⊗ₜ[coinvariants ρ] b₀) ⊗ₜ[R] a from
      Algebra.TensorProduct.assoc_symm_tmul _ _ _ _ _ _,
      Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, AlgHom.coe_id, id_eq, graftMap_tmul]
  | add z₁ z₂ ih₁ ih₂ =>
    rw [TensorProduct.tmul_add, map_add, map_add, ih₁, ih₂, map_add, map_add]

/-- The coassociativity law transports to the base change. -/
theorem coactionBaseChange_coassoc (hρ : IsCoaction ρ) :
    (Algebra.TensorProduct.assoc R R R (C' ⊗[coinvariants ρ] B) A A).toAlgHom.comp
      ((Algebra.TensorProduct.map (coactionBaseChange R A ρ C') (AlgHom.id R A)).comp
        (coactionBaseChange R A ρ C'))
      = (Algebra.TensorProduct.map (AlgHom.id R (C' ⊗[coinvariants ρ] B))
          (Bialgebra.comulAlgHom R A)).comp (coactionBaseChange R A ρ C') := by
  refine AlgHom.ext fun x => ?_
  induction x with
  | zero => simp
  | tmul c' b =>
    show (Algebra.TensorProduct.assoc R R R (C' ⊗[coinvariants ρ] B) A A)
        ((Algebra.TensorProduct.map (coactionBaseChange R A ρ C') (AlgHom.id R A))
          ((baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] ρ b)))
      = (Algebra.TensorProduct.map (AlgHom.id R (C' ⊗[coinvariants ρ] B))
          (Bialgebra.comulAlgHom R A))
          ((baseChangeAssoc R A ρ C').symm (c' ⊗ₜ[coinvariants ρ] ρ b))
    rw [assoc_map_coactionBaseChange, map_comul_baseChangeAssoc_symm]
    congr 1
    exact hρ.coassoc_apply b
  | add x y ihx ihy =>
    simp only [AlgHom.comp_apply] at ihx ihy ⊢
    rw [map_add, map_add, map_add, map_add, ihx, ihy]

/-- **The base-changed co-action is a co-action.** -/
theorem isCoaction_coactionBaseChange (hρ : IsCoaction ρ) :
    IsCoaction (coactionBaseChange R A ρ C') where
  counit := coactionBaseChange_counit R A ρ C' hρ
  coassoc := coactionBaseChange_coassoc R A ρ C' hρ

end IsCoactionTransport

end ModularCurves
