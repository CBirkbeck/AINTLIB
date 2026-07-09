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
    rw [show (baseChangeAssoc R A ρ C').symm
        ((Algebra.TensorProduct.map (AlgHom.id C' C') (coactionOverCoinvariants ρ)) x)
        = coactionBaseChange R A ρ C' x from rfl, ← baseChangeAssoc_tmul_one,
      AlgEquiv.symm_apply_apply] at h2
    exact h2

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
    have key : ∀ y : C' ⊗[coinvariants ρ] (AlgHom.equalizer (coactionOverCoinvariants ρ)
        (includeLeftOverCoinvariants ρ)),
        ∃ c' : C', c' ⊗ₜ[coinvariants ρ] (1 : B)
          = (Algebra.TensorProduct.map (AlgHom.id C' C')
              (AlgHom.equalizer (coactionOverCoinvariants ρ)
                (includeLeftOverCoinvariants ρ)).val) y := by
      intro y
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
    obtain ⟨c', hc'⟩ := key y
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

end IsCoactionTransport

end ModularCurves
