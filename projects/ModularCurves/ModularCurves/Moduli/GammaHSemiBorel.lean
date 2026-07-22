/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.Moduli.GammaHMaster
import ModularCurves.Moduli.KeystoneGeometricPoint

/-!
# Γ_H rigidity for semi-Borel level subgroups, and the Borel no-go

**KM 7.4.2(3) (print p. 198, verbatim):** "The natural map `[Γ(N)] → [Γ₁(N)]`,
`(P,Q) ↦ P` identifies `[Γ₁(N)]` with the quotient of `[Γ(N)]` by the "semi-Borel"
sub-group `(1 *; 0 *)` of `GL(2, ℤ/Nℤ)`."

**Loeffler, Prop 3.8.3 (verbatim):** "`𝒫_H` is rigid on `Ell/R[1/6]` if and only if
the preimage in `SL₂(ℤ)` of `H ∩ SL₂(ℤ/N)` contains no elements of finite order
(i.e. has no elliptic points and does not contain `−1`)."

This file supplies the honest per-`H` rigidity input of `gammaH_rigidNoeth` — the
k̄-orbit-freeness `hfree` — for every `H` contained in the semi-Borel subgroup
`{(1 *; 0 *)}` (the stabilizer of the first basis vector), `N ≥ 4` invertible: a
`γ`-twisted fixed point forces the base-identical iso `e` to fix the *first* section
of the naive full level structure (the first column of `γ` is `e₁`), that section has
exact order `N` over `k̄`, and the PROVEN exact-order keystone
(`aut_endo_eq_one_of_fixes_point`, with `hbound` discharged by `hbound_of_kvc` exactly
as in the Γ₁ closure) forces `e = refl`. For such `H` the preimage of
`H ∩ SL₂(ℤ/N)` is (conjugate into) `Γ₁(N)`, torsion-free for `N ≥ 4` — the Loeffler
3.8.3 condition holds, and `P_H` is representable through the KM 4.7.0 engine.

**The Borel no-go (v10.345-AMEND §A).** For `H` containing `−1` — the Borel
`{(* *; 0 *)}` of `[Γ₀(N)]` in particular — rigidity FAILS (Loeffler 3.8.3: `−1` is a
finite-order element of the preimage), and the former `hH` finite-order pin of
`gammaH_representable_of_orderOf` is refutable inside the library: `e := negIso` is a
nontrivial base-identical iso with `isoPow e 2 = refl`, and `orderOf (−1) = 2`. The
`hH_refuted_of_neg_one_mem` witness below records this no-go as a theorem so that no
future worker attempts a fine `Y₀(N)` through the `orderOf` interface. `Y₀(N)` is the
KM Ch. 8 *coarse* moduli scheme (KM 8.1.5: `M(𝒫)/G ≅ M(𝒫/G)`; Loeffler Def 3.6.2:
`Y₀(N) = Y₁(N)/(ℤ/N)ˣ`) — a separate stream (M3).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable (R : CommRingCat.{u})

/-! ## The semi-Borel subgroup -/

/-- The **semi-Borel subgroup** `{(1 *; 0 *)} ≤ GL₂(ℤ/N)` (KM 7.4.2(3)): matrices
whose first column is `e₁`. Under the `glSmul` right-action convention
(`g • (P,Q) = (g₀₀P + g₁₀Q, g₀₁P + g₁₁Q)`) these are exactly the elements fixing the
first component of every full level structure. `[Γ(N)]`-quotient by it = `[Γ₁(N)]`
(KM 7.4.2(3)). -/
def semiBorel (N : ℕ) [NeZero N] :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0 = 1 ∧
    (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry

/-- Membership in the semi-Borel subgroup, unfolded. -/
theorem mem_semiBorel_iff (N : ℕ) [NeZero N]
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    g ∈ semiBorel N ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 :=
  Iff.rfl

/-! ## Semi-Borel matrices fix the first component of a full level structure -/

variable {S : Scheme.{u}}

/-- A semi-Borel matrix fixes the first component of every full level structure:
`(glSmul g L).1.1 = (1.val : ℤ) • L.1.1 + (0.val : ℤ) • L.1.2 = L.1.1` (needs
`1 < N` so that `(1 : ZMod N).val = 1`). -/
theorem EllipticCurve.glSmul_fst_of_mem_semiBorel (E : EllipticCurve S) {N : ℕ}
    [NeZero N] (hN : 1 < N) (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (hg : g ∈ semiBorel N) (L : E.FullLevelPt N) :
    (E.glSmul g L).1.1 = L.1.1 := by
  sorry

/-- **The untwist + first-component extraction**: a `γ`-twisted fixed point of the
naive full-level problem under a base-identical iso `e`, for `γ ∈ H ≤ semi-Borel`,
forces `e` to fix the first section of the structure:
`(gammaHAut γ).app (map e.op b) = b` untwists (via `gammaHAut_app_val` and
`glSmul_mul`) to `map e.op b = glSmul γ b`, whose first components read
`pullSection e b.1.1 = b.1.1`. Mirror of the untwist in
`gammaH_hfree_of_orderOf_absurd` + the `h1`-extraction of
`gammaFullNaive_twist_pow_refl`. -/
theorem gammaFullNaive_fix_fst_of_le_semiBorel (N : ℕ) [NeZero N] (hN : 1 < N)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hle : H ≤ semiBorel N)
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (γ : ↥H)
    (hcon : (gammaHAut R N H γ).hom.app
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
      ((gammaFullNaiveProblem R N).map e.hom.op b) = b) :
    EllHom.pullSection R e.hom b.1.1 = b.1.1 := by
  sorry

/-- Over `k̄` with `N` invertible, the first section of a naive full level structure
has exact order `N`: its small multiples are nonzero. (The structure pins a basis of
`E[N](k̄) ≅ (ℤ/N)²` — the [GH2-core] geometric-fibre machinery
(`torsion_geometricFibre_rank_two`); a basis vector of `(ℤ/N)²` has additive order
`N`.) -/
theorem gammaFullNaive_fst_smul_ne_zero (N : ℕ) [NeZero N]
    (hinv : IsUnit (N : R))
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (a : ℕ) (ha0 : 0 < a) (haN : a < N) :
    (a : ℤ) • b.1.1 ≠ 0 := by
  sorry

/-- **The naive-side one-section rigidity kill** (the `gammaOneDrinfeld_fix_absurd`
endgame on the naive full-level problem): over `k̄`, `N ≥ 4` invertible, a
base-identical iso `e ≠ refl` cannot fix a section of exact order `N`. Route: `e`
transports to a pointed endomorphism `εO` of `E.asOver` (invertible since `e` is an
iso), the fixed section is `εO`-fixed, its small multiples are nonzero
(`gammaFullNaive_fst_smul_ne_zero`), and the PROVEN keystone
`aut_endo_eq_one_of_fixes_point` — `hbound` discharged by `hbound_of_kvc` exactly as
in the Γ₁ closure (`gammaOneDrinfeld_rigid_and_representable`) — forces `εO = 𝟙`,
hence `e.hom.top = 𝟙` and `e = refl`. -/
theorem gammaFullNaive_fix_fst_absurd (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R))
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (he : e.hom.baseHom = 𝟙 _) (hne : e ≠ Iso.refl _)
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (hfix : EllHom.pullSection R e.hom b.1.1 = b.1.1) : False := by
  sorry

/-! ## The hfree pin for `H ≤ semiBorel`, and the closure -/

/-- **[Γ_H hfree, semi-Borel] (the rectified Gate 2)** — the `hfree` pin of
`gammaH_rigidNoeth` holds for every `H` contained in the semi-Borel subgroup,
`N ≥ 4` invertible: assembly of `gammaFullNaive_fix_fst_of_le_semiBorel` +
`gammaFullNaive_fix_fst_absurd`. -/
theorem gammaH_hfree_of_le_semiBorel (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hle : H ≤ semiBorel N)
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (he : e.hom.baseHom = 𝟙 _) (hne : e ≠ Iso.refl _)
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (γ : ↥H) :
    (gammaHAut R N H γ).hom.app
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
      ((gammaFullNaiveProblem R N).map e.hom.op b) ≠ b := by
  sorry

/-- **[Γ_H rigidity, semi-Borel, noetherian-local]** — `P_H` is noetherian-locally
rigid for every `H ≤ semiBorel N`, `N ≥ 4` invertible, UNCONDITIONALLY (no `hH`/`hfree`
pin left): `gammaH_rigidNoeth` fed by `gammaH_hfree_of_le_semiBorel`. -/
theorem gammaH_rigidNoeth_of_le_semiBorel (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hle : H ≤ semiBorel N)
    (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H)) :
    qpd.prob.RigidNoeth := by
  sorry

/-- **[Γ_H `.Representable`, semi-Borel] (KM 7.4.2(3)-adjacent; the first
unconditional representable `Y_H` beyond `H = ⊥`)** — for `H ≤ semiBorel N`,
`N ≥ 4` invertible, the quotient problem `P_H` is representable: relative
representability and affineness from `qpd`, rigidity from
`gammaH_rigidNoeth_of_le_semiBorel`, through the KM 4.7.0 engine (mirror of
`gammaH_representable_of_orderOf` with the honest rigidity input). With the
M1-unconditional `gammaH_relativelyRepresentable` this closes `Y_H(N)` for every
semi-Borel `H`; by KM 7.4.2(3) the `H = semiBorel` quotient is `[Γ₁(N)]` itself. -/
theorem gammaH_representable_of_le_semiBorel (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hle : H ≤ semiBorel N)
    (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H)) :
    qpd.prob.Representable := by
  sorry

/-- **[Y_H HEADLINE, semi-Borel] (KM 7.4.2(3)-grade)** — for `N ≥ 4` invertible and any
`H ≤ semiBorel N`, the quotient problem data exists UNCONDITIONALLY (M1's
diagonal-free `gammaH_relativelyRepresentable`) and every such quotient problem is
representable (`gammaH_representable_of_le_semiBorel`). The first unconditional
`Y_H(N)` beyond `H = ⊥`; at `H = semiBorel N` the quotient is `[Γ₁(N)]` itself
(KM 7.4.2(3)). -/
theorem gammaH_semiBorel_closure (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hle : H ≤ semiBorel N)
    (hinv : IsUnit (N : R)) :
    Nonempty (ModuliProblem.QuotientProblemData (gammaHAut R N H)) ∧
      ∀ qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H),
        qpd.prob.Representable := by
  sorry

/-! ## The Borel no-go: the `orderOf` pin is refutable for `−1 ∈ H` -/

/-- `−1` has order two in `GL₂(ℤ/N)` for `N ≥ 3`. -/
theorem orderOf_neg_one_gl (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    orderOf (-1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = 2 := by
  sorry

/-- The square of the negation iso is the identity (already `negHom_comp_negHom`,
iterated through `isoPow`). -/
theorem isoPow_negIso_two (X : EllObj R) :
    isoPow (EllObj.negIso R X) 2 = Iso.refl X := by
  sorry

/-- Over a base with a geometric point, the negation iso is not the identity
(T-H7c `mulByHom_neg_one_ne_id`, lifted to the `Ell/R`-iso). -/
theorem negIso_ne_refl (X : EllObj R) (k : Type u) [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ X.base) :
    EllObj.negIso R X ≠ Iso.refl X := by
  sorry

/-- **THE BOREL NO-GO (v10.345-AMEND §A, as a theorem)** — for any `H` containing
`−1` (the Borel of `[Γ₀(N)]` in particular) and any geometric test object, the
former `hH` finite-order pin of `gammaH_representable_of_orderOf` is FALSE: the
negation iso is a nontrivial base-identical iso with
`isoPow e (orderOf γ) = refl` at `γ = −1`. Classical content: Loeffler Prop 3.8.3
(verbatim: rigid ⟺ the `SL₂(ℤ)`-preimage of `H ∩ SL₂(ℤ/N)` "has no elliptic points
and does not contain `−1`"); `[Γ₀(N)]` is a quotient problem (KM 7.4.2(4)) whose
moduli scheme is COARSE (KM 8.1). Do NOT attempt a fine `Y₀(N)` through the
`orderOf` interface. -/
theorem hH_refuted_of_neg_one_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hmem : (-1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) ∈ H)
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k))) :
    ∃ (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
        (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)),
      e.hom.baseHom = 𝟙 _ ∧ e ≠ Iso.refl _ ∧ ∃ γ : ↥H,
        isoPow e (orderOf ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))) =
          Iso.refl _ := by
  sorry

end ModularCurves
