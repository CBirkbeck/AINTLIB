/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.TateModule.InverseSystem
import HasseWeil.WeilPairing.PairingNondeg

/-!
# `E[ℓⁿ] ≅ (ZMod ℓⁿ)²` — the `ℓⁿ`-torsion is free of rank 2 (Silverman III.6.4(c) at `m = ℓⁿ`)

For `ℓ` prime, `F` algebraically closed with `(ℓ : F) ≠ 0`, the `ℓⁿ`-torsion
`E[ℓⁿ] = W.toAffine[((ℓ^n : ℕ) : ℤ)]` is a free `ZMod (ℓⁿ)`-module of rank 2. Over the
**non-field** ring `ZMod (ℓⁿ)` the cardinality `(ℓⁿ)²` alone does *not* pin the module type, so
the proof proceeds by **coherent induction on `n`** from the field case `E[ℓ] ≅ (ZMod ℓ)²`
(`torsion_ell_linearEquiv`), using that the connecting map `tateConn n = [ℓ] : E[ℓⁿ⁺¹] → E[ℓⁿ]`
is surjective.

## Coherence (for the Tate-limit step L10)

The basis sequence `tateBasis n : Basis (Fin 2) (ZMod (ℓⁿ)) E[ℓⁿ]` is built **coherently**: the
level-`(n+1)` basis vectors are *lifts* of the level-`n` ones along `[ℓ]`, so
`tateConn n (tateBasis (n+1) i) = tateBasis n i` holds **by construction**
(`tateConn_tateBasis`). This makes the square
```
E[ℓⁿ⁺¹] --tateBasis--> (ZMod ℓⁿ⁺¹)²
   | [ℓ]                    | castHom
E[ℓⁿ]   --tateBasis--> (ZMod ℓⁿ)²
```
commute, which is exactly the naturality the inverse-limit isomorphism `T_ℓ(E) ≅ ℤ_ℓ²` (L10)
needs. **L4's induction is therefore coherent / L10-ready.**

Main results:
* `tateConn_surjective` (L7) — the connecting maps are surjective;
* `tateBasis n` + `tateConn_tateBasis` (L4, coherent) — the coherent `ZMod (ℓⁿ)`-basis;
* `torsion_ellPow_linearEquiv` (L4) — `E[ℓⁿ] ≃ₗ[ZMod ℓⁿ] (Fin 2 → ZMod ℓⁿ)`;
* `torsion_ellPow_free`, `finrank_torsion_ellPow` — freeness and rank 2.

Reference: Silverman, *The Arithmetic of Elliptic Curves* (2nd ed), §III.7 (Prop 7.1) and
p. 87 (the cyclic-group decomposition `#E[pᵉ] = pᵉ`), III.6.4(b,c).
-/

open WeierstrassCurve

namespace HasseWeil.TateModule

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric
open scoped HasseWeil.WeilPairing.TorsionGeometric

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓF : (ℓ : F) ≠ 0)

include hℓF

section Cardinality

omit hℓ in
/-- `#E[ℓⁿ] = (ℓⁿ)²` as a `Nat.card` equality (no `ℤ`-coercion). -/
theorem card_torsion_ellPow_nat (n : ℕ) :
    Nat.card W.toAffine[((ℓ ^ n : ℕ) : ℤ)] = (ℓ ^ n) ^ 2 := by
  have h := card_torsion_ellPow W ℓ hℓF n
  exact_mod_cast h

/-- `E[ℓⁿ]` is finite. -/
theorem torsion_ellPow_finite (n : ℕ) : Finite W.toAffine[((ℓ ^ n : ℕ) : ℤ)] := by
  apply Nat.finite_of_card_ne_zero
  rw [card_torsion_ellPow_nat W ℓ hℓF n]
  have : ℓ ≠ 0 := hℓ.out.pos.ne'
  positivity

end Cardinality

section Surjective

omit hℓ in
/-- **L7.** The connecting map `tateConn n = [ℓ] : E[ℓⁿ⁺¹] → E[ℓⁿ]` is surjective. Multiplication
by `ℓ` is surjective on all of `E(K̄)` (`mulByInt_point_surjective`, `(ℓ : F) ≠ 0`); a preimage of
`Q ∈ E[ℓⁿ]` lies in `E[ℓⁿ⁺¹]` because `ℓⁿ⁺¹ · P = ℓⁿ · (ℓ · P) = ℓⁿ · Q = 0`. -/
theorem tateConn_surjective (n : ℕ) : Function.Surjective (tateConn W ℓ n) := by
  intro Q
  -- `[ℓ]` is surjective on `E(K̄)`; choose a preimage `P₀` of `Q.val`.
  obtain ⟨P₀, hP₀⟩ := HasseWeil.WeilPairing.mulByInt_point_surjective W (ℓ : ℤ)
    (by exact_mod_cast hℓF) (Q : W.toAffine.Point)
  rw [mulByInt_apply] at hP₀
  -- `P₀ ∈ E[ℓⁿ⁺¹]` because `ℓⁿ⁺¹ · P₀ = ℓⁿ · (ℓ · P₀) = ℓⁿ · Q = 0`.
  have hmem : P₀ ∈ W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)] := by
    rw [mem_torsionSubgroup]
    have hQ : ((ℓ ^ n : ℕ) : ℤ) • (Q : W.toAffine.Point) = 0 := by
      have := Q.property; rwa [mem_torsionSubgroup] at this
    have hcast : ((ℓ ^ n : ℕ) : ℤ) * (ℓ : ℤ) = ((ℓ ^ (n + 1) : ℕ) : ℤ) := by
      push_cast; ring
    have hsplit : ((ℓ ^ (n + 1) : ℕ) : ℤ) • P₀ = ((ℓ ^ n : ℕ) : ℤ) • ((ℓ : ℤ) • P₀) := by
      rw [smul_smul, hcast]
    rw [hsplit, hP₀, hQ]
  refine ⟨⟨P₀, hmem⟩, ?_⟩
  apply Subtype.ext
  rw [tateConn_coe]
  exact hP₀

end Surjective

section TorsionSmul

omit [IsAlgClosed F] hℓ hℓF in
/-- The `ℓⁿ`-multiple map `ℓⁿ • · : E[ℓⁿ⁺¹] → E[ℓⁿ⁺¹]` as an `AddMonoidHom` (the subgroup
`E[ℓⁿ⁺¹]` is closed under the integer action). Its range is the `ℓ`-torsion of `E[ℓⁿ⁺¹]`. -/
noncomputable def smulPow (n : ℕ) :
    W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)] →+ W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)] :=
  ((zsmulAddGroupHom ((ℓ ^ n : ℕ) : ℤ)).comp
    (W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)]).subtype).codRestrict _
    (fun P => by
      rw [mem_torsionSubgroup]
      have hP : ((ℓ ^ (n + 1) : ℕ) : ℤ) • (P : W.toAffine.Point) = 0 := by
        have := P.property; rwa [mem_torsionSubgroup] at this
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype,
        zsmulAddGroupHom_apply]
      rw [smul_smul, mul_comm, ← smul_smul, hP, smul_zero])

omit [IsAlgClosed F] hℓ hℓF in
@[simp] theorem smulPow_coe (n : ℕ) (P : W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)]) :
    (smulPow W ℓ n P : W.toAffine.Point) = ((ℓ ^ n : ℕ) : ℤ) • (P : W.toAffine.Point) :=
  rfl

omit hℓ in
/-- The kernel of `ℓⁿ • · : E[ℓⁿ⁺¹] → E[ℓⁿ⁺¹]` has cardinality `(ℓⁿ)²` (it consists of the
`ℓⁿ`-torsion points, which all already lie in `E[ℓⁿ⁺¹]`). -/
theorem card_ker_smulPow (n : ℕ) :
    Nat.card (smulPow W ℓ n).ker = (ℓ ^ n) ^ 2 := by
  rw [← card_torsion_ellPow_nat W ℓ hℓF n]
  -- `ker (smulPow n) ≃ E[ℓⁿ]` via `⟨⟨P, _⟩, ℓⁿ•P = 0⟩ ↦ ⟨P, ℓⁿ•P = 0⟩`.
  apply Nat.card_congr
  refine
    { toFun := fun P => ⟨(P.val : W.toAffine.Point), ?_⟩
      invFun := fun P => ⟨⟨(P.val : W.toAffine.Point), ?_⟩, ?_⟩
      left_inv := fun P => by ext; rfl
      right_inv := fun P => by ext; rfl }
  · -- `P.val.val ∈ E[ℓⁿ]`: from `smulPow n P.val = 0`.
    have hk : smulPow W ℓ n P.val = 0 := P.property
    rw [mem_torsionSubgroup]
    have : ((smulPow W ℓ n P.val : W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)]) :
        W.toAffine.Point) = 0 := by rw [hk]; rfl
    rwa [smulPow_coe] at this
  · -- `P.val ∈ E[ℓⁿ⁺¹]`: from `P.val ∈ E[ℓⁿ]` (ℓⁿ•P=0 ⟹ ℓⁿ⁺¹•P=0).
    have hP : ((ℓ ^ n : ℕ) : ℤ) • (P : W.toAffine.Point) = 0 := by
      have := P.property; rwa [mem_torsionSubgroup] at this
    rw [mem_torsionSubgroup]
    have hcast : (ℓ : ℤ) * ((ℓ ^ n : ℕ) : ℤ) = ((ℓ ^ (n + 1) : ℕ) : ℤ) := by push_cast; ring
    have hsplit : ((ℓ ^ (n + 1) : ℕ) : ℤ) • (P : W.toAffine.Point)
        = (ℓ : ℤ) • (((ℓ ^ n : ℕ) : ℤ) • (P : W.toAffine.Point)) := by
      rw [smul_smul, hcast]
    rw [hsplit, hP, smul_zero]
  · -- membership in `ker (smulPow n)`.
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    rw [smulPow_coe, ZeroMemClass.coe_zero]
    have := P.property; rwa [mem_torsionSubgroup] at this

omit hℓ in
/-- The `ℓ`-torsion subgroup of `E[ℓⁿ⁺¹]` (the kernel of `tateConn`) has cardinality `ℓ²` — it is
the image of `E[ℓ]` inside `E[ℓⁿ⁺¹]`. -/
theorem card_ker_tateConn (n : ℕ) :
    Nat.card (tateConn W ℓ n).ker = ℓ ^ 2 := by
  rw [← card_torsion_ell_nat W ℓ hℓF]
  -- `ker (tateConn n) ≃ E[ℓ]` via `⟨⟨P, _⟩, ℓ•P = 0⟩ ↦ ⟨P, ℓ•P = 0⟩`.
  apply Nat.card_congr
  refine
    { toFun := fun P => ⟨(P.val : W.toAffine.Point), ?_⟩
      invFun := fun P => ⟨⟨(P.val : W.toAffine.Point), ?_⟩, ?_⟩
      left_inv := fun P => by ext; rfl
      right_inv := fun P => by ext; rfl }
  · -- `P.val.val ∈ E[ℓ]`: from `tateConn n P.val = 0`.
    have hk : tateConn W ℓ n P.val = 0 := P.property
    rw [mem_torsionSubgroup]
    have : ((tateConn W ℓ n P.val : W.toAffine[((ℓ ^ n : ℕ) : ℤ)]) :
        W.toAffine.Point) = 0 := by rw [hk]; rfl
    rwa [tateConn_coe] at this
  · -- `P.val ∈ E[ℓⁿ⁺¹]`: from `P.val ∈ E[ℓ]` (ℓ•P=0 ⟹ ℓⁿ⁺¹•P=0).
    have hP : (ℓ : ℤ) • (P : W.toAffine.Point) = 0 := by
      have := P.property; rwa [mem_torsionSubgroup] at this
    rw [mem_torsionSubgroup]
    have hcast : ((ℓ ^ n : ℕ) : ℤ) * (ℓ : ℤ) = ((ℓ ^ (n + 1) : ℕ) : ℤ) := by push_cast; ring
    have hsplit : ((ℓ ^ (n + 1) : ℕ) : ℤ) • (P : W.toAffine.Point)
        = ((ℓ ^ n : ℕ) : ℤ) • ((ℓ : ℤ) • (P : W.toAffine.Point)) := by
      rw [smul_smul, hcast]
    rw [hsplit, hP, smul_zero]
  · -- membership in `ker (tateConn n)`.
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    rw [tateConn_coe, ZeroMemClass.coe_zero]
    have := P.property; rwa [mem_torsionSubgroup] at this

/-- **Key structural fact** (`E[ℓ] = ℓⁿ · E[ℓⁿ⁺¹]`). The range of `ℓⁿ • ·` on `E[ℓⁿ⁺¹]` is exactly
the `ℓ`-torsion `ker (tateConn n)`: it is contained in it (`ℓ · ℓⁿ · P = ℓⁿ⁺¹ · P = 0`), and both
have cardinality `ℓ²`. -/
theorem range_smulPow_eq_ker_tateConn (n : ℕ) :
    (smulPow W ℓ n).range = (tateConn W ℓ n).ker := by
  haveI : Finite W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)] := torsion_ellPow_finite W ℓ hℓF (n + 1)
  -- `range ⊆ ker`: `ℓ · (ℓⁿ · P) = ℓⁿ⁺¹ · P = 0`.
  have hle : (smulPow W ℓ n).range ≤ (tateConn W ℓ n).ker := by
    rintro _ ⟨P, rfl⟩
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    rw [tateConn_coe, smulPow_coe, ZeroMemClass.coe_zero, smul_smul]
    have hP : ((ℓ ^ (n + 1) : ℕ) : ℤ) • (P : W.toAffine.Point) = 0 := by
      have := P.property; rwa [mem_torsionSubgroup] at this
    have hcast : (ℓ : ℤ) * ((ℓ ^ n : ℕ) : ℤ) = ((ℓ ^ (n + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, hP]
  -- Cardinality: `#range = #domain / #ker(smulPow) = (ℓⁿ⁺¹)² / (ℓⁿ)² = ℓ²`.
  have hcard_range : Nat.card (smulPow W ℓ n).range = ℓ ^ 2 := by
    have hformula : Nat.card (smulPow W ℓ n).range * Nat.card (smulPow W ℓ n).ker
        = Nat.card W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)] := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (smulPow W ℓ n).ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (smulPow W ℓ n)).toEquiv]
    rw [card_ker_smulPow W ℓ hℓF n, card_torsion_ellPow_nat W ℓ hℓF (n + 1)] at hformula
    -- `#range * (ℓⁿ)² = (ℓⁿ⁺¹)²`; cancel to get `#range = ℓ²`.
    have hpos : 0 < (ℓ ^ n) ^ 2 := by
      have : ℓ ≠ 0 := hℓ.out.pos.ne'; positivity
    have heq : Nat.card (smulPow W ℓ n).range * (ℓ ^ n) ^ 2 = ℓ ^ 2 * (ℓ ^ n) ^ 2 := by
      rw [hformula]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos heq
  -- subset + equal card ⟹ equal.
  exact AddSubgroup.eq_of_le_of_card_ge hle
    (by rw [hcard_range, card_ker_tateConn W ℓ hℓF n])

end TorsionSmul

section CoherentBasis

omit [IsAlgClosed F] hℓ hℓF in
/-- The connecting map `[ℓ]` applied to a linear combination of the lifts `c` equals the
corresponding linear combination of the level-`n` basis vectors, with `ZMod (ℓⁿ)`-reduced
coefficients (a consequence of L6 semilinearity and `tateConn (c i) = b i`). -/
theorem tateConn_linearCombination_lift (n : ℕ)
    (b : Module.Basis (Fin 2) (ZMod (ℓ ^ n)) W.toAffine[((ℓ ^ n : ℕ) : ℤ)])
    (c : Fin 2 → W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)])
    (hc : ∀ i, tateConn W ℓ n (c i) = b i) (v : Fin 2 → ZMod (ℓ ^ (n + 1))) :
    tateConn W ℓ n (Fintype.linearCombination (ZMod (ℓ ^ (n + 1))) c v) =
      Fintype.linearCombination (ZMod (ℓ ^ n)) b
        (fun i => ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ ^ n)) (v i)) := by
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tateConn_castHom_compat, hc]

/-- Given a basis `b` of `E[ℓⁿ]` (with `n ≥ 1`) and a lifted family `c i ∈ E[ℓⁿ⁺¹]` with
`tateConn (c i) = b i`, the linear-combination map `(Fin 2 → ZMod ℓⁿ⁺¹) → E[ℓⁿ⁺¹]`,
`v ↦ Σ vᵢ • cᵢ`, is surjective.

Proof outline (Silverman's "product of cyclic groups", p. 87): the composite `[ℓ] ∘ g` is
surjective (it factors through the bijective `Σ aᵢ • bᵢ` after reducing coefficients mod `ℓⁿ`,
and `castHom` is surjective); and the `ℓ`-torsion kernel of `[ℓ]` is contained in the range of
`g` because it equals `ℓⁿ · E[ℓⁿ⁺¹]` (`range_smulPow_eq_ker_tateConn`) and `ℓⁿ` annihilates that
torsion (using `n ≥ 1`). A point `P` differs from a `g`-value by an element of that kernel, hence
lies in the range. -/
theorem linearCombination_lift_surjective (n : ℕ) (hn : 1 ≤ n)
    (b : Module.Basis (Fin 2) (ZMod (ℓ ^ n)) W.toAffine[((ℓ ^ n : ℕ) : ℤ)])
    (c : Fin 2 → W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)])
    (hc : ∀ i, tateConn W ℓ n (c i) = b i) :
    Function.Surjective (Fintype.linearCombination (ZMod (ℓ ^ (n + 1))) c) := by
  set g := Fintype.linearCombination (ZMod (ℓ ^ (n + 1))) c with hg
  -- Step 1: `tateConn ∘ g` is surjective.
  have htc_surj : Function.Surjective (fun v => tateConn W ℓ n (g v)) := by
    intro Q
    -- lift the coordinates of `Q` in the basis `b` to `ZMod ℓⁿ⁺¹`.
    refine ⟨fun i => Classical.choose
      (ZMod.castHom_surjective (m := ℓ ^ n) (n := ℓ ^ (n + 1)) (pow_dvd_pow ℓ n.le_succ)
        (b.equivFun Q i)), ?_⟩
    show tateConn W ℓ n (g _) = Q
    rw [hg, tateConn_linearCombination_lift W ℓ n b c hc]
    have hlift : ∀ i, ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ ^ n))
        (Classical.choose (ZMod.castHom_surjective (m := ℓ ^ n) (n := ℓ ^ (n + 1))
          (pow_dvd_pow ℓ n.le_succ) (b.equivFun Q i))) = b.equivFun Q i :=
      fun i => Classical.choose_spec (ZMod.castHom_surjective (m := ℓ ^ n) (n := ℓ ^ (n + 1))
        (pow_dvd_pow ℓ n.le_succ) (b.equivFun Q i))
    simp_rw [hlift]
    rw [Fintype.linearCombination_apply]
    exact b.sum_equivFun Q
  -- A reusable form: `ℓⁿ` annihilates the `ℓ`-torsion (kernel of `tateConn`), since `n ≥ 1`.
  have hpow_kill : ∀ x : W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)],
      (ℓ : ℤ) • x = 0 → ((ℓ ^ n : ℕ) : ℤ) • x = 0 := by
    intro x hx
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    have hcast : ((ℓ ^ n : ℕ) : ℤ) = ((ℓ ^ k : ℕ) : ℤ) * (ℓ : ℤ) := by
      rw [hk, pow_add, pow_one]; push_cast; ring
    rw [hcast, ← smul_smul, hx, smul_zero]
  -- Step 2: `ker (tateConn) ⊆ range g`.
  have hker_sub : ∀ R ∈ (tateConn W ℓ n).ker, R ∈ Set.range g := by
    intro R hR
    -- `R ∈ ker tateConn = range smulPow`, so `R = ℓⁿ • S`.
    rw [← range_smulPow_eq_ker_tateConn W ℓ hℓF n] at hR
    obtain ⟨S, hS⟩ := hR
    -- `tateConn S` is a `tateConn ∘ g` value: `∃ w, tateConn (g w) = tateConn S`.
    obtain ⟨w, hw⟩ := htc_surj (tateConn W ℓ n S)
    simp only at hw
    -- `S - g w ∈ ker tateConn`, killed by `ℓ`, hence by `ℓⁿ` (n ≥ 1).
    have hℓkill : (ℓ : ℤ) • (S - g w) = 0 := by
      have hker0 : tateConn W ℓ n (S - g w) = 0 := by rw [map_sub, hw, sub_self]
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero]
      have hc0 : ((tateConn W ℓ n (S - g w) : W.toAffine[((ℓ ^ n : ℕ) : ℤ)]) :
          W.toAffine.Point) = 0 := by rw [hker0]; rfl
      rwa [tateConn_coe] at hc0
    have hkill : ((ℓ ^ n : ℕ) : ℤ) • (S - g w) = 0 := hpow_kill _ hℓkill
    -- `R = ℓⁿ • S = ℓⁿ • (g w) = g (ℓⁿ • w) ∈ range g`.
    refine ⟨((ℓ ^ n : ℕ) : ℤ) • w, ?_⟩
    have hRsmul : R = ((ℓ ^ n : ℕ) : ℤ) • S := by
      rw [← hS]; apply Subtype.ext; rw [smulPow_coe, AddSubgroup.coe_zsmul]
    have hsplit : ((ℓ ^ n : ℕ) : ℤ) • S = ((ℓ ^ n : ℕ) : ℤ) • (g w) := by
      rw [smul_sub] at hkill; exact sub_eq_zero.mp hkill
    rw [map_zsmul, hRsmul, hsplit]
  -- Combine: any `P` differs from a `g`-value by a kernel element, which is in `range g`.
  intro P
  obtain ⟨v, hv⟩ := htc_surj (tateConn W ℓ n P)
  simp only at hv
  have hPdiff : P - g v ∈ (tateConn W ℓ n).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, hv, sub_self]
  obtain ⟨u, hu⟩ := hker_sub (P - g v) hPdiff
  refine ⟨v + u, ?_⟩
  rw [map_add, hu, add_sub_cancel]

omit [IsAlgClosed F] hℓ hℓF in
/-- `E[ℓ⁰] = E[1]` is trivial (only the zero point has `1`-torsion). -/
theorem subsingleton_torsion_ellPow_zero :
    Subsingleton W.toAffine[((ℓ ^ 0 : ℕ) : ℤ)] := by
  constructor
  rintro P Q
  apply Subtype.ext
  have hP : ((ℓ ^ 0 : ℕ) : ℤ) • (P : W.toAffine.Point) = 0 := by
    have := P.property; rwa [mem_torsionSubgroup] at this
  have hQ : ((ℓ ^ 0 : ℕ) : ℤ) • (Q : W.toAffine.Point) = 0 := by
    have := Q.property; rwa [mem_torsionSubgroup] at this
  simp only [pow_zero, Nat.cast_one, one_smul] at hP hQ
  rw [hP, hQ]

/-- **L4 base case `n = 0`.** The trivial basis of `E[ℓ⁰] = E[1] = ⊥` over the trivial ring
`ZMod (ℓ⁰) = ZMod 1`. -/
noncomputable def tateBasisZero :
    Module.Basis (Fin 2) (ZMod (ℓ ^ 0)) W.toAffine[((ℓ ^ 0 : ℕ) : ℤ)] := by
  haveI : Subsingleton (ZMod (ℓ ^ 0)) := by rw [pow_zero]; infer_instance
  haveI hs : Subsingleton W.toAffine[((ℓ ^ 0 : ℕ) : ℤ)] := subsingleton_torsion_ellPow_zero W ℓ
  -- both `E[1]` and `Fin 2 → ZMod 1` are subsingletons; the zero map is bijective.
  exact Module.Basis.ofEquivFun (LinearEquiv.ofBijective
    (0 : W.toAffine[((ℓ ^ 0 : ℕ) : ℤ)] →ₗ[ZMod (ℓ ^ 0)] (Fin 2 → ZMod (ℓ ^ 0)))
    ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩)

/-- **L4 base case `n = 1`.** The field-theoretic basis of `E[ℓ¹]` over `ZMod (ℓ¹)`. Since
`ℓ¹ = ℓ` is prime, `ZMod (ℓ¹)` is a field and `#E[ℓ¹] = (ℓ¹)²` forces `finrank = 2`
(`Module.natCard_eq_pow_finrank`), as in the `n = 1` case `finrank_torsion_ell`. -/
noncomputable def tateBasisOne :
    Module.Basis (Fin 2) (ZMod (ℓ ^ 1)) W.toAffine[((ℓ ^ 1 : ℕ) : ℤ)] := by
  haveI : Fact ((ℓ ^ 1).Prime) := ⟨by rw [pow_one]; exact hℓ.out⟩
  haveI : Finite W.toAffine[((ℓ ^ 1 : ℕ) : ℤ)] := torsion_ellPow_finite W ℓ hℓF 1
  have hrank : Module.finrank (ZMod (ℓ ^ 1)) W.toAffine[((ℓ ^ 1 : ℕ) : ℤ)] = 2 := by
    have hcard : Nat.card W.toAffine[((ℓ ^ 1 : ℕ) : ℤ)]
        = Nat.card (ZMod (ℓ ^ 1)) ^ Module.finrank (ZMod (ℓ ^ 1)) W.toAffine[((ℓ ^ 1 : ℕ) : ℤ)] :=
      Module.natCard_eq_pow_finrank
    rw [card_torsion_ellPow_nat W ℓ hℓF 1] at hcard
    have hZcard : Nat.card (ZMod (ℓ ^ 1)) = ℓ ^ 1 := by
      haveI : NeZero (ℓ ^ 1) := ⟨by have : ℓ ≠ 0 := hℓ.out.pos.ne'; positivity⟩
      rw [Nat.card_eq_fintype_card, ZMod.card]
    rw [hZcard] at hcard
    exact (Nat.pow_right_injective (by rw [pow_one]; exact hℓ.out.two_le) hcard).symm
  exact Module.finBasisOfFinrankEq (ZMod (ℓ ^ 1)) W.toAffine[((ℓ ^ 1 : ℕ) : ℤ)] hrank

omit [DecidableEq F] [IsAlgClosed F] hℓF in
/-- The cardinality of `Fin 2 → ZMod (ℓⁿ)` is `(ℓⁿ)²`, matching `#E[ℓⁿ]`. -/
theorem card_fin_two_zmod (n : ℕ) : Nat.card (Fin 2 → ZMod (ℓ ^ n)) = (ℓ ^ n) ^ 2 := by
  haveI : NeZero (ℓ ^ n) := ⟨by have : ℓ ≠ 0 := hℓ.out.pos.ne'; positivity⟩
  rw [Nat.card_eq_fintype_card]
  simp [ZMod.card]

/-- **The lift step of L4's induction** (`n ≥ 1` packaged as `n+1`). Given a basis `b` of
`E[ℓⁿ⁺¹]`, produce a basis of `E[ℓⁿ⁺²]` whose vectors are `[ℓ]`-lifts of the `b i`. Surjectivity of
the linear-combination map (`linearCombination_lift_surjective`) plus equal cardinality
(`#E[ℓⁿ⁺²] = (ℓⁿ⁺²)² = #(Fin 2 → ZMod ℓⁿ⁺²)`) makes that map bijective, giving the basis; the lift
property is recorded for coherence (`tateConn (b' i) = b i`). -/
noncomputable def liftBasisData (n : ℕ)
    (b : Module.Basis (Fin 2) (ZMod (ℓ ^ (n + 1))) W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)]) :
    { b' : Module.Basis (Fin 2) (ZMod (ℓ ^ (n + 2))) W.toAffine[((ℓ ^ (n + 2) : ℕ) : ℤ)] //
        ∀ i, tateConn W ℓ (n + 1) (b' i) = b i } := by
  haveI : Finite W.toAffine[((ℓ ^ (n + 2) : ℕ) : ℤ)] := torsion_ellPow_finite W ℓ hℓF (n + 2)
  -- lifts `c i` of `b i` along the surjective `tateConn`.
  choose c hc using fun i => tateConn_surjective W ℓ hℓF (n + 1) (b i)
  -- the linear-combination map is surjective, hence bijective (equal finite cardinality).
  have hsurj : Function.Surjective (Fintype.linearCombination (ZMod (ℓ ^ (n + 2))) c) :=
    linearCombination_lift_surjective W ℓ hℓF (n + 1) (Nat.le_add_left 1 n) b c hc
  have hbij : Function.Bijective (Fintype.linearCombination (ZMod (ℓ ^ (n + 2))) c) := by
    apply hsurj.bijective_of_nat_card_le
    rw [card_fin_two_zmod ℓ (n + 2), card_torsion_ellPow_nat W ℓ hℓF (n + 2)]
  -- package as a basis via `ofEquivFun` of the inverse equivalence.
  refine ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ hbij).symm, fun i => ?_⟩
  -- `b' i = c i`, and `tateConn (c i) = b i`.
  have hbi : (Module.Basis.ofEquivFun (LinearEquiv.ofBijective
      (Fintype.linearCombination (ZMod (ℓ ^ (n + 2))) c) hbij).symm) i = c i := by
    rw [Module.Basis.coe_ofEquivFun]
    simp only [LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply]
    rw [Fintype.linearCombination_apply_single, one_smul]
  rw [hbi, hc]

/-- **L4 (coherent).** A coherent sequence of `ZMod (ℓⁿ)`-bases of `E[ℓⁿ]`. The level-`0` basis is
the (trivial) basis of `E[1] = ⊥`; the level-`1` basis is the field-theoretic basis
`torsion_ell_basis`; and for `n ≥ 1` the level-`(n+1)` basis vectors are `[ℓ]`-lifts of the level-`n`
ones (`liftBasisData`), so `tateConn (tateBasis (n+1) i) = tateBasis n i` holds by construction (see
`tateConn_tateBasis`). This coherence is what the Tate-limit step (L10) needs. -/
noncomputable def tateBasis :
    (n : ℕ) → Module.Basis (Fin 2) (ZMod (ℓ ^ n)) W.toAffine[((ℓ ^ n : ℕ) : ℤ)]
  | 0 => tateBasisZero W ℓ
  | 1 => tateBasisOne W ℓ hℓF
  | n + 2 => (liftBasisData W ℓ hℓF n (tateBasis (n + 1))).1

/-- **Coherence of `tateBasis`** (L10-ready): the connecting map `[ℓ]` sends each level-`(n+1)`
basis vector to the corresponding level-`n` basis vector. -/
theorem tateConn_tateBasis (n : ℕ) (i : Fin 2) :
    tateConn W ℓ n (tateBasis W ℓ hℓF (n + 1) i) = tateBasis W ℓ hℓF n i := by
  match n with
  | 0 =>
    -- both sides live in the trivial group `E[ℓ⁰] = E[1]`.
    haveI := subsingleton_torsion_ellPow_zero W ℓ
    exact Subsingleton.elim _ _
  | n + 1 =>
    -- `tateBasis (n+2)` is the lift of `tateBasis (n+1)`; coherence is its defining property.
    exact (liftBasisData W ℓ hℓF n (tateBasis W ℓ hℓF (n + 1))).2 i

end CoherentBasis

section Structure

/-- **L4.** `E[ℓⁿ] ≅ (ZMod ℓⁿ)²` as `ZMod (ℓⁿ)`-modules, via the coherent basis `tateBasis`. -/
noncomputable def torsion_ellPow_linearEquiv (n : ℕ) :
    W.toAffine[((ℓ ^ n : ℕ) : ℤ)] ≃ₗ[ZMod (ℓ ^ n)] (Fin 2 → ZMod (ℓ ^ n)) :=
  (tateBasis W ℓ hℓF n).equivFun

/-- `E[ℓⁿ]` is a free `ZMod (ℓⁿ)`-module. -/
theorem torsion_ellPow_free (n : ℕ) :
    Module.Free (ZMod (ℓ ^ n)) W.toAffine[((ℓ ^ n : ℕ) : ℤ)] :=
  Module.Free.of_basis (tateBasis W ℓ hℓF n)

/-- `finrank (ZMod ℓⁿ) E[ℓⁿ] = 2` for `n ≥ 1`. (At `n = 0` the coefficient ring `ZMod 1` is trivial
and `finrank` is degenerate, so the rank-`2` statement is only meaningful for `n ≥ 1`.) -/
theorem finrank_torsion_ellPow {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank (ZMod (ℓ ^ n)) W.toAffine[((ℓ ^ n : ℕ) : ℤ)] = 2 := by
  haveI : Nontrivial (ZMod (ℓ ^ n)) := by
    haveI : Fact (1 < ℓ ^ n) := ⟨by
      calc 1 < ℓ := hℓ.out.one_lt
        _ = ℓ ^ 1 := (pow_one ℓ).symm
        _ ≤ ℓ ^ n := Nat.pow_le_pow_right hℓ.out.pos hn⟩
    infer_instance
  rw [Module.finrank_eq_card_basis (tateBasis W ℓ hℓF n), Fintype.card_fin]

end Structure

end HasseWeil.TateModule
