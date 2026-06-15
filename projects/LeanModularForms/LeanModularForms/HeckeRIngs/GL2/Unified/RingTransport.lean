/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp

/-!
# Transport of Hecke-operator identities from the ring `𝕋(Γ₀(N))`

This file completes the ring-first architecture: the structural identities of the
classical Hecke operators `T_n` on `M_k(Γ₁(N))` — pairwise commutativity, coprime
multiplicativity, commutation with the diamond operators — are **derived from the
commutative Hecke ring** `𝕋 (Gamma0_pair N) ℤ` (commutativity: Shimura Prop 3.8 via the
Atkin–Lehner anti-involution; multiplicativity: the ring-side identities of
`Gamma0RingDn`), transported along the character-space ring homomorphisms
`heckeRingHomCharSpace` and glued over the Nebentypus decomposition by
`ModularForm_Gamma1_endo_ext`.

The pipeline:
1. `chiAllU χ n` — the good-part character scalar `∏_{p ∤ N} χ(p)^{v_p(n)}` as a *unit*,
   assembled by the same generic `peelProd` as the ring elements, so its coprime
   multiplicativity is the generic `peelProd_mul_coprime`.
2. `heckeRingHomCharSpace_heckeRingDn_all` — the **extended composite bridge**: for every
   positive `n` (bad primes included),
   `Φ_χ(D_n) = (chiAllU χ n)⁻¹ • (T_n restricted to M_k(N,χ))`.
3. The endomorphism-level identities on each `M_k(N,χ)` follow from ring identities by
   applying `Φ_χ`; the full-space identities follow by gluing.

The headline outputs `heckeT_n_comm_ring`, `heckeT_n_mul_coprime_ring`,
`heckeT_n_comm_diamondOp_all` replace the former self-contained induction cascades.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn
open HeckeRing
open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- The good-part character value `∏_{p ∤ N} χ(p)^{v_p(n)}`, as a unit of `ℂ`.
Assembled by the generic `peelProd`, so that coprime multiplicativity and prime-power
evaluation come from the generic lemmas. -/
noncomputable def chiAllU (χ : (ZMod N)ˣ →* ℂˣ) (n : ℕ) : ℂˣ :=
  peelProd (R := ℂˣ)
    (fun p v ↦ if h : Nat.Coprime p N then (χ (ZMod.unitOfCoprime p h)) ^ v else 1) n

@[simp] theorem chiAllU_one (χ : (ZMod N)ˣ →* ℂˣ) : chiAllU χ 1 = 1 := peelProd_one _

theorem chiAllU_mul_coprime (χ : (ZMod N)ˣ →* ℂˣ) (m n : ℕ) (hmn : Nat.Coprime m n) :
    chiAllU χ (m * n) = chiAllU χ m * chiAllU χ n :=
  peelProd_mul_coprime _ m n hmn

theorem chiAllU_ppow_good (χ : (ZMod N)ˣ →* ℂˣ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (v : ℕ) (hv : 0 < v) :
    chiAllU χ (p ^ v) = (χ (ZMod.unitOfCoprime p hpN)) ^ v := by
  rw [chiAllU, peelProd_ppow _ hp v hv, dif_pos hpN]

/-- `heckeT_ppow k p hp r` restricted to `modFormCharSpace k χ`, for **every** prime `p`
(including `p ∣ N`). -/
noncomputable def heckeT_ppow_charRestrictAll (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (r : ℕ)
    (χ : (ZMod N)ˣ →* ℂˣ) : Module.End ℂ (modFormCharSpace k χ) where
  toFun f :=
    ⟨heckeT_ppow k p hp r (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      heckeT_ppow_preserves_modFormCharSpace k p hp r χ f.property⟩
  map_add' _ _ := Subtype.ext (map_add (heckeT_ppow k p hp r) _ _)
  map_smul' c _ := Subtype.ext (map_smul (heckeT_ppow k p hp r) c _)

@[simp] lemma heckeT_ppow_charRestrictAll_coe (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (r : ℕ)
    (χ : (ZMod N)ˣ →* ℂˣ) (f : modFormCharSpace k χ) :
    ((heckeT_ppow_charRestrictAll k p hp r χ f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      heckeT_ppow k p hp r (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-- On good primes the general restriction agrees with the bridge file's
`heckeT_ppow_charRestrict`. -/
lemma heckeT_ppow_charRestrictAll_eq_good (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ) (χ : (ZMod N)ˣ →* ℂˣ) :
    heckeT_ppow_charRestrictAll (N := N) k p hp r χ =
      heckeT_ppow_charRestrict (k := k) (χ := χ) p hp hpN r :=
  LinearMap.ext fun _ ↦ Subtype.ext rfl

@[simp] lemma heckeT_n_charRestrictAll_one (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    heckeT_n_charRestrictAll (N := N) k 1 χ = 1 := by
  refine LinearMap.ext fun f ↦ Subtype.ext ?_
  rw [heckeT_n_charRestrictAll_coe, heckeT_n_one]
  rfl

/-- Peeling for the general restriction, mirroring `heckeT_n_unfold`. -/
lemma heckeT_n_charRestrictAll_unfold (k : ℤ) (n : ℕ) [NeZero n] (hn : 1 < n)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    haveI : NeZero (n / n.minFac ^ n.factorization n.minFac) :=
      ⟨(Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n n.minFac))
        (pow_pos (Nat.minFac_prime (by omega : n ≠ 1)).pos _)).ne'⟩
    heckeT_n_charRestrictAll (N := N) k n χ =
      heckeT_ppow_charRestrictAll k n.minFac (Nat.minFac_prime (by omega : n ≠ 1))
          (n.factorization n.minFac) χ *
        heckeT_n_charRestrictAll k (n / n.minFac ^ n.factorization n.minFac) χ := by
  haveI : NeZero (n / n.minFac ^ n.factorization n.minFac) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n n.minFac))
      (pow_pos (Nat.minFac_prime (by omega : n ≠ 1)).pos _)).ne'⟩
  refine LinearMap.ext fun f ↦ Subtype.ext ?_
  simp only [Module.End.mul_apply, heckeT_n_charRestrictAll_coe,
    heckeT_ppow_charRestrictAll_coe]
  rw [heckeT_n_unfold k n hn]
  rfl

/-- **Composite bridge, restriction form**: for `n` coprime to `N`,
`Φ_χ(D_n) = (chiAllU χ n)⁻¹ • (T_n restricted to M_k(N,χ))`.

This is the engine of the ring-first transports.  It is deliberately restricted to
indices coprime to the level: the character-space homomorphism `heckeRingHomCharSpace`
is built on the *adjugate* twisted slash, and at a bad prime `p ∣ N` the adjugate sends
the class of `diag(1,p)` to the (disjoint) class of `diag(p,1)`, so the ring image of
`D_p` is **not** `U_p` — see the diagnosis at `decompQuot_D_p_Gamma0_bad_natcard` in
`NebentypusHeckeRingHom.lean`.  Bad-prime blocks are therefore handled on the operator
side (they are explicit `U_p`-powers), and only the good part transports. -/
theorem heckeRingHomCharSpace_heckeRingDn_all (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) :
    heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingDn n) =
      ((chiAllU χ n : ℂ))⁻¹ • heckeT_n_charRestrictAll k n χ := by
  suffices H : ∀ m : ℕ, (hm0 : NeZero m) → Nat.Coprime m N →
      heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingDn m) =
        ((chiAllU χ m : ℂ))⁻¹ • heckeT_n_charRestrictAll k m χ from H n ‹_› hn
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 hmN
    haveI := hm0
    rcases eq_or_ne m 1 with rfl | hm1
    · rw [heckeRingDn_one, map_one, chiAllU_one, heckeT_n_charRestrictAll_one]
      simp
    · have hm : 1 < m := by
        have := NeZero.ne m
        omega
      set p := m.minFac with hp_def
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      set v := m.factorization p with hv_def
      have hv_pos : 0 < v :=
        hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)
      have hdiv_pos : 0 < m / p ^ v :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) (pow_pos hp.pos v)
      haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
      have hdiv_lt : m / p ^ v < m :=
        Nat.div_lt_self (by omega) (Nat.one_lt_pow hv_pos.ne' hp.one_lt)
      have hcop : Nat.Coprime (p ^ v) (m / p ^ v) :=
        Nat.Coprime.pow_left v
          (hp.coprime_iff_not_dvd.mpr (hv_def ▸ Nat.not_dvd_ordCompl hp (NeZero.ne m)))
      have hsplit : m = p ^ v * (m / p ^ v) := (Nat.ordProj_mul_ordCompl_eq_self m p).symm
      -- Peel all three objects.
      have hD : heckeRingDn (N := N) m =
          heckeRingDppow p hp v * heckeRingDn (m / p ^ v) := by
        conv_lhs => rw [hsplit]
        rw [heckeRingDn_mul_coprime _ _ hcop, heckeRingDn_ppow p hp v]
      have hchi : chiAllU χ m = chiAllU χ (p ^ v) * chiAllU χ (m / p ^ v) := by
        conv_lhs => rw [hsplit]
        exact chiAllU_mul_coprime χ _ _ hcop
      have hT : heckeT_n_charRestrictAll (N := N) k m χ =
          heckeT_ppow_charRestrictAll k p hp v χ *
            heckeT_n_charRestrictAll k (m / p ^ v) χ := by
        have := heckeT_n_charRestrictAll_unfold (N := N) k m hm χ
        simpa [← hp_def, ← hv_def] using this
      have hquotN : Nat.Coprime (m / p ^ v) N :=
        Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m p)) hmN
      have hpN : Nat.Coprime p N := hmN.coprime_dvd_left (Nat.minFac_dvd m)
      rw [hD, map_mul, ih (m / p ^ v) hdiv_lt ⟨hdiv_pos.ne'⟩ hquotN, hchi, hT]
      rw [heckeRingHomCharSpace_heckeRingDppow p hp hpN v,
          heckeT_ppow_charRestrictAll_eq_good k hp hpN v χ,
          chiAllU_ppow_good χ hp hpN v hv_pos]
      rw [smul_mul_smul_comm]
      congr 1
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_inv]
      rw [inv_pow]

/-- The general restriction, rescaled form of the bridge:
`T_n|_χ = chiAllU χ n • Φ_χ(D_n)`. -/
theorem heckeT_n_charRestrictAll_eq_smul_ringHom (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) :
    heckeT_n_charRestrictAll (N := N) k n χ =
      ((chiAllU χ n : ℂ)) • heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingDn n) := by
  rw [heckeRingHomCharSpace_heckeRingDn_all n hn, smul_smul,
    mul_inv_cancel₀ (Units.ne_zero _), one_smul]

/-- Pairwise commutativity of the restricted operators — from `CommRing 𝕋(Γ₀(N))`. -/
theorem heckeT_n_charRestrictAll_comm (m n : ℕ) [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) :
    heckeT_n_charRestrictAll (N := N) k m χ * heckeT_n_charRestrictAll k n χ =
      heckeT_n_charRestrictAll k n χ * heckeT_n_charRestrictAll k m χ := by
  rw [heckeT_n_charRestrictAll_eq_smul_ringHom m hm,
    heckeT_n_charRestrictAll_eq_smul_ringHom n hn,
    smul_mul_smul_comm, smul_mul_smul_comm, ← map_mul, ← map_mul,
    Gamma0_pair_HeckeAlgebra_mul_comm N (heckeRingDn m) (heckeRingDn n),
    mul_comm ((chiAllU χ m : ℂ)) ((chiAllU χ n : ℂ))]

/-- Coprime multiplicativity of the restricted operators — from
`heckeRingDn_mul_coprime` in the ring. -/
theorem heckeT_n_charRestrictAll_mul_coprime' (m n : ℕ) [NeZero m] [NeZero n]
    (hmn : Nat.Coprime m n) (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) :
    haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
    heckeT_n_charRestrictAll (N := N) k (m * n) χ =
      heckeT_n_charRestrictAll k m χ * heckeT_n_charRestrictAll k n χ := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [heckeT_n_charRestrictAll_eq_smul_ringHom (m * n) (Nat.Coprime.mul_left hm hn),
    heckeT_n_charRestrictAll_eq_smul_ringHom m hm,
    heckeT_n_charRestrictAll_eq_smul_ringHom n hn,
    heckeRingDn_mul_coprime m n hmn, map_mul, chiAllU_mul_coprime χ m n hmn,
    smul_mul_smul_comm, Units.val_mul]

/-- **Commutativity of the Hecke operators `T_n` on `M_k(Γ₁(N))`** — for all positive
indices, transported from the commutative ring `𝕋(Γ₀(N))` and glued over the character
decomposition.  Replaces the operator-level induction cascade. -/
theorem heckeT_n_comm_ring (k : ℤ) (m n : ℕ) [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) :
    heckeT_n (N := N) k m * heckeT_n k n = heckeT_n k n * heckeT_n k m := by
  refine ModularForm_Gamma1_endo_ext (fun χ f hf ↦ ?_)
  have h := congrArg
    (fun T : Module.End ℂ (modFormCharSpace k χ) ↦
      ((T ⟨f, hf⟩ : modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    (heckeT_n_charRestrictAll_comm (N := N) (k := k) (χ := χ) m n hm hn)
  simpa only [Module.End.mul_apply, heckeT_n_charRestrictAll_coe] using h

/-- **Coprime multiplicativity of the Hecke operators on `M_k(Γ₁(N))`** — transported
from the ring. -/
theorem heckeT_n_mul_coprime_ring (k : ℤ) (m n : ℕ) [NeZero m] [NeZero n]
    (hmn : Nat.Coprime m n) (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) :
    haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
    heckeT_n (N := N) k (m * n) = heckeT_n k m * heckeT_n k n := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  refine ModularForm_Gamma1_endo_ext (fun χ f hf ↦ ?_)
  have h := congrArg
    (fun T : Module.End ℂ (modFormCharSpace k χ) ↦
      ((T ⟨f, hf⟩ : modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    (heckeT_n_charRestrictAll_mul_coprime' (N := N) (k := k) (χ := χ) m n hmn hm hn)
  simpa only [Module.End.mul_apply, heckeT_n_charRestrictAll_coe] using h

/-- **Commutation with the diamond operators, all indices** — on each character space the
diamond acts as a scalar (or vanishes), so no ring input is needed. -/
theorem heckeT_n_comm_diamondOp_all (k : ℤ) (n d : ℕ) [NeZero n] :
    diamondOp_n (N := N) k d * heckeT_n k n = heckeT_n k n * diamondOp_n k d := by
  by_cases hd : Nat.Coprime d N
  · refine ModularForm_Gamma1_endo_ext (fun χ f hf ↦ ?_)
    have hTf : heckeT_n k n f ∈ modFormCharSpace k χ :=
      heckeT_n_preserves_modFormCharSpace_all k n χ hf
    have h1 : diamondOp k (ZMod.unitOfCoprime d hd) (heckeT_n k n f) =
        (↑(χ (ZMod.unitOfCoprime d hd)) : ℂ) • heckeT_n k n f :=
      (mem_modFormCharSpace_iff k χ _).mp hTf _
    have h2 : diamondOp k (ZMod.unitOfCoprime d hd) f =
        (↑(χ (ZMod.unitOfCoprime d hd)) : ℂ) • f :=
      (mem_modFormCharSpace_iff k χ f).mp hf _
    simp only [Module.End.mul_apply, diamondOp_n_coprime k hd, h1, h2, map_smul]
  · simp [diamondOp_n_not_coprime k hd]

end HeckeRing.GL2.Unified

/- Re-homed public operator identities.

The public Hecke-operator structural identities formerly lived (with self-contained
induction proofs) in `HeckeT_n.lean`.  After the ring-first refactor their proofs are the
transported `Unified.*_ring` results above; we re-export them here under their original
`HeckeRing.GL2` names and signatures so that downstream consumers are unaffected (modulo the
explicit coprimality hypotheses, which the consumers already have in scope).

`heckeT_n_mul` (the full divisor-sum multiplication table) is **deleted without an
operator-level replacement**: its canonical form is the ring-side `heckeRingDn_mul`
in `Unified/Gamma0RingDn.lean`. -/

namespace HeckeRing.GL2

open HeckeRing.GL2.Unified

variable {N : ℕ} [NeZero N]

/-- `T_m` and `T_n` commute (for `m, n` coprime to the level `N`) — transported from the
commutative Hecke ring `𝕋(Γ₀(N))`. -/
theorem heckeT_n_comm (k : ℤ) (m n : ℕ) [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) :
    heckeT_n (N := N) k m * heckeT_n k n = heckeT_n k n * heckeT_n k m :=
  heckeT_n_comm_ring k m n hm hn

/-- Coprime multiplicativity `T_{mn} = T_m T_n` (for `m, n` coprime to the level `N`) —
transported from the ring identity `heckeRingDn_mul_coprime`. -/
theorem heckeT_n_mul_coprime (k : ℤ) (m n : ℕ) [NeZero m] [NeZero n]
    (hmn : Nat.Coprime m n) (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) :
    haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
    heckeT_n (N := N) (n := m * n) k = heckeT_n k m * heckeT_n k n :=
  heckeT_n_mul_coprime_ring k m n hmn hm hn

/-- `T_n` commutes with the diamond operator `⟨d⟩` (for `n` coprime to the level `N`) —
on each character space the diamond acts by a scalar, so the identity glues from the
character decomposition. -/
theorem heckeT_n_comm_diamondOp (k : ℤ) (n : ℕ) [NeZero n]
    (_hn : Nat.Coprime n N) (d : (ZMod N)ˣ) :
    diamondOp k d * heckeT_n (N := N) k n = heckeT_n k n * diamondOp k d := by
  refine ModularForm_Gamma1_endo_ext (fun χ f hf ↦ ?_)
  have hTf : heckeT_n k n f ∈ modFormCharSpace k χ :=
    heckeT_n_preserves_modFormCharSpace_all k n χ hf
  have h1 : diamondOp k d (heckeT_n k n f) = (↑(χ d) : ℂ) • heckeT_n k n f :=
    (mem_modFormCharSpace_iff k χ _).mp hTf _
  have h2 : diamondOp k d f = (↑(χ d) : ℂ) • f :=
    (mem_modFormCharSpace_iff k χ f).mp hf _
  simp only [Module.End.mul_apply, h1, h2, map_smul]

end HeckeRing.GL2
