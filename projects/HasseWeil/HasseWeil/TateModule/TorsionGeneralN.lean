/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.TateModule.TorsionPowStructure
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# `E[N] ≅ (ZMod N)²` for general `N` — the rank-2 torsion structure via CRT

For `F` algebraically closed and `N` invertible in `F` (`(N : F) ≠ 0`), the `N`-torsion
`E[N] = W.toAffine[(N : ℤ)]` of an elliptic curve is free of rank `2` over `ZMod N`:
`E[N] ≅ (ZMod N)²`.

The proof reduces the general `N` to the prime-power case `E[ℓⁿ] ≅ (ZMod ℓⁿ)²`
(`HasseWeil.TateModule.torsion_ellPow_linearEquiv`) by the **Chinese Remainder Theorem**:

* `N` is `(N : ℤ)`-torsion, so by `Submodule.torsionBy_isInternal` (with the prime-power
  factors `qₚ = p^(N.factorization p)`, pairwise coprime) `E[N]` is the internal direct sum
  of its `qₚ`-torsion submodules `torsionBy ℤ E[N] qₚ`;
* each summand is canonically `E[qₚ]` (drop / rebuild the redundant `E[N]`-membership), hence
  `≅ (ZMod qₚ)²` by the prime-power structure theorem;
* reassembling `⨁ → Π`, swapping `Fin 2`/primes, and recombining `∏ₚ ZMod qₚ ≅ ZMod N`
  (`ZMod.equivPi`) yields `E[N] ≅ (Fin 2 → ZMod N)`.

The chain is built at base `ℤ` (`AddEquiv` / `≃ₗ[ℤ]`) to avoid scalar-ring friction between
`ZMod N` and the per-factor `ZMod qₚ`, and is upgraded to `ZMod N`-linearity at the very end via
`AddMonoidHom.toZModLinearMap`.

Main result:
* `HasseWeil.TateModule.torsion_genN_linearEquiv` — `E[N] ≃ₗ[ZMod N] (Fin 2 → ZMod N)`.

Reference: Silverman, *The Arithmetic of Elliptic Curves* (2nd ed), §III.6 (Cor 6.4(b)).
-/

open WeierstrassCurve

namespace HasseWeil.TateModule

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric
open scoped HasseWeil.WeilPairing.TorsionGeometric DirectSum

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

section Setup

variable (N : ℕ) (hN : (N : F) ≠ 0)

include hN

omit [DecidableEq F] [IsAlgClosed F] [W.toAffine.IsElliptic] in
/-- `N ≠ 0` whenever `(N : F) ≠ 0`. -/
theorem ne_zero_of_natCast_ne_zero : N ≠ 0 := by
  rintro rfl; simp at hN

omit [DecidableEq F] [IsAlgClosed F] [W.toAffine.IsElliptic] hN in
/-- If `p ∣ N` and `(N : F) ≠ 0` then `(p : F) ≠ 0` (a factor of an invertible element is
invertible). -/
theorem natCast_factor_ne_zero {p : ℕ} (hp : p ∣ N) (hN : (N : F) ≠ 0) : (p : F) ≠ 0 := by
  obtain ⟨c, rfl⟩ := hp
  intro hp0
  exact hN (by rw [Nat.cast_mul, hp0, zero_mul])

end Setup

section Annihilation

variable (N : ℕ)

omit [IsAlgClosed F] in
/-- **Annihilation.** Every element of `E[N]` is killed by `N` (the natural-number scalar
action). This is the defining property feeding the `ZMod N`-module structure; it needs no
hypothesis on the characteristic. (General-`N` analogue of
`nsmul_eq_zero_of_mem_torsion_ellPow`.) -/
theorem nsmul_eq_zero_of_mem_torsion_genN (P : W.toAffine[(N : ℤ)]) : N • P = 0 := by
  have hP : (N : ℤ) • P.val = 0 := by
    have := P.property
    rwa [mem_torsionSubgroup] at this
  have hnat : N • P.val = 0 := by
    rw [← natCast_zsmul]; exact hP
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero]
  exact hnat

/-- The `ZMod N`-module structure on `E[N]`, from the fact that every element is killed by `N`.
Registered as a `scoped instance`. (For prime-power `N` this is *defeq* to the existing
`torsion_ellPow_zmodModule`, both being `AddCommGroup.zmodModule` of an annihilation proof.) -/
noncomputable scoped instance torsion_genN_zmodModule :
    Module (ZMod N) W.toAffine[(N : ℤ)] :=
  AddCommGroup.zmodModule (nsmul_eq_zero_of_mem_torsion_genN W N)

end Annihilation

section ScalarBridge

omit [Field F] [DecidableEq F] [IsAlgClosed F] [W.toAffine.IsElliptic]

/-- For an element `x` of a `ZMod m`-module the scalar action of `c : ZMod m` is the integer
action of any integer lift `(ZMod.cast c : ℤ)`. (Replicated from the `private`
`HasseWeil.TateModule.zmodModule_smul_eq_zsmul_cast` in `InverseSystem.lean`.) -/
theorem zmodModule_smul_eq_zsmul_cast {m : ℕ} {G : Type*} [AddCommGroup G]
    [Module (ZMod m) G] (c : ZMod m) (x : G) : c • x = (ZMod.cast c : ℤ) • x := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast c]
  rw [Int.cast_smul_eq_zsmul]

end ScalarBridge

section DirectSum

variable (N : ℕ) (hN : (N : F) ≠ 0)

/-- The prime-power factor `qₚ = p ^ (N.factorization p)`, as an integer. (Defined on all of `ℕ`
so it matches the `q : ι → R` slot of `Submodule.torsionBy_isInternal` with `ι = ℕ`.) -/
noncomputable abbrev primePowerFactor (p : ℕ) : ℤ :=
  ((p ^ (N.factorization p) : ℕ) : ℤ)

omit [IsAlgClosed F] in
/-- `E[N]` is `(N : ℤ)`-torsion: every element is killed by `N`. -/
theorem isTorsionBy_natCast :
    Module.IsTorsionBy ℤ W.toAffine[(N : ℤ)] (N : ℤ) := by
  intro P
  rw [natCast_zsmul]
  exact nsmul_eq_zero_of_mem_torsion_genN W N P

omit [IsAlgClosed F] in
/-- The pairwise-coprimality of the prime-power factors `qₚ`, transported to `ℤ` as
`IsCoprime`. -/
theorem pairwise_isCoprime_primePowerFactor :
    (↑N.primeFactors : Set ℕ).Pairwise (Function.onFun IsCoprime (primePowerFactor N)) := by
  intro p hp q hq hpq
  have hcop : Nat.Coprime (p ^ N.factorization p) (q ^ N.factorization q) := by
    refine Nat.Coprime.pow _ _ ?_
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  exact hcop.cast (R := ℤ)

/-- `(N : ℤ) = ∏ p ∈ N.primeFactors, (p ^ (N.factorization p) : ℤ)`, for `N ≠ 0`. -/
theorem natCast_eq_prod_primePowerFactor (hN0 : N ≠ 0) :
    (N : ℤ) = ∏ p ∈ N.primeFactors, primePowerFactor N p := by
  have h : N = ∏ p ∈ N.primeFactors, (p ^ (N.factorization p) : ℕ) := by
    conv_lhs => rw [Nat.prod_pow_primeFactors_factorization hN0]
    exact Finset.prod_coe_sort N.primeFactors fun p ↦ (p ^ (N.factorization p) : ℕ)
  show (N : ℤ) = ∏ p ∈ N.primeFactors, ((p ^ (N.factorization p) : ℕ) : ℤ)
  exact_mod_cast h

include hN in
omit [IsAlgClosed F] in
/-- **Internal direct-sum decomposition (CRT).** `E[N]` is the internal direct sum of its
prime-power torsion submodules `torsionBy ℤ E[N] qₚ`. -/
theorem isInternal_torsionBy :
    DirectSum.IsInternal fun p : N.primeFactors =>
      Submodule.torsionBy ℤ W.toAffine[(N : ℤ)] (primePowerFactor N p) := by
  have hN0 : N ≠ 0 := ne_zero_of_natCast_ne_zero (F := F) N hN
  apply Submodule.torsionBy_isInternal (S := N.primeFactors) (q := primePowerFactor N)
    (pairwise_isCoprime_primePowerFactor N)
  -- `E[N]` is `(∏ p, qₚ)`-torsion since it is `(N:ℤ)`-torsion and `N = ∏ p, qₚ`.
  rw [← natCast_eq_prod_primePowerFactor N hN0]
  exact isTorsionBy_natCast W N

include hN in
/-- The internal-direct-sum isomorphism `(⨁ p, torsionBy ℤ E[N] qₚ) ≃ₗ[ℤ] E[N]`. -/
noncomputable def directSumEquiv :
    (⨁ p : N.primeFactors, Submodule.torsionBy ℤ W.toAffine[(N : ℤ)] (primePowerFactor N p))
      ≃ₗ[ℤ] W.toAffine[(N : ℤ)] :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _) (isInternal_torsionBy W N hN)

end DirectSum

section SummandBridge

variable (N : ℕ)

omit [IsAlgClosed F] in
/-- The `.val` of a `zsmul` in the torsion subgroup `E[m]` is the `zsmul` of the `.val` (push the
integer action through the `AddSubgroup` inclusion). -/
theorem coe_zsmul_torsionSubgroup (m : ℤ) (k : ℤ) (x : W.toAffine[m]) :
    ((k • x : W.toAffine[m]) : W.toAffine.Point) = k • (x : W.toAffine.Point) :=
  map_zsmul (W.toAffine[m]).subtype k x

omit [IsAlgClosed F] in
/-- A point killed by `m` with `m ∣ N` is `N`-torsion: `E[m] ≤ E[N]`. -/
theorem mem_torsionSubgroup_of_dvd {m : ℤ} (hm : m ∣ (N : ℤ)) {Q : W.toAffine.Point}
    (hQ : m • Q = 0) : Q ∈ W.toAffine[(N : ℤ)] := by
  rw [mem_torsionSubgroup]
  obtain ⟨c, hc⟩ := hm
  rw [hc, mul_comm, mul_smul, hQ, smul_zero]

omit [IsAlgClosed F] in
/-- Forward membership: a `qₚ`-torsion element `x` of `E[N]` gives a point `x.val.val` killed
by `qₚ`. -/
theorem summandFwd_mem {p : ℕ}
    (x : Submodule.torsionBy ℤ W.toAffine[(N : ℤ)] (primePowerFactor N p)) :
    x.val.val ∈ W.toAffine[(primePowerFactor N p)] := by
  rw [mem_torsionSubgroup]
  have hx : (primePowerFactor N p) • x.val = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.property
  have hval := congrArg (Subtype.val (p := fun P => P ∈ W.toAffine[(N : ℤ)])) hx
  rwa [coe_zsmul_torsionSubgroup, ZeroMemClass.coe_zero] at hval

omit [IsAlgClosed F] in
/-- Backward membership: a point `Q` killed by `qₚ` lies in `E[N]` (since `qₚ ∣ N`), and the
resulting element of `E[N]` is `qₚ`-torsion. -/
theorem summandBwd_mem {p : ℕ} (Q : W.toAffine[(primePowerFactor N p)]) :
    (⟨Q.val, mem_torsionSubgroup_of_dvd W N (by exact_mod_cast Nat.ordProj_dvd N p)
        ((mem_torsionSubgroup _ _ _).mp Q.property)⟩ : W.toAffine[(N : ℤ)]) ∈
      Submodule.torsionBy ℤ W.toAffine[(N : ℤ)] (primePowerFactor N p) := by
  rw [Submodule.mem_torsionBy_iff]
  apply Subtype.ext
  rw [coe_zsmul_torsionSubgroup, ZeroMemClass.coe_zero]
  exact (mem_torsionSubgroup _ _ _).mp Q.property

omit [IsAlgClosed F] in
/-- The `qₚ`-torsion of the subgroup `E[N]` is canonically the `qₚ`-torsion `E[qₚ]` of the whole
point group: a `qₚ`-torsion element of `E[N]` is just a point killed by `qₚ` (its
`E[N]`-membership is automatic, since `qₚ ∣ N`). -/
noncomputable def summandEquiv (p : ℕ) :
    Submodule.torsionBy ℤ W.toAffine[(N : ℤ)] (primePowerFactor N p)
      ≃ₗ[ℤ] W.toAffine[(primePowerFactor N p)] where
  toFun x := ⟨x.val.val, summandFwd_mem W N x⟩
  invFun Q := ⟨⟨Q.val, mem_torsionSubgroup_of_dvd W N (by exact_mod_cast Nat.ordProj_dvd N p)
      ((mem_torsionSubgroup _ _ _).mp Q.property)⟩, summandBwd_mem W N Q⟩
  left_inv x := by ext; rfl
  right_inv Q := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' c x := by ext; rfl

/-- **Per-summand rank-2 (additive).** For `p ∈ N.primeFactors` with `k = N.factorization p`, the
`qₚ`-torsion summand is additively `(Fin 2 → ZMod (p ^ k))`: compose the subgroup bridge
`summandEquiv` with the prime-power structure theorem `torsion_ellPow_linearEquiv`. -/
noncomputable def summandRankTwoAddEquiv (hN : (N : F) ≠ 0) {p : ℕ} (hp : p ∈ N.primeFactors) :
    Submodule.torsionBy ℤ W.toAffine[(N : ℤ)] (primePowerFactor N p)
      ≃+ (Fin 2 → ZMod (p ^ (N.factorization p))) := by
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hpF : (p : F) ≠ 0 := natCast_factor_ne_zero N (Nat.dvd_of_mem_primeFactors hp) hN
  exact (summandEquiv W N p).toAddEquiv.trans
    (torsion_ellPow_linearEquiv W p hpF (N.factorization p)).toAddEquiv

end SummandBridge

section Assembly

variable (N : ℕ)

/-- The additive "swap" `(Π p, Fin 2 → Xₚ) ≃+ (Fin 2 → Π p, Xₚ)`. -/
def piSwapAddEquiv {ι : Type*} (X : ι → Type*) [∀ i, AddCommGroup (X i)] :
    (∀ i, Fin 2 → X i) ≃+ (Fin 2 → ∀ i, X i) where
  toFun f j i := f i j
  invFun g i j := g j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The pointwise CRT recombination `(Fin 2 → Π p, ZMod (p ^ kₚ)) ≃+ (Fin 2 → ZMod N)`, from
`ZMod.equivPi`. -/
noncomputable def piCrtAddEquiv (hN0 : N ≠ 0) :
    (Fin 2 → ∀ p : N.primeFactors, ZMod ((p : ℕ) ^ (N.factorization p)))
      ≃+ (Fin 2 → ZMod N) :=
  AddEquiv.piCongrRight fun _ : Fin 2 => (ZMod.equivPi (n := N) hN0).symm.toAddEquiv

variable (hN : (N : F) ≠ 0)

include hN in
/-- **The full additive isomorphism** `E[N] ≃+ (Fin 2 → ZMod N)`, assembled from the CRT
decomposition, the per-summand rank-2 structure, the index swap, and the CRT recombination. -/
noncomputable def torsion_genN_addEquiv :
    W.toAffine[(N : ℤ)] ≃+ (Fin 2 → ZMod N) :=
  have hN0 : N ≠ 0 := ne_zero_of_natCast_ne_zero (F := F) N hN
  -- `E[N] ≃+ ⨁ p, torsionBy ℤ E[N] qₚ`
  (directSumEquiv W N hN).symm.toAddEquiv.trans <|
  -- `⨁ ≃+ Π p, torsionBy ℤ E[N] qₚ`
  (DirectSum.linearEquivFunOnFintype ℤ _
      (fun p : N.primeFactors =>
        Submodule.torsionBy ℤ W.toAffine[(N : ℤ)] (primePowerFactor N p))).toAddEquiv.trans <|
  -- per-summand rank 2: `Π p, torsionBy ≃+ Π p, (Fin 2 → ZMod (p ^ kₚ))`
  (AddEquiv.piCongrRight fun p : N.primeFactors =>
      summandRankTwoAddEquiv W N hN p.2).trans <|
  -- swap and recombine
  (piSwapAddEquiv (fun p : N.primeFactors => ZMod ((p : ℕ) ^ (N.factorization p)))).trans <|
  piCrtAddEquiv N hN0

include hN in
/-- **`E[N] ≅ (ZMod N)²`** as `ZMod N`-modules, for `N` invertible in the algebraically closed
field `F`. This is the general-`N` rank-2 structure of the `N`-torsion of an elliptic curve,
obtained from the prime-power case by the Chinese Remainder Theorem. The underlying additive
isomorphism is `torsion_genN_addEquiv`; this upgrades it to a `ZMod N`-linear equivalence (every
additive map between `ZMod N`-modules is automatically `ZMod N`-linear, `ZMod.map_smul`). -/
noncomputable def torsion_genN_linearEquiv :
    W.toAffine[(N : ℤ)] ≃ₗ[ZMod N] (Fin 2 → ZMod N) :=
  (torsion_genN_addEquiv W N hN).toLinearEquiv
    (fun c x => ZMod.map_smul (torsion_genN_addEquiv W N hN).toAddMonoidHom c x)

end Assembly

end HasseWeil.TateModule
