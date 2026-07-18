/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import ModularCurves.ForMathlib.TorsionByEquiv

/-!
# Torsion-count characterisation of `(ℤ/N)²`

## Main result

* `addEquiv_pi_fin_two_zmod_of_natCard`: a finite abelian group killed by `N` whose
  `d`-torsion has exactly `d ^ 2` elements for every divisor `d` of `N` is isomorphic to
  `(ZMod N)²`.

This is the pure group-theory half of Silverman III.6.4(b)/KM 2.3.5 (ticket T-B6e).
The scheme-theoretic étale counting (`EtaleSectionsCount.lean`) produces exactly these
cardinalities for the torsion of an elliptic curve over an algebraically closed field.

The proof runs through the elementary-divisor structure theorem
(`AddCommGroup.equiv_directSum_zmod_of_finite`): the counting hypothesis forces, for each
prime `p ∣ N`, exactly two summands with `p`-part `p ^ (N.factorization p)`; CRT
(`ZMod.equivPi`) reassembles the summands into two copies of `ZMod N`.

Upstream candidate: `Mathlib.GroupTheory.FiniteAbelian`.
-/

universe u

open AddSubgroup DirectSum

namespace ModularCurves

private lemma natCard_nsmul_ker_zmod (p e j : ℕ) (hp : p.Prime) :
    Nat.card {x : ZMod (p ^ e) // p ^ j • x = 0} = p ^ min j e := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  change Nat.card ↥(nsmulAddMonoidHom (α := ZMod (p ^ e)) (p ^ j)).ker = _
  rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod]
  rcases le_total j e with hje | hej
  · rw [min_eq_left hje, Nat.gcd_eq_right (pow_dvd_pow p hje)]
  · rw [min_eq_right hej, Nat.gcd_eq_left (pow_dvd_pow p hej)]

private lemma natCard_nsmul_ker_zmod_of_coprime (d n : ℕ) (hd : Nat.Coprime d n) :
    Nat.card {x : ZMod n // d • x = 0} = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at hd
    subst hd
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => ?_⟩, ⟨0, one_smul _ 0⟩⟩
    have hx := x.2
    have hy := y.2
    rw [one_smul] at hx hy
    exact Subtype.ext (hx.trans hy.symm)
  · haveI : NeZero n := ⟨hn⟩
    change Nat.card ↥(nsmulAddMonoidHom (α := ZMod n) d).ker = 1
    rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod]
    exact hd.symm

private lemma natCard_nsmul_ker_zmod_pow (p q e j : ℕ) (hp : p.Prime)
    (hq : e ≠ 0 → q = p) :
    Nat.card {y : ZMod (q ^ e) // p ^ j • y = 0} = p ^ min j e := by
  rcases eq_or_ne e 0 with hE | hE
  · subst hE
    rw [natCard_nsmul_ker_zmod_of_coprime _ _
      (by
        rw [pow_zero]
        exact Nat.coprime_one_right _)]
    rw [min_zero, pow_zero]
  · rw [hq hE]
    exact natCard_nsmul_ker_zmod p e j hp

private def nsmulKerCongr {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H)
    (d : ℕ) : {x : G // d • x = 0} ≃ {y : H // d • y = 0} :=
  (Equiv.subtypeEquivRight fun _ => by
      simp only [Submodule.mem_torsionBy_iff, natCast_zsmul]).trans <|
    (Submodule.torsionByCongr e d).trans
      (Equiv.subtypeEquivRight fun _ => by
        simp only [Submodule.mem_torsionBy_iff, natCast_zsmul]).symm

private def nsmulKerPiEquiv {ι : Type} (M : ι → Type u) [∀ i, AddCommGroup (M i)]
    (d : ℕ) : {x : ∀ i, M i // d • x = 0} ≃ ∀ i, {y : M i // d • y = 0} where
  toFun x i := ⟨x.1 i, congrFun x.2 i⟩
  invFun y := ⟨fun i => (y i).1, funext fun i => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma natCard_nsmul_ker_directSum {ι : Type} [Fintype ι] (n : ι → ℕ) (d : ℕ) :
    Nat.card {x : (⨁ i, ZMod (n i)) // d • x = 0} =
      ∏ i, Nat.card {y : ZMod (n i) // d • y = 0} := by
  rw [Nat.card_congr ((nsmulKerCongr (DirectSum.addEquivProd fun i => ZMod (n i))
    d).trans (nsmulKerPiEquiv (fun i => ZMod (n i)) d))]
  exact Nat.card_pi

private def piEquivProdOfSubsingleton {ι : Type} [DecidableEq ι] (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] (i₁ i₂ : ι) (hne : i₁ ≠ i₂)
    (htriv : ∀ i, i ≠ i₁ → i ≠ i₂ → Subsingleton (M i)) :
    (∀ i, M i) ≃+ M i₁ × M i₂ where
  toFun f := (f i₁, f i₂)
  invFun x := Function.update (Function.update (0 : ∀ i, M i) i₁ x.1) i₂ x.2
  left_inv f := by
    funext i
    by_cases h2 : i = i₂
    · subst h2
      simp only [Function.update_self]
    · by_cases h1 : i = i₁
      · dsimp only
        rw [Function.update_of_ne h2, h1, Function.update_self]
      · haveI := htriv i h1 h2
        exact Subsingleton.elim _ _
  right_inv x := by
    ext
    · dsimp only
      rw [Function.update_of_ne hne, Function.update_self]
    · dsimp only
      rw [Function.update_self]
  map_add' f g := rfl

private def prodAddEquivFinTwoArrow (A : Type u) [AddCommGroup A] :
    (A × A) ≃+ (Fin 2 → A) :=
  { (finTwoArrowEquiv A).symm with
    map_add' := fun x y => by
      funext t
      fin_cases t <;> rfl }

private lemma orderSummand_dvd_of_kill {ι : Type} (P E : ι → ℕ) {G : Type u}
    [AddCommGroup G] (e : G ≃+ ⨁ i, ZMod (P i ^ E i)) (m : ℕ)
    (hkill : ∀ x : G, m • x = 0) (i : ι) : P i ^ E i ∣ m := by
  classical
  have h1 : m • (DirectSum.of (fun i => ZMod (P i ^ E i)) i 1) = 0 := by
    have h2 := congrArg e (hkill (e.symm (DirectSum.of (fun i => ZMod (P i ^ E i)) i 1)))
    rwa [map_nsmul, e.apply_symm_apply, map_zero] at h2
  have h5 : m • (1 : ZMod (P i ^ E i)) = 0 := by
    have h1' : DirectSum.of (fun i => ZMod (P i ^ E i)) i (m • 1) = 0 := by
      rw [map_nsmul]
      exact h1
    have h6 := congrArg (fun z => z i) h1'
    simpa [DirectSum.of_eq_same] using h6
  rw [← ZMod.addOrderOf_one (P i ^ E i)]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h5

private lemma sum_min_exponent {ι : Type} [Fintype ι] (P E : ι → ℕ) (p j : ℕ)
    (hp : p.Prime) (hPp : ∀ i, E i ≠ 0 → P i = p) {G : Type u} [AddCommGroup G]
    (e : G ≃+ ⨁ i, ZMod (P i ^ E i))
    (hcountj : Nat.card {x : G // p ^ j • x = 0} = (p ^ j) ^ 2) :
    ∑ i, min j (E i) = 2 * j := by
  have hprod : ∏ i, Nat.card {y : ZMod (P i ^ E i) // p ^ j • y = 0} = (p ^ j) ^ 2 := by
    rw [← natCard_nsmul_ker_directSum (fun i => P i ^ E i) (p ^ j),
      ← Nat.card_congr (nsmulKerCongr e (p ^ j))]
    exact hcountj
  have hterm : ∀ i, Nat.card {y : ZMod (P i ^ E i) // p ^ j • y = 0} = p ^ min j (E i) :=
    fun i => natCard_nsmul_ker_zmod_pow p (P i) (E i) j hp (hPp i)
  rw [Finset.prod_congr rfl fun i _ => hterm i, Finset.prod_pow_eq_pow_sum, ← pow_mul,
    mul_comm j 2] at hprod
  exact Nat.pow_right_injective hp.two_le hprod

private lemma primePow_case (p v : ℕ) (hp : p.Prime) (hv : 0 < v) (H : Type u)
    [AddCommGroup H] (hkill : ∀ x : H, p ^ v • x = 0)
    (hcount : ∀ j : ℕ, j ≤ v → Nat.card {x : H // p ^ j • x = 0} = (p ^ j) ^ 2) :
    Nonempty (H ≃+ (Fin 2 → ZMod (p ^ v))) := by
  classical
  haveI : Finite H := by
    have hH : Nat.card H = (p ^ v) ^ 2 := by
      rw [← hcount v le_rfl]
      exact (Nat.card_congr (Equiv.subtypeUnivEquiv hkill)).symm
    exact Nat.finite_of_card_ne_zero (by
      rw [hH]
      exact pow_ne_zero 2 (pow_ne_zero v hp.ne_zero))
  obtain ⟨ι, hfin, P, hP, E, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite H
  have hdvd : ∀ i, P i ^ E i ∣ p ^ v := orderSummand_dvd_of_kill P E e (p ^ v) hkill
  have hPp : ∀ i, E i ≠ 0 → P i = p := by
    intro i hE
    have h1 : P i ∣ p ^ v := (dvd_pow_self (P i) hE).trans (hdvd i)
    exact (Nat.prime_dvd_prime_iff_eq (hP i) hp).mp ((hP i).dvd_of_dvd_pow h1)
  have hEv : ∀ i, E i ≤ v := by
    intro i
    rcases eq_or_ne (E i) 0 with hE | hE
    · lia
    · have h1 := hdvd i
      rw [hPp i hE] at h1
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1
  have hsum : ∀ j : ℕ, j ≤ v → ∑ i, min j (E i) = 2 * j :=
    fun j hj => sum_min_exponent P E p j hp hPp e (hcount j hj)
  set σ : Finset ι := Finset.univ.filter (fun i => E i ≠ 0) with hσdef
  have hσcard : σ.card = 2 := by
    have h1 := hsum 1 hv
    have h2 : ∑ i, min 1 (E i) = σ.card := by
      rw [hσdef, Finset.card_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases eq_or_ne (E i) 0 with hE | hE
      · simp only [hE, min_zero, ne_eq, not_true_eq_false, if_false]
      · rw [Nat.min_eq_left (Nat.one_le_iff_ne_zero.mpr hE), if_pos hE]
    lia
  obtain ⟨i₁, i₂, hne12, hσeq⟩ := Finset.card_eq_two.mp hσcard
  have hmem : ∀ i, i ∈ σ ↔ E i ≠ 0 := by
    intro i
    rw [hσdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hE1ne : E i₁ ≠ 0 := (hmem i₁).mp (hσeq ▸ Finset.mem_insert_self i₁ {i₂})
  have hE2ne : E i₂ ≠ 0 := (hmem i₂).mp (hσeq ▸ Finset.mem_insert_of_mem
    (Finset.mem_singleton_self i₂))
  have hEsum : E i₁ + E i₂ = 2 * v := by
    have h1 := hsum v le_rfl
    have h2 : ∑ i, min v (E i) = ∑ i, E i :=
      Finset.sum_congr rfl fun i _ => Nat.min_eq_right (hEv i)
    have h3 : ∑ i, E i = ∑ i ∈ σ, E i := by
      refine (Finset.sum_filter_of_ne fun i _ hE => hE).symm
    rw [h2, h3, hσeq, Finset.sum_pair hne12] at h1
    exact h1
  have hE1 : E i₁ = v := by
    have := hEv i₁
    have := hEv i₂
    lia
  have hE2 : E i₂ = v := by
    have := hEv i₁
    lia
  have hzm1 : P i₁ ^ E i₁ = p ^ v := by
    rw [hE1, hPp i₁ hE1ne]
  have hzm2 : P i₂ ^ E i₂ = p ^ v := by
    rw [hE2, hPp i₂ hE2ne]
  have htriv : ∀ i, i ≠ i₁ → i ≠ i₂ → Subsingleton (ZMod (P i ^ E i)) := by
    intro i h1 h2
    have hE : E i = 0 := by
      by_contra hE
      have hin : i ∈ σ := (hmem i).mpr hE
      rw [hσeq] at hin
      rcases Finset.mem_insert.mp hin with h | h
      · exact h1 h
      · exact h2 (Finset.mem_singleton.mp h)
    rw [hE, pow_zero]
    infer_instance
  exact ⟨e.trans ((DirectSum.addEquivProd (fun i => ZMod (P i ^ E i))).trans
    (((piEquivProdOfSubsingleton (fun i => ZMod (P i ^ E i)) i₁ i₂ hne12 htriv).trans
      (AddEquiv.prodCongr (ZMod.ringEquivCongr hzm1).toAddEquiv
        (ZMod.ringEquivCongr hzm2).toAddEquiv)).trans
      (prodAddEquivFinTwoArrow (ZMod (p ^ v)))))⟩

private def nsmulKerSubgroup (H : Type u) [AddCommGroup H] (a : ℕ) : AddSubgroup H where
  carrier := {x | a • x = 0}
  zero_mem' := smul_zero a
  add_mem' := fun {x y} hx hy => by
    have hx' : a • x = 0 := hx
    have hy' : a • y = 0 := hy
    show a • (x + y) = 0
    rw [smul_add, hx', hy', add_zero]
  neg_mem' := fun {x} hx => by
    have hx' : a • x = 0 := hx
    show a • (-x) = 0
    rw [smul_neg, hx', neg_zero]

private lemma nsmulKerSubgroup_kill (H : Type u) [AddCommGroup H] (a : ℕ)
    (z : nsmulKerSubgroup H a) : a • z = 0 := by
  apply Subtype.ext
  have h2 : ((a • z : nsmulKerSubgroup H a) : H) = a • (z : H) :=
    map_nsmul (nsmulKerSubgroup H a).subtype a z
  rw [h2, ZeroMemClass.coe_zero]
  exact z.2

private lemma nsmulKerSubgroupKer_mem {H : Type u} [AddCommGroup H] {a d : ℕ}
    (hda : d ∣ a) {x : H} (hx : d • x = 0) : x ∈ nsmulKerSubgroup H a := by
  obtain ⟨c, hc⟩ := hda
  show a • x = 0
  rw [hc, mul_comm d c, mul_smul, hx, smul_zero]

private def nsmulKerSubgroupKerEquiv (H : Type u) [AddCommGroup H] (a d : ℕ)
    (hda : d ∣ a) :
    {z : nsmulKerSubgroup H a // d • z = 0} ≃ {x : H // d • x = 0} where
  toFun z := ⟨z.1.1, by
    have h1 := congrArg ((nsmulKerSubgroup H a).subtype) z.2
    rwa [map_nsmul, map_zero] at h1⟩
  invFun x := ⟨⟨x.1, nsmulKerSubgroupKer_mem hda x.2⟩, Subtype.ext (by
    have h2 : ((d • (⟨x.1, nsmulKerSubgroupKer_mem hda x.2⟩ : nsmulKerSubgroup H a) :
        nsmulKerSubgroup H a) : H) = d • x.1 :=
      map_nsmul (nsmulKerSubgroup H a).subtype d _
    rw [h2, ZeroMemClass.coe_zero]
    exact x.2)⟩
  left_inv z := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

private noncomputable def coprimeTorsionSplit (H : Type u) [AddCommGroup H] (a b : ℕ)
    (hco : Nat.Coprime a b) (hkill : ∀ x : H, (a * b) • x = 0) :
    H ≃+ (nsmulKerSubgroup H a × nsmulKerSubgroup H b) := by
  let q : Fin 2 → ℤ := fun i => if i = 0 then a else b
  have hicop : IsCoprime (a : ℤ) (b : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact hco
  have hq : ((Finset.univ : Finset (Fin 2)) : Set (Fin 2)).Pairwise
      (Function.onFun IsCoprime q) := by
    simp only [Finset.coe_univ, Set.pairwise_univ]
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hicop
    · exact hicop.symm
    · exact (hij rfl).elim
  have htors : Module.IsTorsionBy ℤ H (∏ i ∈ Finset.univ, q i) := by
    intro x
    have hx : ((a : ℤ) * (b : ℤ)) • x = 0 := by
      rw [← Nat.cast_mul, natCast_zsmul]
      exact hkill x
    simpa only [Finset.prod_filter, Finset.mem_univ, ↓reduceIte, Fin.prod_univ_two, q,
      if_pos, if_neg, Fin.zero_eta, Fin.isValue, one_ne_zero] using hx
  have hi := Submodule.torsionBy_isInternal (R := ℤ) (M := H) hq htors
  let i0 : (Finset.univ : Finset (Fin 2)) := ⟨0, Finset.mem_univ _⟩
  let i1 : (Finset.univ : Finset (Fin 2)) := ⟨1, Finset.mem_univ _⟩
  have hu : (Set.univ : Set (Finset.univ : Finset (Fin 2))) = {i0, i1} := by
    ext i
    constructor
    · intro _
      change i = i0 ∨ i = i1
      rcases i with ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Subtype.ext rfl)
      · exact Or.inr (Subtype.ext rfl)
    · exact fun _ => Set.mem_univ _
  have hc := DirectSum.IsInternal.isCompl (i := i0) (j := i1) (by decide) hu hi
  have hA : (nsmulKerSubgroup H a).toIntSubmodule =
      Submodule.torsionBy ℤ H (a : ℤ) := by
    ext x
    change a • x = 0 ↔ (a : ℤ) • x = 0
    rw [natCast_zsmul]
  have hB : (nsmulKerSubgroup H b).toIntSubmodule =
      Submodule.torsionBy ℤ H (b : ℤ) := by
    ext x
    change b • x = 0 ↔ (b : ℤ) • x = 0
    rw [natCast_zsmul]
  rw [show q i0 = a by rfl, show q i1 = b by rfl, ← hA, ← hB] at hc
  exact (Submodule.prodEquivOfIsCompl _ _ hc).symm.toAddEquiv

private def arrowProdAddEquiv (κ : Type) (A B : Type u) [AddCommGroup A]
    [AddCommGroup B] : ((κ → A) × (κ → B)) ≃+ (κ → A × B) where
  toFun x k := (x.1 k, x.2 k)
  invFun f := (fun k => (f k).1, fun k => (f k).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **Torsion-count characterisation of `(ℤ/N)²`** (pure group theory; T-B6e). A group
killed by `N ≠ 0` whose `d`-torsion has exactly `d ^ 2` elements for every divisor
`d` of `N` is isomorphic to `(Fin 2 → ZMod N)`. -/
theorem addEquiv_pi_fin_two_zmod_of_natCard (N : ℕ) (hN : N ≠ 0) (H : Type u)
    [AddCommGroup H] (hkill : ∀ x : H, N • x = 0)
    (hcount : ∀ d : ℕ, 0 < d → d ∣ N → Nat.card {x : H // d • x = 0} = d ^ 2) :
    Nonempty (H ≃+ (Fin 2 → ZMod N)) := by
  induction N using Nat.recOnPosPrimePosCoprime generalizing H with
  | prime_pow p n hp hn =>
    refine primePow_case p n hp hn H hkill fun j hj => ?_
    rw [hcount (p ^ j) (pow_pos hp.pos j) (pow_dvd_pow p hj)]
  | zero => exact absurd rfl hN
  | one =>
    refine ⟨{ toFun := fun _ => 0
              invFun := fun _ => 0
              left_inv := fun x => ?_
              right_inv := fun f => Subsingleton.elim _ _
              map_add' := fun _ _ => (add_zero 0).symm }⟩
    rw [← one_smul ℕ x, hkill x]
  | coprime a b ha hb hco iha ihb =>
    have haz : a ≠ 0 := by lia
    have hbz : b ≠ 0 := by lia
    have hkillA : ∀ z : nsmulKerSubgroup H a, a • z = 0 :=
      nsmulKerSubgroup_kill H a
    have hkillB : ∀ z : nsmulKerSubgroup H b, b • z = 0 :=
      nsmulKerSubgroup_kill H b
    have hcountA : ∀ d : ℕ, 0 < d → d ∣ a →
        Nat.card {z : nsmulKerSubgroup H a // d • z = 0} = d ^ 2 := by
      intro d hd hda
      rw [Nat.card_congr (nsmulKerSubgroupKerEquiv H a d hda)]
      exact hcount d hd (hda.trans (dvd_mul_right a b))
    have hcountB : ∀ d : ℕ, 0 < d → d ∣ b →
        Nat.card {z : nsmulKerSubgroup H b // d • z = 0} = d ^ 2 := by
      intro d hd hdb
      rw [Nat.card_congr (nsmulKerSubgroupKerEquiv H b d hdb)]
      exact hcount d hd (hdb.trans (dvd_mul_left b a))
    obtain ⟨ea⟩ := iha haz (nsmulKerSubgroup H a) hkillA hcountA
    obtain ⟨eb⟩ := ihb hbz (nsmulKerSubgroup H b) hkillB hcountB
    exact ⟨(coprimeTorsionSplit H a b hco hkill).trans
      ((AddEquiv.prodCongr ea eb).trans ((arrowProdAddEquiv (Fin 2) (ZMod a)
        (ZMod b)).trans (AddEquiv.piCongrRight fun _ =>
          (ZMod.chineseRemainder hco).symm.toAddEquiv)))⟩

end ModularCurves
