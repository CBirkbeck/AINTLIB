import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Torsion-count characterisation of `(ℤ/N)²`

A finite abelian group killed by `N` whose `d`-torsion has exactly `d ^ 2` elements for
every divisor `d` of `N` is isomorphic to `(ZMod N)²` (`addEquiv_pi_fin_two_zmod_of_card`).
This is the pure group-theory half of Silverman III.6.4(b)/KM 2.3.5 (ticket T-B6e): the
scheme-theoretic étale counting (`EtaleSectionsCount.lean`) produces exactly these
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

/-- The `p ^ j`-torsion of `ZMod (p ^ e)` has exactly `p ^ min j e` elements. -/
private lemma natCard_nsmul_ker_zmod (p e j : ℕ) (hp : p.Prime) :
    Nat.card {x : ZMod (p ^ e) // p ^ j • x = 0} = p ^ min j e := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  set m := min j e with hm
  set g : ZMod (p ^ e) := ((p ^ (e - m) : ℕ) : ZMod (p ^ e)) with hg
  have hme : m ≤ e := hm ▸ min_le_right j e
  have hmj : m ≤ j := hm ▸ min_le_left j e
  have hpj_g : p ^ j • g = 0 := by
    rw [hg, nsmul_eq_mul, ← Nat.cast_mul, ← pow_add]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr
      (pow_dvd_pow p (by omega : e ≤ j + (e - m)))
  have hmem : ∀ x : ZMod (p ^ e), p ^ j • x = 0 ↔ x ∈ zmultiples g := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := (ZMod.natCast_rightInverse (n := p ^ e)).surjective x
      have hdvd : p ^ e ∣ p ^ j * a := by
        rw [nsmul_eq_mul, ← Nat.cast_mul] at hx
        exact (ZMod.natCast_eq_zero_iff _ _).mp hx
      have hdvd2 : p ^ (e - m) ∣ a := by
        rcases le_or_gt e j with hej | hje
        · have hme' : e - m = 0 := by omega
          simp [hme']
        · have hmj' : m = j := hm ▸ min_eq_left hje.le
          have h1 : p ^ j * p ^ (e - j) ∣ p ^ j * a := by
            rw [← pow_add, Nat.add_sub_cancel' hje.le]
            exact hdvd
          rw [hmj']
          exact (mul_dvd_mul_iff_left (pow_ne_zero j hp.ne_zero)).mp h1
      refine mem_zmultiples_iff.mpr ⟨(a / p ^ (e - m) : ℕ), ?_⟩
      rw [natCast_zsmul, hg, nsmul_eq_mul, ← Nat.cast_mul,
        Nat.div_mul_cancel hdvd2]
    · intro hx
      obtain ⟨k, rfl⟩ := mem_zmultiples_iff.mp hx
      rw [smul_comm, hpj_g, smul_zero]
  have hcard1 : Nat.card {x : ZMod (p ^ e) // p ^ j • x = 0} =
      Nat.card (zmultiples g) :=
    Nat.card_congr (Equiv.subtypeEquivRight hmem)
  rw [hcard1, Nat.card_zmultiples, hg, ZMod.addOrderOf_coe _ (pow_ne_zero e hp.ne_zero),
    Nat.gcd_eq_right (pow_dvd_pow p (Nat.sub_le e m)), Nat.pow_div (Nat.sub_le e m) hp.pos,
    Nat.sub_sub_self hme]

/-- The `d`-torsion of `ZMod n` is trivial when `d` is coprime to `n`. -/
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
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨0, smul_zero d⟩⟩
    have hu : IsUnit (d : ZMod n) := (ZMod.isUnit_iff_coprime d n).mpr hd
    have hx := x.2
    have hy := y.2
    rw [nsmul_eq_mul] at hx hy
    have hx0 : (x.1 : ZMod n) = 0 :=
      hu.mul_left_cancel (hx.trans (mul_zero ((d : ℕ) : ZMod n)).symm)
    have hy0 : (y.1 : ZMod n) = 0 :=
      hu.mul_left_cancel (hy.trans (mul_zero ((d : ℕ) : ZMod n)).symm)
    rw [hx0, hy0]

/-- Transport of `d`-torsion along an additive equivalence. -/
private def nsmulKerCongr {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H)
    (d : ℕ) : {x : G // d • x = 0} ≃ {y : H // d • y = 0} :=
  Equiv.subtypeEquiv e.toEquiv fun x => by
    show d • x = 0 ↔ d • e x = 0
    constructor
    · intro h
      rw [← map_nsmul, h, map_zero]
    · intro h
      have h2 : e (d • x) = e 0 := by
        rw [map_nsmul, map_zero]
        exact h
      exact e.injective h2

/-- The `d`-torsion of a finite product is the product of the `d`-torsions. -/
private def nsmulKerPiEquiv {ι : Type} (M : ι → Type u) [∀ i, AddCommGroup (M i)]
    (d : ℕ) : {x : ∀ i, M i // d • x = 0} ≃ ∀ i, {y : M i // d • y = 0} where
  toFun x i := ⟨x.1 i, congrFun x.2 i⟩
  invFun y := ⟨fun i => (y i).1, funext fun i => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `d`-torsion count of a finite direct sum of `ZMod (n i)`s. -/
private lemma natCard_nsmul_ker_directSum {ι : Type} [Fintype ι] (n : ι → ℕ) (d : ℕ) :
    Nat.card {x : (⨁ i, ZMod (n i)) // d • x = 0} =
      ∏ i, Nat.card {y : ZMod (n i) // d • y = 0} := by
  rw [Nat.card_congr ((nsmulKerCongr (DirectSum.addEquivProd fun i => ZMod (n i))
    d).trans (nsmulKerPiEquiv (fun i => ZMod (n i)) d))]
  exact Nat.card_pi

/-- A dependent product all of whose components except two are trivial is the product of
those two components. -/
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
      simp
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

/-- The prime-power case: an abelian group killed by `p ^ v` whose `p ^ j`-torsion has
`(p ^ j) ^ 2` elements for all `j ≤ v` is `(ZMod (p ^ v))²`. -/
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
  have hdvd : ∀ i, P i ^ E i ∣ p ^ v := by
    intro i
    have h1 : p ^ v • (DirectSum.of (fun i => ZMod (P i ^ E i)) i 1) = 0 := by
      have h2 := congrArg e (hkill (e.symm (DirectSum.of (fun i => ZMod (P i ^ E i)) i 1)))
      rwa [map_nsmul, e.apply_symm_apply, map_zero] at h2
    have h5 : p ^ v • (1 : ZMod (P i ^ E i)) = 0 := by
      have h1' : DirectSum.of (fun i => ZMod (P i ^ E i)) i (p ^ v • 1) = 0 := by
        rw [map_nsmul]
        exact h1
      have h6 := congrArg (fun z => z i) h1'
      simpa [DirectSum.of_eq_same] using h6
    rw [← ZMod.addOrderOf_one (P i ^ E i)]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h5
  have hPp : ∀ i, E i ≠ 0 → P i = p := by
    intro i hE
    have h1 : P i ∣ p ^ v := (dvd_pow_self (P i) hE).trans (hdvd i)
    exact (Nat.prime_dvd_prime_iff_eq (hP i) hp).mp ((hP i).dvd_of_dvd_pow h1)
  have hEv : ∀ i, E i ≤ v := by
    intro i
    rcases eq_or_ne (E i) 0 with hE | hE
    · omega
    · have h1 := hdvd i
      rw [hPp i hE] at h1
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1
  have hsum : ∀ j : ℕ, j ≤ v → ∑ i, min j (E i) = 2 * j := by
    intro j hj
    have hprod : ∏ i, Nat.card {y : ZMod (P i ^ E i) // p ^ j • y = 0} = (p ^ j) ^ 2 := by
      rw [← natCard_nsmul_ker_directSum (fun i => P i ^ E i) (p ^ j),
        ← Nat.card_congr (nsmulKerCongr e (p ^ j))]
      exact hcount j hj
    have hterm : ∀ i, Nat.card {y : ZMod (P i ^ E i) // p ^ j • y = 0} =
        p ^ min j (E i) := by
      intro i
      rcases eq_or_ne (E i) 0 with hE | hE
      · rw [natCard_nsmul_ker_zmod_of_coprime _ _
          (by rw [hE, pow_zero]; exact Nat.coprime_one_right _), hE]
        simp
      · rw [hPp i hE]
        exact natCard_nsmul_ker_zmod p (E i) j hp
    rw [Finset.prod_congr rfl fun i _ => hterm i, Finset.prod_pow_eq_pow_sum, ← pow_mul,
      mul_comm j 2] at hprod
    exact Nat.pow_right_injective hp.two_le hprod
  set σ : Finset ι := Finset.univ.filter (fun i => E i ≠ 0) with hσdef
  have hσcard : σ.card = 2 := by
    have h1 := hsum 1 hv
    have h2 : ∑ i, min 1 (E i) = σ.card := by
      rw [hσdef, Finset.card_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases eq_or_ne (E i) 0 with hE | hE
      · simp [hE]
      · simp [Nat.min_eq_left (Nat.one_le_iff_ne_zero.mpr hE), hE]
    omega
  obtain ⟨i₁, i₂, hne12, hσeq⟩ := Finset.card_eq_two.mp hσcard
  have hmem : ∀ i, i ∈ σ ↔ E i ≠ 0 := by
    intro i
    rw [hσdef]
    simp
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
    omega
  have hE2 : E i₂ = v := by
    have := hEv i₁
    omega
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

/-- The `a`-torsion, as an additive subgroup. -/
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
  have h1 : a • (z : H) = 0 := z.2
  exact Subtype.ext (by
    rw [← h1]
    exact map_nsmul (nsmulKerSubgroup H a).subtype a z)

/-- Count transfer: the `d`-torsion of the `a`-torsion subgroup is the `d`-torsion,
for `d ∣ a`. -/
private def nsmulKerSubgroupKerEquiv (H : Type u) [AddCommGroup H] (a d : ℕ)
    (hda : d ∣ a) :
    {z : nsmulKerSubgroup H a // d • z = 0} ≃ {x : H // d • x = 0} where
  toFun z := ⟨z.1.1, by
    have h1 := congrArg ((nsmulKerSubgroup H a).subtype) z.2
    rwa [map_nsmul, map_zero] at h1⟩
  invFun x := ⟨⟨x.1, by
      obtain ⟨c, hc⟩ := hda
      show a • x.1 = 0
      rw [hc, mul_comm d c, mul_smul, x.2, smul_zero]⟩,
    Subtype.ext (by
      have h1 : d • x.1 = 0 := x.2
      rw [← h1]
      exact map_nsmul (nsmulKerSubgroup H a).subtype d _)⟩
  left_inv z := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

/-- Bezout splitting of a group killed by a coprime product into its two torsion parts. -/
private noncomputable def coprimeTorsionSplit (H : Type u) [AddCommGroup H] (a b : ℕ)
    (hco : Nat.Coprime a b) (hkill : ∀ x : H, (a * b) • x = 0) :
    H ≃+ (nsmulKerSubgroup H a × nsmulKerSubgroup H b) := by
  have hicop : IsCoprime (a : ℤ) (b : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact hco
  obtain ⟨u, w, huw⟩ := hicop
  have hkillZ : ∀ x : H, ((a : ℤ) * (b : ℤ)) • x = 0 := by
    intro x
    have h1 : ((a * b : ℕ) : ℤ) • x = 0 := by
      rw [natCast_zsmul]
      exact hkill x
    rwa [Nat.cast_mul] at h1
  have hmemA : ∀ x : H, (w * b) • x ∈ nsmulKerSubgroup H a := by
    intro x
    show a • ((w * (b : ℤ)) • x) = 0
    rw [← natCast_zsmul, smul_smul,
      show (a : ℤ) * (w * b) = w * ((a : ℤ) * b) from by ring, ← smul_smul, hkillZ,
      smul_zero]
  have hmemB : ∀ x : H, (u * a) • x ∈ nsmulKerSubgroup H b := by
    intro x
    show b • ((u * (a : ℤ)) • x) = 0
    rw [← natCast_zsmul, smul_smul,
      show (b : ℤ) * (u * a) = u * ((a : ℤ) * b) from by ring, ← smul_smul, hkillZ,
      smul_zero]
  refine
    { toFun := fun x => (⟨(w * b) • x, hmemA x⟩, ⟨(u * a) • x, hmemB x⟩)
      invFun := fun y => y.1.1 + y.2.1
      left_inv := fun x => ?_
      right_inv := fun y => ?_
      map_add' := fun x y => ?_ }
  · show (w * (b : ℤ)) • x + (u * (a : ℤ)) • x = x
    rw [← add_zsmul, show w * (b : ℤ) + u * a = u * a + w * b from by ring, huw, one_zsmul]
  · have hby1 : (w * (b : ℤ)) • (y.1.1 : H) = y.1.1 := by
      have hay : (a : ℤ) • (y.1.1 : H) = 0 := by
        rw [natCast_zsmul]
        exact y.1.2
      have h2 : (w * (b : ℤ)) • (y.1.1 : H) = (1 - u * a) • (y.1.1 : H) := by
        rw [show (1 : ℤ) - u * a = w * b from by linarith [huw]]
      rw [h2, sub_zsmul, one_zsmul, smul_smul, ← smul_smul, hay, smul_zero, sub_zero]
    have hbz0 : (w * (b : ℤ)) • (y.2.1 : H) = 0 := by
      have hby : (b : ℤ) • (y.2.1 : H) = 0 := by
        rw [natCast_zsmul]
        exact y.2.2
      rw [smul_smul, ← smul_smul, hby, smul_zero]
    have haz1 : (u * (a : ℤ)) • (y.2.1 : H) = y.2.1 := by
      have hby : (b : ℤ) • (y.2.1 : H) = 0 := by
        rw [natCast_zsmul]
        exact y.2.2
      have h2 : (u * (a : ℤ)) • (y.2.1 : H) = (1 - w * b) • (y.2.1 : H) := by
        rw [show (1 : ℤ) - w * b = u * a from by linarith [huw]]
      rw [h2, sub_zsmul, one_zsmul, smul_smul, ← smul_smul, hby, smul_zero, sub_zero]
    have hay0 : (u * (a : ℤ)) • (y.1.1 : H) = 0 := by
      have hay : (a : ℤ) • (y.1.1 : H) = 0 := by
        rw [natCast_zsmul]
        exact y.1.2
      rw [smul_smul, ← smul_smul, hay, smul_zero]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (w * (b : ℤ)) • (y.1.1 + y.2.1) = (y.1.1 : H)
      rw [smul_add, hby1, hbz0, add_zero]
    · show (u * (a : ℤ)) • (y.1.1 + y.2.1) = (y.2.1 : H)
      rw [smul_add, hay0, haz1, zero_add]
  · refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (w * (b : ℤ)) • (x + y) = (w * (b : ℤ)) • x + (w * (b : ℤ)) • y
      rw [smul_add]
    · show (u * (a : ℤ)) • (x + y) = (u * (a : ℤ)) • x + (u * (a : ℤ)) • y
      rw [smul_add]

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
    refine primePow_case p n hp.nat_prime hn H hkill fun j hj => ?_
    rw [hcount (p ^ j) (pow_pos hp.nat_prime.pos j) (pow_dvd_pow p hj)]
  | zero => exact absurd rfl hN
  | one =>
    refine ⟨{ toFun := fun _ => 0
              invFun := fun _ => 0
              left_inv := fun x => ?_
              right_inv := fun f => Subsingleton.elim _ _
              map_add' := fun _ _ => (add_zero 0).symm }⟩
    rw [← one_smul ℕ x, hkill x]
  | coprime a b ha hb hco iha ihb =>
    have haz : a ≠ 0 := by omega
    have hbz : b ≠ 0 := by omega
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
