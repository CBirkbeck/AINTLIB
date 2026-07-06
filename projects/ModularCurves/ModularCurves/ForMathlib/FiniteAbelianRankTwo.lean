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

end ModularCurves
