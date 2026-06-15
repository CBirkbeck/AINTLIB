/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.AtkinLehner

/-!
# Hecke Ring for Congruence Subgroups (Shimura §3.3) — Polynomial presentation

The free polynomial presentation `π : ℤ[X_{(p,k)}] →+* HeckeAlgebra 2`
(surjective, `π_surjective`), the target ring hom
`ψ : ℤ[X_{(p,k)}] →+* 𝕋 (Γ₀(N)) ℤ`, and the factorization machinery
(`Gamma0_exists_diag_rep`, `cosetMap_T_diag_Gamma0`, `mulMap_Gamma0_coprime_eq`)
that feeds Shimura Theorem 3.35.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.3
-/

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

/-- Index type for all p-local generators: `(p, k)` with `p` prime, `k ∈ Fin 2`. -/
abbrev GenIdx := { p : ℕ // p.Prime } × Fin 2

/-- The free polynomial ring on all Hecke algebra generators. -/
private abbrev FreeHecke := MvPolynomial GenIdx ℤ

/-- The presentation map `π : ℤ[X_{(p,k)}] →+* HeckeAlgebra 2`. -/
noncomputable def π_hom : FreeHecke →+* HeckeAlgebra 2 :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (fun ⟨⟨p, _⟩, k⟩ ↦ T_gen 2 p k)

/-- The p-local embedding `ℤ[X₀, X₁] ↪ ℤ[X_{(p,k)}]`. -/
private noncomputable def embedPoly (p : ℕ) (hp : p.Prime) :
    MvPolynomial (Fin 2) ℤ →+* FreeHecke :=
  (MvPolynomial.rename (fun k : Fin 2 ↦ (⟨⟨p, hp⟩, k⟩ : GenIdx))).toRingHom

/-- `π ∘ embedPoly p = evalHom 2 p`. -/
private lemma π_comp_embed (p : ℕ) (hp : p.Prime) :
    π_hom.comp (embedPoly p hp) = evalHom 2 p := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [π_hom, embedPoly, evalHom]
  · intro i
    show π_hom (embedPoly p hp (MvPolynomial.X i)) = evalHom 2 p (MvPolynomial.X i)
    have h1 : embedPoly p hp (MvPolynomial.X i) =
        MvPolynomial.X (⟨⟨p, hp⟩, i⟩ : GenIdx) := by
      simp [embedPoly, MvPolynomial.rename_X]
    rw [h1]
    have h2 : π_hom (MvPolynomial.X (⟨⟨p, hp⟩, i⟩ : GenIdx)) = T_gen 2 p i := by
      show (MvPolynomial.eval₂Hom (Int.castRingHom (HeckeAlgebra 2))
        (fun x : GenIdx ↦ T_gen 2 x.1.1 x.2)) (MvPolynomial.X (⟨⟨p, hp⟩, i⟩ : GenIdx)) =
        T_gen 2 p i
      exact MvPolynomial.eval₂Hom_X' _ _ _
    have h3 : evalHom 2 p (MvPolynomial.X i) = T_gen 2 p i := by
      show (MvPolynomial.eval₂Hom (Int.castRingHom (HeckeAlgebra 2))
        (fun k : Fin 2 ↦ T_gen 2 p k)) (MvPolynomial.X i) = T_gen 2 p i
      exact MvPolynomial.eval₂Hom_X' _ _ _
    rw [h2, h3]

/-- Each p-power-diagonal T_elem is in the range of π. -/
private lemma ppow_mem_π_range (p : ℕ) (hp : p.Prime)
    (e : Fin 2 → ℕ) (he : Monotone e) :
    T_elem (ppowDiag 2 p e) ∈ π_hom.range := by
  obtain ⟨poly, hpoly⟩ := Surj.T_gen_generates_R_p_two p hp
    (T_elem (ppowDiag 2 p e)) (T_elem_ppow_mem_R_p 2 p hp e he)
  rw [show evalHom 2 p = π_hom.comp (embedPoly p hp) from
    (π_comp_embed p hp).symm] at hpoly
  exact ⟨embedPoly p hp poly, hpoly⟩

/-- Removing the p-component strictly decreases the product when p divides it. -/
private lemma prod_removePrime_lt (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (p : ℕ) (hp : p.Prime) (hp_dvd : p ∣ ∏ i, a i) :
    ∏ i, removePrime 2 p a i < ∏ i, a i := by
  refine Finset.prod_lt_prod (fun i _ ↦ removePrime_pos 2 p a ha i)
    (fun i _ ↦ Nat.le_of_dvd (ha i) (Nat.ordCompl_dvd (a i) p)) ?_
  simp only [Fin.prod_univ_two] at hp_dvd
  have strict (i : Fin 2) (hi : p ∣ a i) : removePrime 2 p a i < a i := by
    simp only [removePrime]
    exact Nat.div_lt_self (ha i)
      (one_lt_pow₀ hp.one_lt (hp.factorization_pos_of_dvd (ha i).ne' hi).ne')
  obtain hi | hi := hp.dvd_mul.mp hp_dvd
  · exact ⟨0, Finset.mem_univ _, strict 0 hi⟩
  · exact ⟨1, Finset.mem_univ _, strict 1 hi⟩

/-- Every `T_elem a` is in the range of `π`, by strong induction on `∏ a`. -/
private lemma T_elem_mem_π_range (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (hdiv : DivChain 2 a) : T_elem a ∈ π_hom.range := by
  suffices ∀ (n : ℕ) (a : Fin 2 → ℕ), (∀ i, 0 < a i) → DivChain 2 a →
      ∏ i, a i = n → T_elem a ∈ π_hom.range by
    exact this _ a ha hdiv rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a ha hdiv hprod
    by_cases h_one : n = 1
    · subst h_one
      obtain rfl : a = fun _ ↦ 1 := funext fun i ↦ Nat.eq_one_of_dvd_one
        (hprod ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
      rw [T_elem_ones_eq_one 2]
      exact π_hom.range.one_mem'
    · obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (by lia : n ≠ 1)
      rw [T_elem_split_prime 2 a ha hdiv p hp]
      apply π_hom.range.mul_mem
      · exact ppow_mem_π_range p hp _ (pComponent_monotone 2 a ha hdiv p)
      · have h_lt : ∏ i, removePrime 2 p a i < n :=
          hprod ▸ prod_removePrime_lt a ha p hp (hprod ▸ hp_dvd)
        exact ih _ h_lt _ (removePrime_pos 2 p a ha)
          (removePrime_divChain 2 p a hdiv) rfl

/-- The presentation map `π` is surjective. -/
lemma π_surjective : Function.Surjective π_hom := by
  rw [← RingHom.range_eq_top, eq_top_iff]
  intro f _
  obtain ⟨S, c, hf⟩ := T_diag_span 2 f
  rw [hf]
  exact π_hom.range.sum_mem fun s _ ↦
    π_hom.range.zsmul_mem (T_elem_mem_π_range s.1.1 s.1.2.1 s.1.2.2) _

variable (N : ℕ) [NeZero N]

/-- The target ring hom `ψ : ℤ[X_{(p,k)}] →+* 𝕋 (Gamma0_pair N) ℤ`:
    `X_{(p,0)} ↦ T'(1,p)`, `X_{(p,1)} ↦ T'(p,p)` if `p ∤ N` else `0`. -/
noncomputable def ψ_hom :
    FreeHecke →+* HeckeRing.𝕋 (Gamma0_pair N) ℤ :=
  @MvPolynomial.eval₂Hom _ _ _ _ (instCommRing_Gamma0 N).toCommSemiring
    (Int.castRingHom _) (fun ⟨⟨p, hp⟩, k⟩ ↦
    if k = 0 then
      HeckeRing.T_single (Gamma0_pair N) ℤ
        (T_diag_Gamma0 N (![1, p])
          (fun i ↦ by fin_cases i <;> simp [hp.pos])
          (by simp)) 1
    else if h : p ∣ N then 0
    else
      HeckeRing.T_single (Gamma0_pair N) ℤ
        (T_diag_Gamma0 N (![p, p])
          (fun i ↦ by fin_cases i <;> simp [hp.pos])
          (by show Int.gcd (↑p) ↑N = 1
              rw [Int.gcd_natCast_natCast]
              exact hp.coprime_iff_not_dvd.mpr h)) 1)

/-- Every Gamma0 double coset equals `T_diag_Gamma0 N (![1, m])` for some `m > 0`:
any `g ∈ Δ₀(N)` with integer matrix `A`, `gcd(A 0 0, det) = 1`, has
`⟦g⟧ = T_diag_Gamma0 N (![1, m])` where `m = det(A).natAbs`. -/
private lemma Gamma0_coset_eq_T_diag_of_coprime (N : ℕ) [NeZero N]
    (g : (Gamma0_pair N).Δ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g.1 : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0)
    (m : ℕ) (hm_pos : 0 < m) (hdet : g.1.val.det = (m : ℚ))
    (ham : Int.gcd (A 0 0) (m : ℤ) = 1) :
    (⟦g⟧ : HeckeCoset (Gamma0_pair N)) =
      T_diag_Gamma0 N (![1, m])
        (fun i ↦ by fin_cases i <;> simp [hm_pos])
        (by simp) :=
  HeckeCoset.eq_mk_of_mem (shimura_prop_3_33_gen N m hm_pos g.1 g.2 A hA hAN hdet ham)

/-- The cofactor `c = m / gcd(m, Nᵐ)` is coprime to `N`: any common prime `p₀` would,
by `m = (gcd m Nᵐ) * c`, force `p₀ ^ k ∣ m` for all `k`, contradicting `m > 0`. -/
private lemma cofactor_coprime_to_level (m N : ℕ) (hm_pos : 0 < m)
    (c : ℕ) (hbc : m = Nat.gcd m (N ^ m) * c) : Nat.Coprime c N := by
  rw [Nat.coprime_comm]
  by_contra h_nc
  obtain ⟨p₀, hp₀, hpg⟩ := Nat.exists_prime_and_dvd h_nc
  obtain ⟨hp₀N, hp₀c⟩ := Nat.dvd_gcd_iff.mp hpg
  suffices ∀ k, p₀ ^ k ∣ m from absurd (Nat.le_of_dvd hm_pos (this (m + 1)))
    (not_le.mpr ((Nat.lt_pow_self hp₀.one_lt).trans_le
      (Nat.pow_le_pow_right hp₀.pos (Nat.le_succ m))))
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hbc, pow_succ]
    exact mul_dvd_mul (Nat.dvd_gcd ih ((pow_dvd_pow_of_dvd hp₀N k).trans
      (Nat.pow_dvd_pow N ((Nat.lt_pow_self hp₀.one_lt).le.trans
        (Nat.le_of_dvd hm_pos ih))))) hp₀c

/-- For the two-sided coprime rep `A'`, `gcd(A' 0 0, m) = 1` where `m = b * c`,
`b = gcd(m, Nᵐ) ∣ Nᵐ`, using `gcd(A' 0 0, N) = 1` and `gcd(A' 0 0, c) = 1`. -/
private lemma coprime_rep_gcd_with_det (m N : ℕ) (c : ℕ) (b : ℕ)
    (hbc : m = b * c) (hb_dvd : b ∣ N ^ m) (A' : Matrix (Fin 2) (Fin 2) ℤ)
    (hA'Nco : Int.gcd (A' 0 0) N = 1) (hA'c : Int.gcd (A' 0 0) c = 1) :
    Int.gcd (A' 0 0) (m : ℤ) = 1 := by
  rw [show (m : ℤ) = ↑b * ↑c by exact_mod_cast hbc]
  exact Int.isCoprime_iff_gcd_eq_one.mp (IsCoprime.mul_right
    (IsCoprime.of_isCoprime_of_dvd_right
      ((Int.isCoprime_iff_gcd_eq_one.mpr hA'Nco).pow_right (n := m))
      (by exact_mod_cast hb_dvd))
    (Int.isCoprime_iff_gcd_eq_one.mpr hA'c))

/-- The Γ₀(N)-conjugate `g' = γL * g * γR` has the same determinant as `g`,
since `γL, γR ∈ Γ₀(N) ⊆ SL₂(ℤ)` have determinant `1`. -/
private lemma two_sided_conj_det (N : ℕ) [NeZero N]
    (g : (Gamma0_pair N).Δ) (γL γR : (Gamma0_pair N).H) (m : ℕ)
    (hdet_m : g.1.val.det = (m : ℚ)) :
    ((γL : GL (Fin 2) ℚ) * g.1 * (γR : GL (Fin 2) ℚ)).val.det = (m : ℚ) := by
  have hdet1 (γ : (Gamma0_pair N).H) : (γ.1 : GL (Fin 2) ℚ).val.det = 1 := by
    obtain ⟨σ, _, hσ⟩ := Subgroup.mem_map.mp γ.2
    rw [← hσ]
    simp [mapGL_coe_matrix, algebraMap_int_eq, det_intMat_cast, σ.prop]
  simp only [Units.val_mul, Matrix.det_mul, hdet1 γL, hdet1 γR, one_mul, mul_one, hdet_m]

/-- The content `d = gcd` of the four matrix entries divides every entry of `A`. -/
private lemma content_gcd_dvd_entries (A : Matrix (Fin 2) (Fin 2) ℤ)
    (d : ℕ) (hd_def : d = Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
      (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs)) :
    ∀ i j : Fin 2, (d : ℤ) ∣ A i j := by
  intro i j
  apply Int.natAbs_dvd_natAbs.mp
  fin_cases i <;> fin_cases j <;> (rw [hd_def]; first
    | exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    | exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
    | exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    | exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))

/-- The content `d` is positive: otherwise all entries of `A` vanish, forcing `det A = 0`,
contradicting `det A > 0`. -/
private lemma content_gcd_pos (A : Matrix (Fin 2) (Fin 2) ℤ) (d : ℕ)
    (hd_dvd : ∀ i j : Fin 2, (d : ℤ) ∣ A i j) (hA_det_pos : 0 < A.det) :
    0 < d := Nat.pos_of_ne_zero fun h ↦ by
  have h00 := hd_dvd 0 0; have h01 := hd_dvd 0 1
  have h10 := hd_dvd 1 0; have h11 := hd_dvd 1 1
  simp [h] at h00 h01 h10 h11
  linarith [show A.det = 0 by rw [Matrix.det_fin_two]; simp [h00, h01, h10, h11]]

/-- Content-scaling double-coset membership: if `g₀` (matrix `A₀`) lies in the double
coset of `diag(a₀)` via `γ₁, γ₂`, and `A = d • A₀`, `a = d • a₀`, then `g` (matrix `A`)
lies in the double coset of `diag(a)` via the *same* `γ₁, γ₂`. -/
private lemma content_scaled_doubleCoset_mem (N : ℕ) [NeZero N]
    (g g₀ : (Gamma0_pair N).Δ) (γ₁ γ₂ : GL (Fin 2) ℚ)
    (A A₀ : Matrix (Fin 2) (Fin 2) ℤ) (d : ℕ) (a a₀ : Fin 2 → ℕ)
    (hA : (g.1 : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hg₀_val : (g₀.1 : Matrix (Fin 2) (Fin 2) ℚ) = A₀.map (Int.cast : ℤ → ℚ))
    (hA₀_eq : ∀ i j, A i j = ↑d * A₀ i j) (ha₀_def : a = fun i ↦ d * a₀ i)
    (ha : ∀ i, 0 < a i) (ha₀ : ∀ i, 0 < a₀ i)
    (hγ₁ : γ₁ ∈ ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)))
    (hγ₂ : γ₂ ∈ ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)))
    (hg₀_eq : g₀.1 = γ₁ * diagMat 2 a₀ * γ₂) :
    g.1 ∈ DoubleCoset.doubleCoset (diagMat 2 a : GL (Fin 2) ℚ)
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨γ₁, hγ₁, γ₂, hγ₂, Units.ext ?_⟩
  ext i j
  have hg₀_ij : g₀.1.val i j = (γ₁ * diagMat 2 a₀ * γ₂).val i j :=
    congr_fun₂ (show g₀.1.val = (γ₁ * diagMat 2 a₀ * γ₂).val by rw [hg₀_eq]) i j
  have hg_ij : g.1.val i j = (d : ℚ) * g₀.1.val i j := by
    have h1 := congr_fun₂ hA i j
    rw [hg₀_val]
    simp only [Matrix.map_apply] at h1 ⊢
    rw [h1]; push_cast [hA₀_eq i j]; ring
  have hd_kl : ∀ k l : Fin 2, (diagMat 2 a : GL _ ℚ).val k l =
      (d : ℚ) * (diagMat 2 a₀ : GL _ ℚ).val k l := fun k l ↦ by
    rw [diagMat_val 2 a ha, diagMat_val 2 a₀ ha₀]
    simp only [Matrix.diagonal_apply, ha₀_def]
    split_ifs with heq <;> simp
  change g.1.val i j = (γ₁ * (diagMat 2 a : GL _ ℚ) * γ₂).val i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at hg₀_ij ⊢
  rw [hg_ij, hg₀_ij, hd_kl 0 0, hd_kl 0 1, hd_kl 1 0, hd_kl 1 1]
  ring

/-- Extracting a common prime factor `p` from `A = d • A₀` strictly decreases `|det|`:
since `p ∣ d`, `d ≥ 2`, so `|det A| = d² · |det A₀| ≥ 4·|det A₀| > |det A₀|`.
This is the well-founded descent bound for `Gamma0_exists_diag_rep`. -/
private lemma content_quotient_det_natAbs_lt (A A₀ : Matrix (Fin 2) (Fin 2) ℤ)
    (d p : ℕ) (hp : p.Prime) (hd_pos : 0 < d) (hp_dvd_d : p ∣ d)
    (hA₀_eq : ∀ i j, A i j = ↑d * A₀ i j) (hA₀_det_pos : 0 < A₀.det) :
    A₀.det.natAbs < A.det.natAbs := by
  have hdet_eq : A.det = (d : ℤ) ^ 2 * A₀.det := by
    simp only [Matrix.det_fin_two]
    rw [hA₀_eq 0 0, hA₀_eq 0 1, hA₀_eq 1 0, hA₀_eq 1 1]; ring
  rw [hdet_eq, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  have hA₀_na : 0 < A₀.det.natAbs := Int.natAbs_pos.mpr hA₀_det_pos.ne'
  calc A₀.det.natAbs < 2 * A₀.det.natAbs := by lia
    _ ≤ d ^ 2 * A₀.det.natAbs := Nat.mul_le_mul_right _ <| by
        nlinarith [hp.two_le.trans (Nat.le_of_dvd hd_pos hp_dvd_d)]

/-- **Primitive case** of `Gamma0_exists_diag_rep`: when no prime divides all four
entries of `A`, `⟦g⟧ = T_diag_Gamma0 N (![1, m])` with `m = |det A|`. If `gcd(A 0 0, m) = 1`
apply directly; otherwise two-sided `Γ₀(N)`-clear via `Gamma0_two_sided_coprime_rep_prim`. -/
private lemma Gamma0_exists_diag_rep_primitive (N : ℕ) [NeZero N]
    (g : (Gamma0_pair N).Δ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g.1 : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco : Int.gcd (A 0 0) N = 1) (hA_det_pos : 0 < A.det)
    (hprim : ∀ (p : ℕ), p.Prime →
      ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧ (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1)) :
    ∃ (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1)
      (_ : a 0 ∣ a 1),
      (⟦g⟧ : HeckeCoset (Gamma0_pair N)) = T_diag_Gamma0 N a ha hgcd := by
  set m := A.det.natAbs
  have hm_pos : 0 < m := Int.natAbs_pos.mpr hA_det_pos.ne'
  have hA_det_eq : A.det = (m : ℤ) :=
    (abs_of_pos hA_det_pos ▸ Int.natCast_natAbs A.det).symm
  have hdet_m : g.1.val.det = (m : ℚ) := by
    rw [hA, det_intMat_cast]
    exact_mod_cast hA_det_eq
  by_cases ham : Int.gcd (A 0 0) (m : ℤ) = 1
  · exact ⟨![1, m], fun i ↦ by fin_cases i <;> simp [hm_pos], by simp, ⟨m, by simp⟩,
      Gamma0_coset_eq_T_diag_of_coprime N g A hA hAN m hm_pos hdet_m ham⟩
  · set b := Nat.gcd m (N ^ m)
    set c := m / b
    have hbc : m = b * c := (Nat.mul_div_cancel' (Nat.gcd_dvd_left m _)).symm
    have hc_pos : 0 < c := Nat.pos_of_ne_zero fun hc0 ↦ by
      rw [hc0, Nat.mul_zero] at hbc; lia
    have hc_dvd : (c : ℤ) ∣ A.det := by
      rw [hA_det_eq]; exact_mod_cast show c ∣ m from Dvd.intro_left b hbc.symm
    obtain ⟨γL, γR, A', hA', hA'N, hA'Nco, hA'c⟩ :=
      Gamma0_two_sided_coprime_rep_prim N g.1 g.2 A hA hAN hAco hprim c hc_pos
        (cofactor_coprime_to_level m N hm_pos c hbc) hc_dvd
    set g' : (Gamma0_pair N).Δ := ⟨(γL : GL _ ℚ) * g.1 * (γR : GL _ ℚ),
      (Gamma0_pair N).Δ.mul_mem ((Gamma0_pair N).Δ.mul_mem
        ((Gamma0_pair N).h₀ γL.2) g.2) ((Gamma0_pair N).h₀ γR.2)⟩
    have hg'_coset : (⟦g'⟧ : HeckeCoset (Gamma0_pair N)) = ⟦g⟧ :=
      HeckeCoset.eq_mk_of_mem (DoubleCoset.mem_doubleCoset.mpr ⟨γL, γL.2, γR, γR.2, rfl⟩)
    rw [← hg'_coset]
    exact ⟨![1, m], fun i ↦ by fin_cases i <;> simp [hm_pos], by simp, ⟨m, by simp⟩,
      Gamma0_coset_eq_T_diag_of_coprime N g' A' hA' hA'N m hm_pos
        (two_sided_conj_det N g γL γR m hdet_m)
        (coprime_rep_gcd_with_det m N c b hbc (Nat.gcd_dvd_right m (N ^ m)) A' hA'Nco hA'c)⟩

/-- **Content scale-back** for `Gamma0_exists_diag_rep`: given the primitive quotient `g₀`
(matrix `A₀ = A / d`) with diagonal representative `⟦g₀⟧ = T_diag_Gamma0 N a₀`, scale back by
the content `d` to obtain `⟦g⟧ = T_diag_Gamma0 N (d • a₀)`. Consumes the inductive
hypothesis `hrep₀`, so it is independent of the well-founded recursion. -/
private lemma Gamma0_diag_rep_scale_back (N : ℕ) [NeZero N]
    (g g₀ : (Gamma0_pair N).Δ)
    (A A₀ : Matrix (Fin 2) (Fin 2) ℤ) (d : ℕ)
    (hA : (g.1 : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hg₀_val : (g₀.1 : Matrix (Fin 2) (Fin 2) ℚ) = A₀.map (Int.cast : ℤ → ℚ))
    (hA₀_eq : ∀ i j, A i j = ↑d * A₀ i j)
    (hd_pos : 0 < d) (hd_dvd : ∀ i j : Fin 2, (d : ℤ) ∣ A i j)
    (hAco : Int.gcd (A 0 0) N = 1)
    (a₀ : Fin 2 → ℕ) (ha₀ : ∀ i, 0 < a₀ i) (hgcd₀ : Int.gcd (a₀ 0) N = 1)
    (hdiv₀ : a₀ 0 ∣ a₀ 1)
    (hrep₀ : (⟦g₀⟧ : HeckeCoset (Gamma0_pair N)) = T_diag_Gamma0 N a₀ ha₀ hgcd₀) :
    ∃ (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1)
      (_ : a 0 ∣ a 1),
      (⟦g⟧ : HeckeCoset (Gamma0_pair N)) = T_diag_Gamma0 N a ha hgcd := by
  have hg₀_dc : g₀.1 ∈ DoubleCoset.doubleCoset (diagMat 2 a₀ : GL (Fin 2) ℚ)
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) :=
    ((HeckeCoset.eq_iff g₀ ⟨_, diagMat_mem_Delta0_of_gcd N a₀ ha₀ hgcd₀⟩).mp hrep₀).symm ▸
      DoubleCoset.mem_doubleCoset_self _ _ g₀.1
  rw [DoubleCoset.mem_doubleCoset] at hg₀_dc
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hg₀_eq⟩ := hg₀_dc
  set a := fun i : Fin 2 ↦ d * a₀ i
  have ha : ∀ i, 0 < a i := fun i ↦ Nat.mul_pos hd_pos (ha₀ i)
  have hd_Nco : Int.gcd (d : ℤ) N = 1 :=
    Nat.eq_one_of_dvd_one <| hAco ▸ Nat.dvd_gcd
      (Int.natAbs_dvd_natAbs.mpr ((Int.gcd_dvd_left (d : ℤ) N).trans (hd_dvd 0 0)))
      (Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_right (d : ℤ) N))
  have hgcd_a : Int.gcd (↑(a 0)) ↑N = 1 := by
    change Int.gcd (↑(d * a₀ 0)) ↑N = 1
    simp only [Int.gcd_natCast_natCast]
    exact Nat.Coprime.mul_left
      (by rwa [Int.gcd_natCast_natCast] at hd_Nco)
      (by rwa [Int.gcd_natCast_natCast] at hgcd₀)
  exact ⟨a, ha, hgcd_a, Nat.mul_dvd_mul_left d hdiv₀,
    HeckeCoset.eq_mk_of_mem (content_scaled_doubleCoset_mem N g g₀ γ₁ γ₂ A A₀ d a a₀ hA
      hg₀_val hA₀_eq rfl ha ha₀ hγ₁ hγ₂ hg₀_eq)⟩

/-- **General diagonal representative** for Gamma0 double cosets: every `g ∈ Δ₀(N)` has
`⟦g⟧ = T_diag_Gamma0 N (![d₁, d₂])` for some `d₁ | d₂`, `d₁ > 0`, `d₂ > 0`,
`gcd(d₁, N) = 1`.

Proof: extract content `d`, get primitive quotient `g₀`, clear `gcd(A₀ 0 0, det)` via
`Gamma0_two_sided_coprime_rep_prim`, apply `Gamma0_coset_eq_T_diag_of_coprime` to get
`⟦g₀'⟧ = T_diag_Gamma0 N (![1, m₀])`, then scale back by `d` to get
`⟦g⟧ = T_diag_Gamma0 N (![d, d*m₀])`. -/
lemma Gamma0_exists_diag_rep (N : ℕ) [NeZero N]
    (g : (Gamma0_pair N).Δ) :
    ∃ (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1)
      (_ : a 0 ∣ a 1),
      (⟦g⟧ : HeckeCoset (Gamma0_pair N)) = T_diag_Gamma0 N a ha hgcd := by
  obtain ⟨_, _, A, hA, hAN, hAco⟩ := g.2
  have hA_det_pos : 0 < A.det := by
    rwa [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]
  by_cases hprim : ∀ (p : ℕ), p.Prime →
      ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧ (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1)
  · exact Gamma0_exists_diag_rep_primitive N g A hA hAN hAco hA_det_pos hprim
  · push Not at hprim
    obtain ⟨p, hp, _, _, _, _⟩ := hprim
    set d := Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
              (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) with hd_def
    have hd_dvd : ∀ i j : Fin 2, (d : ℤ) ∣ A i j :=
      content_gcd_dvd_entries A d hd_def
    have hd_pos : 0 < d := content_gcd_pos A d hd_dvd hA_det_pos
    obtain ⟨A₀, hA₀_eq, hA₀_det_pos, hA₀N, hA₀co, _⟩ :=
      Gamma0_content_quotient N A hA_det_pos hAN hAco d hd_pos hd_dvd hd_def
    have hA₀_det_ne : (A₀.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
      rw [det_intMat_cast]
      exact_mod_cast hA₀_det_pos.ne'
    set g₀ : (Gamma0_pair N).Δ := ⟨GeneralLinearGroup.mkOfDetNeZero
      (A₀.map (Int.cast : ℤ → ℚ)) hA₀_det_ne,
      ⟨⟨A₀, rfl⟩, by simp [det_intMat_cast]; exact_mod_cast hA₀_det_pos,
       A₀, rfl, hA₀N, hA₀co⟩⟩
    obtain ⟨a₀, ha₀, hgcd₀, hdiv₀, hrep₀⟩ := Gamma0_exists_diag_rep N g₀
    exact Gamma0_diag_rep_scale_back N g g₀ A A₀ d hA
      (Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _) hA₀_eq hd_pos hd_dvd hAco
      a₀ ha₀ hgcd₀ hdiv₀ hrep₀
  termination_by (g.1.val.det.num.natAbs)
  decreasing_by
    simp only [GeneralLinearGroup.mkOfDetNeZero]
    rw [show (GeneralLinearGroup.mk' (A₀.map (Int.cast : ℤ → ℚ))
          (invertibleOfNonzero hA₀_det_ne)).val.det = (A₀.det : ℚ) by
      simp [det_intMat_cast],
      show g.1.val.det = (A.det : ℚ) by rw [hA, det_intMat_cast],
      show (A₀.det : ℚ).num.natAbs = A₀.det.natAbs by simp [Rat.num_intCast],
      show (A.det : ℚ).num.natAbs = A.det.natAbs by simp [Rat.num_intCast]]
    have hp_dvd_na : ∀ i j : Fin 2, p ∣ (A i j).natAbs := fun i j ↦
      Int.natAbs_natCast p ▸ Int.natAbs_dvd_natAbs.mpr
        (by fin_cases i <;> fin_cases j <;> assumption)
    exact content_quotient_det_natAbs_lt A A₀ d p hp hd_pos
      (Nat.dvd_gcd (Nat.dvd_gcd (hp_dvd_na 0 0) (hp_dvd_na 0 1))
        (Nat.dvd_gcd (hp_dvd_na 1 0) (hp_dvd_na 1 1)))
      hA₀_eq hA₀_det_pos

/-- `cosetMap` preserves diagonal cosets: the GL₂ double coset of `diagMat(a)`
viewed via Gamma0 inclusion equals `T_diag a`. -/
lemma cosetMap_T_diag_Gamma0 (N : ℕ) [NeZero N]
    (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) :
    cosetMap N (T_diag_Gamma0 N a ha hgcd) = T_diag a := by
  show ⟦Delta0_inclusion N ⟨diagMat 2 a, _⟩⟧ = ⟦diagMat_delta 2 a⟧
  congr 1; ext; simp [Delta0_inclusion, diagMat_delta, ha]

/-- `cosetMap` commutes with `mulMap`: the GL coset of the Gamma0 mulMap output
is the GL double coset of the same underlying product element. -/
lemma cosetMap_mulMap_mem_GL_DC (N : ℕ) [NeZero N]
    (g₁ g₂ : (Gamma0_pair N).Δ)
    (p : HeckeRing.decompQuot (Gamma0_pair N) g₁ ×
      HeckeRing.decompQuot (Gamma0_pair N) g₂)
    (D : HeckeCoset (GL_pair 2))
    (h : (p.1.out : GL (Fin 2) ℚ) * g₁ * ((p.2.out : GL (Fin 2) ℚ) * g₂) ∈
      DoubleCoset.doubleCoset (HeckeCoset.rep D : GL (Fin 2) ℚ)
        ((GL_pair 2).H : Set _) ((GL_pair 2).H : Set _)) :
    cosetMap N (HeckeRing.mulMap (Gamma0_pair N) g₁ g₂ p) = D := by
  show ⟦Delta0_inclusion N _⟧ = D
  rw [← HeckeCoset.mk_rep D]
  exact HeckeCoset.eq_mk_of_mem h

/-- GL DC membership for the coprime mulMap product element.
Takes pre-computed GL DC memberships of the reps to avoid expensive elaboration. -/
private lemma product_mem_GL_DC_coprime_aux
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n)
    (σ₁ σ₂ g_m g_n : GL (Fin 2) ℚ)
    (hσ₁ : σ₁ ∈ (SLnZ_subgroup 2 : Set _)) (hσ₂ : σ₂ ∈ (SLnZ_subgroup 2 : Set _))
    (hgm : g_m ∈ DoubleCoset.doubleCoset (diagMat 2 (![1, m]) : GL _ ℚ)
      (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _))
    (hgn : g_n ∈ DoubleCoset.doubleCoset (diagMat 2 (![1, n]) : GL _ ℚ)
      (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _)) :
    σ₁ * g_m * (σ₂ * g_n) ∈ DoubleCoset.doubleCoset (diagMat 2 (![1, m * n]) : GL _ ℚ)
      (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _) := by
  rw [DoubleCoset.mem_doubleCoset] at hgm hgn
  obtain ⟨L₁, ⟨σL₁, rfl⟩, R₁, ⟨σR₁, rfl⟩, hm_eq⟩ := hgm
  obtain ⟨L₂, ⟨σL₂, rfl⟩, R₂, ⟨σR₂, rfl⟩, hn_eq⟩ := hgn
  obtain ⟨σp₁, rfl⟩ := hσ₁
  obtain ⟨σp₂, rfl⟩ := hσ₂
  set τ := σR₁ * σp₂ * σL₂
  have hcore := doubleCoset_mul_coprime_mem 2 ![1, m] ![1, n]
    (fun i ↦ by fin_cases i <;> simp [hm_pos])
    (fun i ↦ by fin_cases i <;> simp [hn_pos])
    (fun i (hi : i + 1 < 2) ↦ by
      have h0 : i = 0 := by lia
      change (![1, m]) ⟨i, _⟩ ∣ _
      subst h0
      simp)
    (fun i (hi : i + 1 < 2) ↦ by
      have h0 : i = 0 := by lia
      change (![1, n]) ⟨i, _⟩ ∣ _
      subst h0
      simp)
    (by simpa [Fin.prod_univ_two] using hcop) τ
  rw [show (![1, m] : Fin 2 → ℕ) * ![1, n] = ![1, m * n] by
    ext i; fin_cases i <;> simp] at hcore
  rw [DoubleCoset.mem_doubleCoset] at hcore ⊢
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hcore_eq⟩ := hcore
  refine ⟨mapGL ℚ (σp₁ * σL₁) * γ₁,
    (SLnZ_subgroup 2).mul_mem (coe_mem_SLnZ 2 _) hγ₁,
    γ₂ * mapGL ℚ σR₂,
    (SLnZ_subgroup 2).mul_mem hγ₂ (coe_mem_SLnZ 2 _), ?_⟩
  rw [hm_eq, hn_eq]
  calc ↑(mapGL ℚ σp₁) * (↑(mapGL ℚ σL₁) * diagMat 2 (![1, m]) * ↑(mapGL ℚ σR₁)) *
        (↑(mapGL ℚ σp₂) * (↑(mapGL ℚ σL₂) * diagMat 2 (![1, n]) * ↑(mapGL ℚ σR₂)))
      = ↑(mapGL ℚ σp₁) * ↑(mapGL ℚ σL₁) *
        (diagMat 2 (![1, m]) * (↑(mapGL ℚ σR₁) * ↑(mapGL ℚ σp₂) * ↑(mapGL ℚ σL₂)) *
          diagMat 2 (![1, n])) * ↑(mapGL ℚ σR₂) := by group
    _ = ↑(mapGL ℚ σp₁) * ↑(mapGL ℚ σL₁) *
        (diagMat 2 (![1, m]) * ↑(mapGL ℚ τ) * diagMat 2 (![1, n])) *
          ↑(mapGL ℚ σR₂) := by simp only [τ, map_mul]
    _ = ↑(mapGL ℚ σp₁) * ↑(mapGL ℚ σL₁) * (γ₁ * diagMat 2 (![1, m * n]) * γ₂) *
          ↑(mapGL ℚ σR₂) := by rw [hcore_eq]
    _ = ↑(mapGL ℚ (σp₁ * σL₁)) * γ₁ * diagMat 2 (![1, m * n]) *
        (γ₂ * ↑(mapGL ℚ σR₂)) := by rw [map_mul]; group

/-- GL DC membership for the coprime mulMap product, specialized to Gamma0 reps. -/
private lemma product_mem_GL_DC_coprime (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n)
    (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N (![1, m])
      (fun i ↦ by fin_cases i <;> simp [hm_pos]) (by simp))) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N (![1, n])
      (fun i ↦ by fin_cases i <;> simp [hn_pos]) (by simp)))) :
    (p.1.out : GL (Fin 2) ℚ) *
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, m])
        (fun i ↦ by fin_cases i <;> simp [hm_pos]) (by simp))).1 *
      ((p.2.out : GL (Fin 2) ℚ) *
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, n])
        (fun i ↦ by fin_cases i <;> simp [hn_pos]) (by simp))).1) ∈
    DoubleCoset.doubleCoset (HeckeCoset.rep (T_diag (![1, m * n])) : GL (Fin 2) ℚ)
      ((GL_pair 2).H : Set _) ((GL_pair 2).H : Set _) := by
  have h_dc_eq : DoubleCoset.doubleCoset
      (HeckeCoset.rep (T_diag (![1, m * n]) : HeckeCoset (GL_pair 2)) : GL _ ℚ)
      ((GL_pair 2).H : Set _) ((GL_pair 2).H : Set _) =
    DoubleCoset.doubleCoset (diagMat 2 (![1, m * n]) : GL _ ℚ)
      ((GL_pair 2).H : Set _) ((GL_pair 2).H : Set _) := by
    have h1 := HeckeCoset.rep_mem (T_diag (![1, m * n]))
    rw [show T_diag (![1, m * n]) = ⟦diagMat_delta 2 (![1, m * n])⟧ from rfl,
      HeckeCoset.toSet_mk,
      diagMat_delta_val 2 _ (fun i ↦ by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])] at h1
    exact DoubleCoset.doubleCoset_eq_of_mem h1
  rw [h_dc_eq]
  apply product_mem_GL_DC_coprime_aux m n hm_pos hn_pos hcop
  · exact Gamma0_le_SLnZ N (SetLike.coe_mem p.1.out)
  · exact Gamma0_le_SLnZ N (SetLike.coe_mem p.2.out)
  · apply Gamma0_doubleCoset_subset_Gamma N
    have h := HeckeCoset.rep_mem (T_diag_Gamma0 N (![1, m])
      (fun i ↦ by fin_cases i <;> simp [hm_pos]) (by simp))
    simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at h ⊢
    exact h
  · apply Gamma0_doubleCoset_subset_Gamma N
    have h := HeckeCoset.rep_mem (T_diag_Gamma0 N (![1, n])
      (fun i ↦ by fin_cases i <;> simp [hn_pos]) (by simp))
    simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at h ⊢
    exact h

/-- Every mulMap output for coprime `diag(1,m) × diag(1,n)` in the Gamma0 Hecke algebra
equals `T_diag_Gamma0 N (![1, m*n])`. Uses the level-1 `doubleCoset_mul_coprime_mem`
to identify the GL coset, then `Gamma0_exists_diag_rep` + `diagonal_representative_unique`
to pin down the Gamma0 coset. -/
lemma mulMap_Gamma0_coprime_eq (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n)
    (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N (![1, m])
      (fun i ↦ by fin_cases i <;> simp [hm_pos]) (by simp))) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N (![1, n])
      (fun i ↦ by fin_cases i <;> simp [hn_pos]) (by simp)))) :
    HeckeRing.mulMap (Gamma0_pair N) _ _ p =
      T_diag_Gamma0 N (![1, m * n])
        (fun i ↦ by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
        (by simp) := by
  set D := HeckeRing.mulMap (Gamma0_pair N) _ _ p
  obtain ⟨a, ha, hgcd_a, hdiv_a, hrep⟩ := Gamma0_exists_diag_rep N (HeckeCoset.rep D)
  have hrep' : D = T_diag_Gamma0 N a ha hgcd_a := hrep ▸ (HeckeCoset.mk_rep D).symm
  have hdiv_mn : DivChain 2 (![1, m * n]) := fun i hi ↦ by
    have h0 : (⟨i, by lia⟩ : Fin 2) = (0 : Fin 2) := Fin.ext (show i = 0 by lia)
    have h1 : (⟨i + 1, hi⟩ : Fin 2) = (1 : Fin 2) := Fin.ext (show i + 1 = 1 by lia)
    change (![1, m * n]) ⟨i, _⟩ ∣ (![1, m * n]) ⟨i + 1, hi⟩
    simp [h0, h1]
  have ha_eq : a = ![1, m * n] := diagonal_representative_unique 2 a ![1, m * n]
    ha (fun i ↦ by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
    (fun i _ ↦ (show i = 0 by lia) ▸ hdiv_a) hdiv_mn (by
      rw [← (show cosetMap N D = T_diag a from by rw [hrep', cosetMap_T_diag_Gamma0]),
        cosetMap_mulMap_mem_GL_DC N _ _ p _
          (product_mem_GL_DC_coprime N m n hm_pos hn_pos hcop p)])
  subst ha_eq
  exact hrep'


end HeckeRing.GLn
