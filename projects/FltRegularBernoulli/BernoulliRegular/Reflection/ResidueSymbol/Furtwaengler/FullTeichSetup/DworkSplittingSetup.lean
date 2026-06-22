module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.FullTeichSetup.TeichmullerSectionConstruction

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-!
## Dwork splitting layer (REF-18c2c4-L2c3d-4a)

The `FullTeichDworkSetup` extends `FullTeichStickelbergerSetup` with
finite-precision Dwork splitting coefficients `λ_{N,n}`.  The target
precision `N` is part of the data because Artin–Hasse coefficients are
naturally local at `Q`: a rational denominator prime to `Q` can be inverted
modulo `Q^(N+1)`, but need not have one globally integral inverse working at
every precision.  The bundle stages three properties of these coefficients as
hypotheses:

1. `λ_{N,n} ∈ Q^n` (so the multi-index expansion lands in `Q^{|m|}` without
   needing a separate `π^{|m|}` factor);
2. for `n ≤ N` and `n < ℓ`, `n! · λ_{N,n} ≡ π^n (mod Q^{n+1})`
   (leading-coefficient identity, used to recover the classical
   `π^s / ∏ a_i!` form);
3. the per-`y` factorization
   `ψ(y) ≡ ∑_{m, |m| ≤ N} (∏_i λ_{N,m_i}) · ω(y)^{M(m)} (mod Q^{N+1})`
   for any truncation `N`, expressing the trace-form additive character
   as a Dwork-style multi-index expansion.

The eventual concrete construction (Artin–Hasse exponential over
`R' = ℚ(ζ_{ℓ(q-1)})`) is deferred; at this layer we only stage the data.
-/

/-- Dwork-splitting refinement of `FullTeichStickelbergerSetup`. Adds
finite-precision Dwork coefficients `dworkCoeff : ℕ → ℕ → 𝓞 R'` together with
the Q-adic / leading-coefficient / factorization hypotheses needed by
the Dwork digit expansion (REF-18c2c4-L2c3d-4b). -/
structure FullTeichDworkSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] extends
    FullTeichStickelbergerSetup ℓ p k K R' where
  /-- Dwork coefficients `λ_{N,n}` of the `N`-precision Artin–Hasse
  splitting function representing the order-`ℓ` additive character. -/
  dworkCoeff : ℕ → ℕ → 𝓞 R'
  /-- `λ_{N,n} ∈ Q^n` for all `N,n`. -/
  dworkCoeff_mem_Q_pow : ∀ (N n : ℕ),
    dworkCoeff N n ∈ toFullTeichStickelbergerSetup.toConcreteStickelbergerSetup.Q ^ n
  /-- Leading-coefficient identity for coefficients that can occur in the
  `N`-th truncation. -/
  dworkCoeff_lt_ell_leading : ∀ (N n : ℕ), n ≤ N → n < ℓ →
    ((Nat.factorial n : ℕ) : 𝓞 R') * dworkCoeff N n -
        toFullTeichStickelbergerSetup.toConcreteStickelbergerSetup.π ^ n ∈
      toFullTeichStickelbergerSetup.toConcreteStickelbergerSetup.Q ^ (n + 1)
  /-- Dwork factorization of the additive character on residue-field
  units. For any `y : kˣ` and any truncation level `N`, the integral
  additive character `ψ((y : k)) = ζ_ℓ^{Tr(c·y).val}` equals the
  multi-index Dwork expansion
  `∑_{m, |m| ≤ N} (∏_i λ_{m_i}) · ω(c·y)^{M(m)}` modulo `Q^{N+1}`,
  where `c = traceScale`.

  This is the per-`y` analog of the classical Dwork splitting identity
  `ζ_ℓ^{Tr(c·y)} = ∏_i Θ(ω(c·y)^{ℓ^i})`, truncated and integrally
  lifted. The `c·y` Teichmüller value is `teichUnitFull (c · y)`.
  Restricted to `kˣ` because `teichUnitFull` is defined only on units. -/
  psi_dwork_factorization : ∀ (N : ℕ) (y : kˣ),
    toFullTeichStickelbergerSetup.toConcreteStickelbergerSetup.psiInt
        ((y : k)) -
      (∑ m ∈ multiIndexLE
          toFullTeichStickelbergerSetup.toConcreteStickelbergerSetup.f N,
        (∏ i : Fin
            toFullTeichStickelbergerSetup.toConcreteStickelbergerSetup.f,
          dworkCoeff N (m i)) *
        ((toFullTeichStickelbergerSetup.teichUnitFull
            (toFullTeichStickelbergerSetup.traceScale * y) : 𝓞 R') ^
          multiIndexValue ℓ m)) ∈
    toFullTeichStickelbergerSetup.toConcreteStickelbergerSetup.Q ^ (N + 1)

namespace FullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : FullTeichDworkSetup ℓ p k K R')

/-- Re-export `dworkCoeff_mem_Q_pow` (L2c3d-4c) at the bundle layer. -/
theorem dworkCoeff_mem_Q_pow_thm (n : ℕ) :
    S.dworkCoeff n n ∈ S.Q ^ n :=
  S.dworkCoeff_mem_Q_pow n n

/-- Re-export `dworkCoeff_mem_Q_pow` with explicit target precision. -/
theorem dworkCoeff_mem_Q_pow_to_thm (N n : ℕ) :
    S.dworkCoeff N n ∈ S.Q ^ n :=
  S.dworkCoeff_mem_Q_pow N n

/-- Re-export `dworkCoeff_lt_ell_leading` (L2c3d-4d) at the bundle layer. -/
theorem dworkCoeff_lt_ell_leading_thm (n : ℕ) (hn : n < ℓ) :
    ((Nat.factorial n : ℕ) : 𝓞 R') * S.dworkCoeff n n - S.π ^ n ∈
      S.Q ^ (n + 1) :=
  S.dworkCoeff_lt_ell_leading n n le_rfl hn

/-- Re-export `dworkCoeff_lt_ell_leading` with explicit target precision. -/
theorem dworkCoeff_lt_ell_leading_to_thm (N n : ℕ) (hnN : n ≤ N) (hn : n < ℓ) :
    ((Nat.factorial n : ℕ) : 𝓞 R') * S.dworkCoeff N n - S.π ^ n ∈
      S.Q ^ (n + 1) :=
  S.dworkCoeff_lt_ell_leading N n hnN hn

end FullTeichDworkSetup

/-! ### Conductor-flexible full-Teich/Dwork API -/

/-- Conductor-flexible full-Teichmüller refinement.

This is the enlarged-conductor replacement for `FullTeichStickelbergerSetup`.
It carries the same explicit Teichmüller section data, but its ambient field
does not have to satisfy the exact pair-cyclotomic typeclass
`[IsCyclotomicExtension {p, ℓ} ℚ R']`. -/
structure ConductorFlexibleFullTeichStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R'] extends
    ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R' where
  /-- Multiplicative section `kˣ →* (𝓞 R')ˣ` of the residue map. -/
  teichUnitFull : kˣ →* (𝓞 R')ˣ
  /-- Residue compatibility: `teichUnitFull` is a section of the residue map. -/
  teichUnitFull_residue :
    ∀ x : kˣ,
      toConductorFlexibleTraceFormStickelbergerSetup.concrete.residueMap
        (teichUnitFull x : 𝓞 R') =
        (x : k)
  /-- The integral residue character is the `d`-th power of the full
  Teichmüller, where `d = (#k - 1) / p`. -/
  residueCharInt_eq_teichUnitFull_pow_d :
    ∀ x : kˣ,
      ConductorFlexibleConcreteStickelbergerSetup.residueCharInt
          toConductorFlexibleTraceFormStickelbergerSetup.concrete (x : k) =
        ((teichUnitFull x : 𝓞 R') ^ ((Fintype.card k - 1) / p) : 𝓞 R')

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

/-- The underlying conductor-flexible concrete setup. -/
def concrete : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' :=
  S.toConductorFlexibleTraceFormStickelbergerSetup.concrete

/-- The underlying integral element of a flexible Teichmüller value. -/
def teichUnitFullVal (x : kˣ) : 𝓞 R' := (S.teichUnitFull x : 𝓞 R')

/-- Multiplicativity of the integral Teichmüller value. -/
@[simp]
theorem teichUnitFullVal_mul (x y : kˣ) :
    S.teichUnitFullVal (x * y) =
      S.teichUnitFullVal x * S.teichUnitFullVal y := by
  unfold teichUnitFullVal
  rw [map_mul]
  rfl

/-- The Teichmüller value at `1` is `1`. -/
@[simp]
theorem teichUnitFullVal_one : S.teichUnitFullVal 1 = 1 := by
  unfold teichUnitFullVal
  rw [map_one]
  rfl

/-- Compatibility of the integral Teichmüller value with powers in `kˣ`. -/
@[simp]
theorem teichUnitFullVal_pow (x : kˣ) (n : ℕ) :
    S.teichUnitFullVal (x ^ n) = S.teichUnitFullVal x ^ n := by
  unfold teichUnitFullVal
  rw [map_pow]
  rfl

/-- The integral Teichmüller value is a unit in `𝓞 R'`, hence not in the prime
ideal `Q`. -/
theorem teichUnitFullVal_not_mem_Q (x : kˣ) :
    S.teichUnitFullVal x ∉ S.Q := by
  intro hmem
  have hunit : IsUnit (S.teichUnitFullVal x) := ⟨S.teichUnitFull x, rfl⟩
  have hQ_prime : S.Q.IsPrime := inferInstance
  exact hQ_prime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)

/-- The Teichmüller residue identity in residue-map form. -/
theorem residueMap_teichUnitFullVal (x : kˣ) :
    S.residueMap (S.teichUnitFullVal x) = (x : k) := by
  change S.concrete.residueMap (S.teichUnitFull x : 𝓞 R') = (x : k)
  exact S.teichUnitFull_residue x

/-- Residue compatibility for Frobenius powers of Teichmüller values. -/
theorem residueMap_teichUnitFullVal_pow (x : kˣ) (n : ℕ) :
    S.residueMap (S.teichUnitFullVal x ^ n) = (x : k) ^ n := by
  rw [map_pow, S.residueMap_teichUnitFullVal]

section TeichOrthogonality

variable [DecidableEq k]

omit [DecidableEq k] in
/-- The integral Teichmüller value has order dividing `#k - 1`. -/
theorem teichUnitFullVal_pow_card_sub_one (x : kˣ) :
    S.teichUnitFullVal x ^ (Fintype.card k - 1) = 1 := by
  haveI : DecidableEq k := Classical.decEq _
  unfold teichUnitFullVal
  rw [show (Fintype.card k - 1) = Fintype.card kˣ from
    (Fintype.card_units (α := k)).symm]
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one]
  rfl

/-- Power sum of Teichmüller lifts over the residue-field unit group. -/
theorem teichUnitFull_sum_pow_units (r : ℕ) :
    (∑ x : kˣ, S.teichUnitFullVal x ^ r) =
      if (Fintype.card k - 1) ∣ r
      then (Fintype.card k - 1 : 𝓞 R')
      else 0 := by
  classical
  rcases Decidable.em ((Fintype.card k - 1) ∣ r) with hdvd | hndvd
  · rw [if_pos hdvd]
    obtain ⟨c, hc⟩ := hdvd
    have h_term : ∀ x : kˣ, S.teichUnitFullVal x ^ r = 1 := by
      intro x
      rw [hc, pow_mul, S.teichUnitFullVal_pow_card_sub_one, one_pow]
    rw [Finset.sum_congr rfl fun x _ => h_term x]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_units]
    rw [nsmul_eq_mul, mul_one]
    have hpos : 1 ≤ Fintype.card k := Fintype.card_pos
    rw [Nat.cast_sub hpos, Nat.cast_one]
  · rw [if_neg hndvd]
    obtain ⟨y, hy⟩ : ∃ y : kˣ, ∀ z : kˣ, z ∈ Subgroup.zpowers y :=
      IsCyclic.exists_generator
    set t := S.teichUnitFullVal y with ht_def
    have h_t_mul_sum :
        t ^ r * (∑ x : kˣ, S.teichUnitFullVal x ^ r) =
          ∑ x : kˣ, S.teichUnitFullVal x ^ r := by
      rw [Finset.mul_sum]
      have h_term_mul : ∀ x : kˣ,
          t ^ r * S.teichUnitFullVal x ^ r =
            S.teichUnitFullVal (y * x) ^ r := by
        intro x
        rw [ht_def, ← mul_pow, ← S.teichUnitFullVal_mul]
      rw [Finset.sum_congr rfl fun x _ => h_term_mul x]
      let e : kˣ ≃ kˣ := Equiv.mulLeft y
      have : (∑ x : kˣ, S.teichUnitFullVal (y * x) ^ r) =
              ∑ x : kˣ, S.teichUnitFullVal (e x) ^ r := rfl
      rw [this]
      exact Finset.sum_equiv e (by simp) (by intros; rfl)
    have h_factor :
        (t ^ r - 1) * (∑ x : kˣ, S.teichUnitFullVal x ^ r) = 0 := by
      rw [sub_mul, one_mul, sub_eq_zero, h_t_mul_sum]
    have h_t_ne : t ^ r ≠ 1 := by
      intro hcontra
      have hres : S.residueMap (t ^ r) = 1 := by
        rw [hcontra]
        exact map_one _
      rw [ht_def, map_pow, S.residueMap_teichUnitFullVal] at hres
      have h_y_unit_pow : ((y : k) ^ r) = 1 := hres
      have h_y_pow_unit : (y : kˣ) ^ r = 1 := by
        ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact h_y_unit_pow
      have h_ord_dvd : orderOf y ∣ r := orderOf_dvd_of_pow_eq_one h_y_pow_unit
      have h_y_gen : orderOf y = Fintype.card kˣ := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hy, Nat.card_eq_fintype_card]
      rw [h_y_gen, Fintype.card_units] at h_ord_dvd
      exact hndvd h_ord_dvd
    have h_t_sub_ne : t ^ r - 1 ≠ 0 := sub_ne_zero.mpr h_t_ne
    rcases mul_eq_zero.mp h_factor with h | h
    · exact absurd h h_t_sub_ne
    · exact h

/-- Inner Teichmüller sum evaluation for conductor-flexible full-Teich setups. -/
theorem teichUnitFull_innerSum_eval (A M : ℕ) (c : kˣ) :
    (∑ x : kˣ,
        S.teichUnitFullVal x ^ A *
          S.teichUnitFullVal (c * x) ^ M) =
      if (Fintype.card k - 1) ∣ (A + M)
      then (Fintype.card k - 1 : 𝓞 R') *
            S.teichUnitFullVal c ^ M
      else 0 := by
  classical
  have h_term : ∀ x : kˣ,
      S.teichUnitFullVal x ^ A * S.teichUnitFullVal (c * x) ^ M =
        S.teichUnitFullVal c ^ M * S.teichUnitFullVal x ^ (A + M) := by
    intro x
    rw [S.teichUnitFullVal_mul, mul_pow, pow_add]
    ring
  rw [Finset.sum_congr rfl fun x _ => h_term x]
  rw [← Finset.mul_sum]
  rw [S.teichUnitFull_sum_pow_units (A + M)]
  by_cases hdvd : (Fintype.card k - 1) ∣ (A + M)
  · rw [if_pos hdvd, if_pos hdvd]
    ring
  · rw [if_neg hdvd, if_neg hdvd]
    ring

end TeichOrthogonality

/-- Raw reciprocal residue-character/Teichmüller power identity. -/
theorem residueCharInt_rec_eq_teichUnitFull_pow
    (a : ℕ) (_ha₁ : 1 ≤ a) (_ha₂ : a ≤ p - 1) (x : kˣ) :
    S.residueCharInt (x : k) ^ (p - a) =
      (S.teichUnitFull x : 𝓞 R') ^ ((p - a) * ((Fintype.card k - 1) / p)) := by
  change
    ConductorFlexibleConcreteStickelbergerSetup.residueCharInt
        (ConductorFlexibleTraceFormStickelbergerSetup.concrete
          S.toConductorFlexibleTraceFormStickelbergerSetup) (x : k) ^
        (p - a) =
      (S.teichUnitFull x : 𝓞 R') ^ ((p - a) * ((Fintype.card k - 1) / p))
  rw [S.residueCharInt_eq_teichUnitFull_pow_d x, ← pow_mul, mul_comm]

end ConductorFlexibleFullTeichStickelbergerSetup

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- The old exact pair-cyclotomic full-Teich setup is a special case of the
conductor-flexible full-Teich API. -/
noncomputable def toConductorFlexible (S : FullTeichStickelbergerSetup ℓ p k K R') :
    ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R' where
  toConductorFlexibleTraceFormStickelbergerSetup :=
    S.toTraceFormStickelbergerSetup.toConductorFlexible
  teichUnitFull := S.teichUnitFull
  teichUnitFull_residue := S.residueMap_teichUnitFullVal
  residueCharInt_eq_teichUnitFull_pow_d := by
    intro x
    exact S.residueCharInt_eq_teichUnitFull_pow_d x

end FullTeichStickelbergerSetup

/-- Conductor-flexible Dwork refinement of the full-Teichmüller setup.  This
is the Dwork payload needed by the enlarged source route, stated without the
old exact pair-cyclotomic typeclass. -/
structure ConductorFlexibleFullTeichDworkSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R'] extends
    ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R' where
  /-- Dwork coefficients `λ_{N,n}`. -/
  dworkCoeff : ℕ → ℕ → 𝓞 R'
  /-- `λ_{N,n} ∈ Q^n` for all `N,n`. -/
  dworkCoeff_mem_Q_pow : ∀ (N n : ℕ),
    dworkCoeff N n ∈
      toConductorFlexibleFullTeichStickelbergerSetup.concrete.Q ^ n
  /-- Leading-coefficient identity for coefficients that can occur in the
  `N`-th truncation. -/
  dworkCoeff_lt_ell_leading : ∀ (N n : ℕ), n ≤ N → n < ℓ →
    ((Nat.factorial n : ℕ) : 𝓞 R') * dworkCoeff N n -
        toConductorFlexibleFullTeichStickelbergerSetup.concrete.π ^ n ∈
      toConductorFlexibleFullTeichStickelbergerSetup.concrete.Q ^ (n + 1)
  /-- Dwork factorization of the additive character on residue-field units. -/
  psi_dwork_factorization : ∀ (N : ℕ) (y : kˣ),
    ConductorFlexibleConcreteStickelbergerSetup.psiInt
        toConductorFlexibleFullTeichStickelbergerSetup.concrete ((y : k)) -
      (∑ m ∈ multiIndexLE
          toConductorFlexibleFullTeichStickelbergerSetup.concrete.f N,
        (∏ i : Fin
            toConductorFlexibleFullTeichStickelbergerSetup.concrete.f,
          dworkCoeff N (m i)) *
        ((toConductorFlexibleFullTeichStickelbergerSetup.teichUnitFull
            (toConductorFlexibleFullTeichStickelbergerSetup.traceScale * y) : 𝓞 R') ^
          multiIndexValue ℓ m)) ∈
    toConductorFlexibleFullTeichStickelbergerSetup.concrete.Q ^ (N + 1)

namespace ConductorFlexibleFullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')

/-- Re-export `dworkCoeff_mem_Q_pow` at the flexible bundle layer. -/
theorem dworkCoeff_mem_Q_pow_thm (N n : ℕ) :
    S.dworkCoeff N n ∈ S.Q ^ n :=
  S.dworkCoeff_mem_Q_pow N n

/-- Re-export `dworkCoeff_mem_Q_pow` with explicit target precision. -/
theorem dworkCoeff_mem_Q_pow_to_thm (N n : ℕ) :
    S.dworkCoeff N n ∈ S.Q ^ n :=
  S.dworkCoeff_mem_Q_pow N n

/-- Re-export `dworkCoeff_lt_ell_leading` with explicit target precision. -/
theorem dworkCoeff_lt_ell_leading_to_thm (N n : ℕ) (hnN : n ≤ N) (hn : n < ℓ) :
    ((Nat.factorial n : ℕ) : 𝓞 R') * S.dworkCoeff N n - S.π ^ n ∈
      S.Q ^ (n + 1) :=
  S.dworkCoeff_lt_ell_leading N n hnN hn

end ConductorFlexibleFullTeichDworkSetup

namespace FullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- The old exact pair-cyclotomic Dwork setup is a special case of the
conductor-flexible Dwork API. -/
noncomputable def toConductorFlexible (S : FullTeichDworkSetup ℓ p k K R') :
    ConductorFlexibleFullTeichDworkSetup ℓ p k K R' where
  toConductorFlexibleFullTeichStickelbergerSetup :=
    S.toFullTeichStickelbergerSetup.toConductorFlexible
  dworkCoeff := S.dworkCoeff
  dworkCoeff_mem_Q_pow := S.dworkCoeff_mem_Q_pow
  dworkCoeff_lt_ell_leading := S.dworkCoeff_lt_ell_leading
  psi_dwork_factorization := S.psi_dwork_factorization

end FullTeichDworkSetup

end Furtwaengler

end BernoulliRegular

end
