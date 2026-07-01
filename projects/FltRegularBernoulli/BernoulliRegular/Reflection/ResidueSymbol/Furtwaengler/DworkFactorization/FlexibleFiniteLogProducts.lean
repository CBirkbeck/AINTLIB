module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteLogAdditivity

/-!
# Product laws for the finite logarithm

This file derives inverse, power, and finite-product laws from the finite-log
additivity theorem for the explicit principal-unit coordinate
`x + y + x*y`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

/-- Coordinate of the principal unit `(1 + x)^n`. -/
def finiteLogPowCoord (n : ℕ) (x : 𝓞 R') : 𝓞 R' :=
  (1 + x) ^ n - 1

omit [NumberField R'] in
theorem finiteLogProductCoord_powCoord (n : ℕ) (x : 𝓞 R') :
    finiteLogProductCoord (finiteLogPowCoord n x) x =
      finiteLogPowCoord (n + 1) x := by
  unfold finiteLogProductCoord finiteLogPowCoord
  rw [pow_succ]
  ring

theorem finiteLogPowCoord_mem_Q {x : 𝓞 R'} (hx : x ∈ F.Q) (n : ℕ) :
    finiteLogPowCoord n x ∈ F.Q := by
  induction n with
  | zero =>
      simp [finiteLogPowCoord]
  | succ n ih =>
      simpa [Nat.succ_eq_add_one, finiteLogProductCoord_powCoord] using
        F.finiteLogProductCoord_mem_Q ih hx

theorem finiteLog_powCoord (N n : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLog N (finiteLogPowCoord n x) (F.finiteLogPowCoord_mem_Q hx n) =
      n • F.finiteLog N x hx := by
  induction n with
  | zero =>
      simp [finiteLogPowCoord, F.finiteLog_arg_zero]
  | succ n ih =>
      have hpow_mem : finiteLogPowCoord n x ∈ F.Q :=
        F.finiteLogPowCoord_mem_Q hx n
      have hprod_mem : finiteLogProductCoord (finiteLogPowCoord n x) x ∈ F.Q :=
        F.finiteLogProductCoord_mem_Q hpow_mem hx
      have hsub :
          finiteLogPowCoord (Nat.succ n) x -
              finiteLogProductCoord (finiteLogPowCoord n x) x ∈ F.Q ^ (N + 1) := by
        rw [Nat.succ_eq_add_one, ← finiteLogProductCoord_powCoord]
        simp
      calc
        F.finiteLog N (finiteLogPowCoord (Nat.succ n) x)
            (F.finiteLogPowCoord_mem_Q hx (Nat.succ n))
            =
          F.finiteLog N (finiteLogProductCoord (finiteLogPowCoord n x) x)
            hprod_mem :=
            F.finiteLog_eq_of_sub_mem _ _ hsub
        _ =
          F.finiteLog N (finiteLogPowCoord n x) hpow_mem +
            F.finiteLog N x hx :=
            F.finiteLog_add_add_mul N hpow_mem hx
        _ = n • F.finiteLog N x hx + F.finiteLog N x hx := by
            rw [ih]
        _ = Nat.succ n • F.finiteLog N x hx := by
            rw [Nat.succ_eq_add_one]
            ring

theorem finiteLog_eq_nsmul_of_sub_powCoord_mem {N n : ℕ}
    {x z : 𝓞 R'} (hx : x ∈ F.Q) (hz : z ∈ F.Q)
    (hzpow : z - finiteLogPowCoord n x ∈ F.Q ^ (N + 1)) :
    F.finiteLog N z hz = n • F.finiteLog N x hx := by
  calc
    F.finiteLog N z hz =
        F.finiteLog N (finiteLogPowCoord n x) (F.finiteLogPowCoord_mem_Q hx n) :=
      F.finiteLog_eq_of_sub_mem hz (F.finiteLogPowCoord_mem_Q hx n) hzpow
    _ = n • F.finiteLog N x hx := F.finiteLog_powCoord N n hx

/-- The `ℓ`-th power of the cyclotomic principal unit `1 + π` has zero
principal-unit coordinate. -/
theorem finiteLogPowCoord_ell_pi_eq_zero :
    finiteLogPowCoord ℓ F.π = 0 := by
  have hzeta : (1 : 𝓞 R') + F.π = F.zeta_ell_int := by
    rw [F.hπ]
    ring
  have hpow : F.zeta_ell_int ^ ℓ = (1 : 𝓞 R') :=
    F.concrete.zeta_ell_int_isPrimitiveRoot.pow_eq_one
  unfold finiteLogPowCoord
  rw [hzeta, hpow]
  ring

/-- `Log_N((1 + π)^ℓ) = Log_N(1) = 0` in finite-log coordinates. -/
theorem finiteLog_powCoord_ell_pi_eq_zero (N : ℕ) :
    F.finiteLog N (finiteLogPowCoord ℓ F.π)
        (F.finiteLogPowCoord_mem_Q F.π_mem_Q ℓ) = 0 :=
  F.finiteLog_eq_zero_of_mem_Q_pow_succ
    (F.finiteLogPowCoord_mem_Q F.π_mem_Q ℓ)
    (by
      rw [F.finiteLogPowCoord_ell_pi_eq_zero]
      simp)

/-- The only torsion consequence needed downstream:
`ℓ • Log_N(1 + π) = 0`. -/
theorem finiteLog_pi_ell_nsmul_eq_zero (N : ℕ) :
    ℓ • F.finiteLog N F.π F.π_mem_Q = 0 := by
  calc
    ℓ • F.finiteLog N F.π F.π_mem_Q =
        F.finiteLog N (finiteLogPowCoord ℓ F.π)
          (F.finiteLogPowCoord_mem_Q F.π_mem_Q ℓ) :=
        (F.finiteLog_powCoord N ℓ F.π_mem_Q).symm
    _ = 0 := F.finiteLog_powCoord_ell_pi_eq_zero N

/-- Multiplicative scalar form of `finiteLog_pi_ell_nsmul_eq_zero`. -/
theorem finiteLog_pi_natCast_ell_mul_eq_zero (N : ℕ) :
    (ℓ : 𝓞 R' ⧸ F.Q ^ (N + 1)) * F.finiteLog N F.π F.π_mem_Q = 0 := by
  simpa [nsmul_eq_mul] using F.finiteLog_pi_ell_nsmul_eq_zero N

/-- Coordinate of the product `∏ i in s, (1 + x i)`. -/
def finiteLogFinsetProductCoord {ι : Type*} (s : Finset ι) (x : ι → 𝓞 R') :
    𝓞 R' :=
  (∏ i ∈ s, (1 + x i)) - 1

omit [NumberField R'] in
theorem finiteLogProductCoord_finsetProductCoord_insert {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι} (ha : a ∉ s) (x : ι → 𝓞 R') :
    finiteLogProductCoord (finiteLogFinsetProductCoord s x) (x a) =
      finiteLogFinsetProductCoord (insert a s) x := by
  simp [finiteLogProductCoord, finiteLogFinsetProductCoord, Finset.prod_insert, ha]
  ring

theorem finiteLogFinsetProductCoord_mem_Q {ι : Type*}
    {s : Finset ι} {x : ι → 𝓞 R'} (hx : ∀ i ∈ s, x i ∈ F.Q) :
    finiteLogFinsetProductCoord s x ∈ F.Q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [finiteLogFinsetProductCoord]
  | insert a s ha ih =>
      have hs : ∀ i ∈ s, x i ∈ F.Q := fun i hi => hx i (Finset.mem_insert_of_mem hi)
      have hcoord : finiteLogFinsetProductCoord s x ∈ F.Q := ih hs
      have haQ : x a ∈ F.Q := hx a (Finset.mem_insert_self a s)
      simpa [finiteLogProductCoord_finsetProductCoord_insert (a := a) ha x] using
        F.finiteLogProductCoord_mem_Q hcoord haQ

theorem finiteLog_finsetProductCoord {ι : Type*} (N : ℕ)
    {s : Finset ι} {x : ι → 𝓞 R'} (hx : ∀ i ∈ s, x i ∈ F.Q) :
    F.finiteLog N (finiteLogFinsetProductCoord s x)
        (F.finiteLogFinsetProductCoord_mem_Q hx) =
      ∑ a ∈ s.attach, F.finiteLog N (x a.1) (hx a.1 a.2) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [finiteLogFinsetProductCoord, F.finiteLog_arg_zero]
  | insert a s ha ih =>
      have hs : ∀ i ∈ s, x i ∈ F.Q := fun i hi => hx i (Finset.mem_insert_of_mem hi)
      have hcoord : finiteLogFinsetProductCoord s x ∈ F.Q :=
        F.finiteLogFinsetProductCoord_mem_Q hs
      have haQ : x a ∈ F.Q := hx a (Finset.mem_insert_self a s)
      have hprod_mem : finiteLogProductCoord (finiteLogFinsetProductCoord s x) (x a) ∈
          F.Q :=
        F.finiteLogProductCoord_mem_Q hcoord haQ
      have hsub :
          finiteLogFinsetProductCoord (insert a s) x -
              finiteLogProductCoord (finiteLogFinsetProductCoord s x) (x a) ∈
            F.Q ^ (N + 1) := by
        rw [← finiteLogProductCoord_finsetProductCoord_insert (a := a) ha x]
        simp
      calc
        F.finiteLog N (finiteLogFinsetProductCoord (insert a s) x)
            (F.finiteLogFinsetProductCoord_mem_Q hx)
            =
          F.finiteLog N (finiteLogProductCoord (finiteLogFinsetProductCoord s x) (x a))
            hprod_mem :=
            F.finiteLog_eq_of_sub_mem _ _ hsub
        _ =
          F.finiteLog N (finiteLogFinsetProductCoord s x) hcoord +
            F.finiteLog N (x a) haQ :=
            F.finiteLog_add_add_mul N hcoord haQ
        _ =
          (∑ i ∈ s.attach, F.finiteLog N (x i.1) (hs i.1 i.2)) +
            F.finiteLog N (x a) haQ := by
            rw [ih hs]
        _ = ∑ i ∈ (insert a s).attach,
            F.finiteLog N (x i.1) (hx i.1 i.2) := by
            symm
            rw [Finset.attach_insert, Finset.sum_insert]
            · rw [Finset.sum_image]
              · simp [add_comm]
              · intro b _hb c _hc hbc
                have hval : b.1 = c.1 :=
                  congrArg (fun z : {i // i ∈ insert a s} => z.1) hbc
                exact Subtype.ext hval
            · simp [ha]

theorem finiteLog_eq_sum_of_sub_finsetProductCoord_mem {ι : Type*}
    {N : ℕ} {s : Finset ι} {x : ι → 𝓞 R'} {z : 𝓞 R'}
    (hx : ∀ i ∈ s, x i ∈ F.Q) (hz : z ∈ F.Q)
    (hzprod : z - finiteLogFinsetProductCoord s x ∈ F.Q ^ (N + 1)) :
    F.finiteLog N z hz =
      ∑ a ∈ s.attach, F.finiteLog N (x a.1) (hx a.1 a.2) := by
  calc
    F.finiteLog N z hz =
        F.finiteLog N (finiteLogFinsetProductCoord s x)
          (F.finiteLogFinsetProductCoord_mem_Q hx) :=
      F.finiteLog_eq_of_sub_mem hz (F.finiteLogFinsetProductCoord_mem_Q hx) hzprod
    _ = ∑ a ∈ s.attach, F.finiteLog N (x a.1) (hx a.1 a.2) :=
      F.finiteLog_finsetProductCoord N hx

theorem finiteLog_add_eq_zero_of_productCoord_mem_Q_pow_succ {N : ℕ}
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q)
    (hxy : finiteLogProductCoord x y ∈ F.Q ^ (N + 1)) :
    F.finiteLog N x hx + F.finiteLog N y hy = 0 := by
  simpa [F.finiteLog_add_add_mul N hx hy] using
    F.finiteLog_eq_zero_of_mem_Q_pow_succ (F.finiteLogProductCoord_mem_Q hx hy) hxy

theorem finiteLog_eq_neg_of_productCoord_mem_Q_pow_succ {N : ℕ}
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q)
    (hxy : finiteLogProductCoord x y ∈ F.Q ^ (N + 1)) :
    F.finiteLog N y hy = -F.finiteLog N x hx := by
  have hsum' : F.finiteLog N y hy + F.finiteLog N x hx = 0 := by
    simpa [add_comm] using
      F.finiteLog_add_eq_zero_of_productCoord_mem_Q_pow_succ hx hy hxy
  exact eq_neg_of_add_eq_zero_left hsum'

theorem finiteLog_add_eq_zero_of_productCoord_eq_zero {N : ℕ}
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q)
    (hxy : finiteLogProductCoord x y = 0) :
    F.finiteLog N x hx + F.finiteLog N y hy = 0 :=
  F.finiteLog_add_eq_zero_of_productCoord_mem_Q_pow_succ hx hy (by simp [hxy])

theorem finiteLog_eq_neg_of_productCoord_eq_zero {N : ℕ}
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q)
    (hxy : finiteLogProductCoord x y = 0) :
    F.finiteLog N y hy = -F.finiteLog N x hx :=
  F.finiteLog_eq_neg_of_productCoord_mem_Q_pow_succ hx hy (by simp [hxy])

end ConductorFlexibleFullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
