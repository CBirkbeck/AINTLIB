import BernoulliRegular.FLT37.Eichler.CaseIIXiReality
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.ProductDescent

/-!
# Washington §9.1 conjugate-norm reassembly algebra (the algebraic heart of FLT37 Case-II)

This file proves, as a **standalone, self-contained pure finite-field-algebra lemma**, Washington's
§9.1 reassembly step (*Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, pp. 179–180): from the
factor equations of the Fermat variables `x, y` at two distinct indices `a, b`, the squared anchor
equation, and **Assumption II** (`η_a/η_b` is a `37`-th power), it produces the **descended Fermat
equation**

  `ω³⁷ + θ³⁷ = δ · λ^{2e-1} · ξ³⁷`,

where `λ = (1-ζ)(1-ζ⁻¹)` is the **real** prime (with `v_𝔭(λ) = 2`), `e` is the anchor exponent, and
`ω, θ, ξ` are the σ-fixed (real) conjugate-norm building blocks
`ω = u²·ρ_a·σρ_a`, `θ = -ρ_b·σρ_b`, `ξ = ρ_0²`.

This is **pure algebra in the field `K`** (no ideal theory, no `p`-adic `L`-functions): it
manipulates field identities under the ring homomorphism `σ = complexConj K`.

## Structure (what is proven here, no `sorry`/`axiom`)

1. **Reality of the building blocks** (general CM field): `complexConj_norm_mul_self`
   (`σ(w·σw) = w·σw`), and the consequent `washington_omega_real`, `washington_theta_real`,
   `washington_xi_real`.

2. **The reassembly** `washington_section91_reassembly` (general CM field): steps 1–4 and 6 of
   Washington's derivation, taking the **crux unit identity** (step 5,
   `λ_a⁻¹ - λ_b⁻¹ = θ'·λ⁻¹` with `θ'` a σ-fixed unit) as a hypothesis on a given `θ' : Kˣ`.  The
   conclusion is the descended equation with `δ = η_0²·θ'·η_b⁻²` a σ-fixed unit, exponent `2e-1`.

3. **The crux unit identity** `washington_section91_crux_unit` (step 5, for
   `K = CyclotomicField 37 ℚ`): `λ_a⁻¹ - λ_b⁻¹ = θ'·λ⁻¹` for a **real unit** `θ'`, proved from the
   repo-proven content lemmas
   `caseII_eta_trace_diff_associated_zeta_sub_one_sq` (`γ_a - γ_b ~ (ζ-1)²` for `a ≢ ±b`) and
   `caseII_K_trace_sub_two_associated` (`λ_a = 2 - γ_a ~ (ζ-1)²`).  This is the "easy calculation"
   on Washington p. 180; the genuine content is `γ_a - γ_b ~ (ζ-1)²`, i.e. that the numerator
   `λ_b - λ_a = γ_a - γ_b` carries exactly the `(ζ-1)²` that cancels one of the four `(ζ-1)` in the
   denominator `λ_a λ_b`, leaving the single net `λ⁻¹`.

4. **The combined core** `washington_section91_descended_equation` (for `K = CyclotomicField 37 ℚ`):
   feeds the proven crux into the reassembly, giving the unconditional descended equation from the
   factor + anchor + Assumption II hypotheses.

## The exact λ-exponent

Derived from the algebra (not assumed): with anchor `(x+y) = η_0·λ^e·ρ_0³⁷`, the descended exponent
is **`2e - 1`**.  Under Washington's `e = m - 18` (so `λ^e` is the `𝔭`-content `λ^{m-18}` of the
anchor, `v_𝔭 = 2(m-18) = 2m-36`), this is `2e-1 = 2m-37`; the `(ζ-1)`-content of `λ^{2e-1}` is
`2·(2e-1) = 2·(2m-37) = 4m-74`, **even** (as it must be: the building blocks are conjugate norms).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1, pp. 179–180.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension NumberField.IsCMField Finset

namespace BernoulliRegular.FLT37.Eichler

open FLT37 BernoulliRegular

/-! ## 1. Reality of the conjugate-norm building blocks (general CM field) -/

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsCMField K]

/-- **The conjugate norm `w·σw` is fixed by complex conjugation** (field level).
`σ(w·σw) = σw·σ(σw) = σw·w = w·σw`, using that `σ = complexConj K` is a ring hom and an involution
(`complexConj_apply_apply`). -/
theorem complexConj_norm_mul_self (w : K) :
    complexConj K (w * complexConj K w) = w * complexConj K w := by
  rw [map_mul, complexConj_apply_apply, mul_comm]

/-- `ω = u²·ρ_a·σρ_a` is **real** (σ-fixed) when `u` is real: it is `u²` (real) times the conjugate
norm `ρ_a·σρ_a` (real, `complexConj_norm_mul_self`). -/
theorem washington_omega_real {u ρa : K} (hu : complexConj K u = u) :
    complexConj K (u ^ 2 * (ρa * complexConj K ρa)) = u ^ 2 * (ρa * complexConj K ρa) := by
  rw [map_mul, map_pow, hu, complexConj_norm_mul_self]

/-- `θ = -ρ_b·σρ_b` is **real** (σ-fixed): the conjugate norm `ρ_b·σρ_b` is real
(`complexConj_norm_mul_self`), and negation commutes with `σ`. -/
theorem washington_section91_theta_real (ρb : K) :
    complexConj K (-(ρb * complexConj K ρb)) = -(ρb * complexConj K ρb) := by
  rw [map_neg, complexConj_norm_mul_self]

/-- `ξ = ρ_0²` is **real** (σ-fixed) when `ρ_0` is real: `σ(ρ_0²) = (σρ_0)² = ρ_0²`. -/
theorem washington_xi_real {ρ0 : K} (hρ0 : complexConj K ρ0 = ρ0) :
    complexConj K (ρ0 ^ 2) = ρ0 ^ 2 := by
  rw [map_pow, hρ0]

/-! ## 2. The reassembly (Washington §9.1 steps 1–4, 6), general CM field

We take the factor equations, the (squared) anchor equation, **Assumption II**, and the crux unit
identity (step 5, `λ_a⁻¹ - λ_b⁻¹ = θ'·λ⁻¹`) as hypotheses, and produce the descended Fermat
equation `ω³⁷ + θ³⁷ = δ·λ^{2e-1}·ξ³⁷` with `δ = η_0²·θ'·η_b⁻²` a σ-fixed unit. -/

/-- **The `xy`-elimination identity** (Washington §9.1 steps 1–3, one index).
From the two `c`-factor equations (`c ∈ {a,b}`) and the squared anchor, subtracting the factor
product from the anchor square eliminates `x²+y²`:
`(x+y)² − (x+ζ^c y)(x+ζ^{-c}y) = (2 − ζ^c − ζ^{-c})·xy = λ_c·xy`.
Solving for `xy` (dividing by the unit `λ_c`) gives
`xy = η_0²λ^{2e}ξ³⁷·λ_c⁻¹ − η_c²·(ρ_cσρ_c)³⁷`, the form used in the index-subtraction step 4. -/
theorem washington_xy_eq
    {x y ρc ρ0 zpc znc : K} {ηc η0 Λc Λ : Kˣ} {e : ℕ}
    (hzc : zpc * znc = 1)
    (hΛc : (Λc : K) = (1 - zpc) * (1 - znc))
    (hfc_pos : x + zpc * y = (1 - zpc) * (ηc : K) * ρc ^ 37)
    (hfc_neg : x + znc * y = (1 - znc) * (ηc : K) * (complexConj K ρc) ^ 37)
    (hanchor : x + y = (η0 : K) * (Λ : K) ^ e * ρ0 ^ 37) :
    x * y =
      (η0 : K) ^ 2 * (Λ : K) ^ (2 * e) * (ρ0 ^ 2) ^ 37 * ((Λc : K)⁻¹) -
        (ηc : K) ^ 2 * (ρc * complexConj K ρc) ^ 37 := by
  -- `λ_c·xy = (x+y)² − (x+ζ^c y)(x+ζ^{-c}y)` = anchor² − product (step 3).
  have hΛc_ne : (Λc : K) ≠ 0 := Λc.ne_zero
  -- Product side `= λ_c·η_c²·(ρ_cσρ_c)³⁷`; anchor square side `= η_0²λ^{2e}ξ³⁷`.
  have key : (Λc : K) * (x * y) =
      (η0 : K) ^ 2 * (Λ : K) ^ (2 * e) * (ρ0 ^ 2) ^ 37 -
        (Λc : K) * ((ηc : K) ^ 2 * (ρc * complexConj K ρc) ^ 37) := by
    have hPc : (x + zpc * y) * (x + znc * y) =
        (Λc : K) * ((ηc : K) ^ 2 * (ρc * complexConj K ρc) ^ 37) := by
      rw [hfc_pos, hfc_neg, hΛc]; ring
    have hS : (x + y) ^ 2 = (η0 : K) ^ 2 * (Λ : K) ^ (2 * e) * (ρ0 ^ 2) ^ 37 := by
      rw [hanchor]; ring
    -- anchor² − product = (2 − ζ^c − ζ^{-c})·xy = λ_c·xy  (uses `ζ^c·ζ^{-c} = 1`).
    have hsub : (x + y) ^ 2 - (x + zpc * y) * (x + znc * y) = (Λc : K) * (x * y) := by
      rw [hΛc]; linear_combination -(x * y + y ^ 2) * hzc
    rw [← hsub, hPc, hS]
  -- Divide by the unit `λ_c`.
  field_simp at key ⊢
  linear_combination key

/-- **Washington §9.1 conjugate-norm reassembly** (steps 1–4, 6; general CM field).

From the four factor equations (indices `a, b`), the anchor equation `x+y = η_0·λ^e·ρ_0³⁷`,
**Assumption II** `η_a = u³⁷·η_b`, and the **crux unit identity** (step 5)
`λ_a⁻¹ − λ_b⁻¹ = θ'·λ⁻¹`, the descended Fermat equation holds:
```
ω³⁷ + θ³⁷ = δ · λ^{2e-1} · ξ³⁷,
```
where `ω = u²·ρ_aσρ_a`, `θ = -ρ_bσρ_b`, `ξ = ρ_0²` are the conjugate-norm building blocks, and
`δ = η_0²·θ'·η_b⁻²` (a unit).  The `37`-odd parity `(-w)³⁷ = -w³⁷` turns `−(ρ_bσρ_b)³⁷` into `θ³⁷`.

Derivation (Washington pp. 179–180):
* steps 1–3: `washington_xy_eq` at `a` and `b` solves `xy` two ways;
* step 4: equate the two, getting `η_a²N_a³⁷ − η_b²N_b³⁷ = S·(λ_a⁻¹ − λ_b⁻¹)`,
  `S = η_0²λ^{2e}ξ³⁷`;
* step 5 (`hcrux`): `λ_a⁻¹ − λ_b⁻¹ = θ'·λ⁻¹`, so the RHS is `η_0²θ'·λ^{2e-1}·ξ³⁷`;
* step 6: divide by `η_b²`, use Assumption II `η_a²/η_b² = (u²)³⁷`, and `(-N_b)³⁷ = -N_b³⁷`
  (37 odd).

The exact descended exponent is `2e-1` (requires `e ≥ 1`); its `(ζ-1)`-content (with `v_𝔭(λ)=2`) is
`2(2e-1)`, **even**. -/
theorem washington_section91_reassembly
    {x y ρa ρb ρ0 zpa zna zpb znb : K} {ηa ηb η0 u θ' Λa Λb Λ : Kˣ} {e : ℕ}
    (he : 1 ≤ e)
    (hza : zpa * zna = 1) (hzb : zpb * znb = 1)
    (hΛa : (Λa : K) = (1 - zpa) * (1 - zna))
    (hΛb : (Λb : K) = (1 - zpb) * (1 - znb))
    (hfa_pos : x + zpa * y = (1 - zpa) * (ηa : K) * ρa ^ 37)
    (hfa_neg : x + zna * y = (1 - zna) * (ηa : K) * (complexConj K ρa) ^ 37)
    (hfb_pos : x + zpb * y = (1 - zpb) * (ηb : K) * ρb ^ 37)
    (hfb_neg : x + znb * y = (1 - znb) * (ηb : K) * (complexConj K ρb) ^ 37)
    (hanchor : x + y = (η0 : K) * (Λ : K) ^ e * ρ0 ^ 37)
    (hII : (ηa : Kˣ) = u ^ 37 * ηb)
    (hcrux : (Λa : K)⁻¹ - (Λb : K)⁻¹ = (θ' : K) * (Λ : K)⁻¹) :
    ((u : K) ^ 2 * (ρa * complexConj K ρa)) ^ 37 +
        (-(ρb * complexConj K ρb)) ^ 37 =
      (η0 ^ 2 * θ' * ηb⁻¹ ^ 2 : Kˣ) * (Λ : K) ^ (2 * e - 1) * (ρ0 ^ 2) ^ 37 := by
  -- `xy` solved two ways (steps 1–3).
  have hxyA := washington_xy_eq hza hΛa hfa_pos hfa_neg hanchor
  have hxyB := washington_xy_eq hzb hΛb hfb_pos hfb_neg hanchor
  -- Step 4: equate, obtaining `η_a²N_a³⁷ − η_b²N_b³⁷ = S·(λ_a⁻¹ − λ_b⁻¹)`.
  set S : K := (η0 : K) ^ 2 * (Λ : K) ^ (2 * e) * (ρ0 ^ 2) ^ 37 with hS_def
  have hstep4 : (ηa : K) ^ 2 * (ρa * complexConj K ρa) ^ 37 -
      (ηb : K) ^ 2 * (ρb * complexConj K ρb) ^ 37 = S * ((Λa : K)⁻¹ - (Λb : K)⁻¹) := by
    have h := hxyA.symm.trans hxyB
    -- `S·Λa⁻¹ − N_a = S·Λb⁻¹ − N_b`  ⟹  `N_a' − N_b' = S(Λa⁻¹ − Λb⁻¹)`.
    linear_combination -h
  -- Step 5: substitute the crux, then `λ^{2e}·λ⁻¹ = λ^{2e-1}`.
  rw [hcrux] at hstep4
  have hΛpow : (Λ : K) ^ (2 * e) * (Λ : K)⁻¹ = (Λ : K) ^ (2 * e - 1) := by
    have hpow : (Λ : K) ^ (2 * e) = (Λ : K) ^ (2 * e - 1) * (Λ : K) := by
      conv_lhs => rw [show 2 * e = (2 * e - 1) + 1 from by omega]
      rw [pow_succ]
    rw [hpow, mul_assoc, mul_inv_cancel₀ Λ.ne_zero, mul_one]
  -- Now `N_a' − N_b' = S·θ'·λ⁻¹ = η_0²·θ'·λ^{2e-1}·ξ³⁷`.
  have hstep5 : (ηa : K) ^ 2 * (ρa * complexConj K ρa) ^ 37 -
      (ηb : K) ^ 2 * (ρb * complexConj K ρb) ^ 37 =
      (η0 : K) ^ 2 * (θ' : K) * (Λ : K) ^ (2 * e - 1) * (ρ0 ^ 2) ^ 37 := by
    rw [hstep4, hS_def]
    rw [show (η0 : K) ^ 2 * (Λ : K) ^ (2 * e) * (ρ0 ^ 2) ^ 37 * ((θ' : K) * (Λ : K)⁻¹) =
      (η0 : K) ^ 2 * (θ' : K) * ((Λ : K) ^ (2 * e) * (Λ : K)⁻¹) * (ρ0 ^ 2) ^ 37 from by ring,
      hΛpow]
  -- Step 6: divide by `η_b²` (use Assumption II `η_a² = (u²)³⁷·η_b²`) and `(-N_b)³⁷ = -N_b³⁷`.
  have hηa_sq : (ηa : K) ^ 2 = ((u : K) ^ 2) ^ 37 * (ηb : K) ^ 2 := by
    have hII' : (ηa : K) = (u : K) ^ 37 * (ηb : K) := by
      rw [show (ηa : K) = ((ηa : Kˣ) : K) from rfl, hII]; push_cast; ring
    rw [hII']; ring
  -- `δ = η_0²·θ'·η_b⁻²` as a unit; its coercion is `η_0²·θ'·η_b⁻²` in `K`.
  have hδ_coe : ((η0 ^ 2 * θ' * ηb⁻¹ ^ 2 : Kˣ) : K) =
      (η0 : K) ^ 2 * (θ' : K) * ((ηb : K) ^ 2)⁻¹ := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow]
  rw [hδ_coe]
  -- Multiply `hstep5` through; substitute `η_a²` and rearrange into the conjugate-norm powers.
  have hηb_ne : (ηb : K) ^ 2 ≠ 0 := pow_ne_zero 2 ηb.ne_zero
  rw [hηa_sq] at hstep5
  -- `(u²)³⁷·N_a³⁷ − η_b²·N_b³⁷ = η_0²θ'λ^{2e-1}ξ³⁷`; divide by `η_b²`.
  -- Target: `(u²·N_a)³⁷ + (-N_b)³⁷ = η_0²θ'(η_b²)⁻¹·λ^{2e-1}ξ³⁷`.
  have key : ((u : K) ^ 2) ^ 37 * (ρa * complexConj K ρa) ^ 37 -
      (ρb * complexConj K ρb) ^ 37 =
      (η0 : K) ^ 2 * (θ' : K) * ((ηb : K) ^ 2)⁻¹ * (Λ : K) ^ (2 * e - 1) * (ρ0 ^ 2) ^ 37 := by
    field_simp
    field_simp at hstep5
    linear_combination hstep5
  -- `(u²·N_a)³⁷ = (u²)³⁷·N_a³⁷` and `(-N_b)³⁷ = -N_b³⁷`.
  rw [mul_pow, Odd.neg_pow (by decide : Odd 37)]
  linear_combination key

/-! ## 3. The crux unit identity (Washington §9.1 step 5)

The "easy calculation" `λ_a⁻¹ − λ_b⁻¹ = θ'·λ⁻¹` with `θ'` a unit.  We first record the **pure
field-algebra core**: if `LA, LB, L` and `LB − LA` all carry exactly the same content `p` (here
`p = (ζ-1)²`) — i.e. each is `p` times a unit — then the difference of inverses is a *unit* times
`L⁻¹`, with the explicit unit `u_A·u_B·u_D⁻¹·u_L⁻¹`. -/

/-- **The unit-quotient core of Washington step 5** (pure field algebra).
Given nonzero `p` and unit cofactors `uA uB uL uD : Kˣ` with `LA·uA = p`, `LB·uB = p`, `L·uL = p`,
`(LB − LA)·uD = p`, the difference of inverses factors as a unit times `L⁻¹`:
```
LA⁻¹ − LB⁻¹ = (uA·uB·uD⁻¹·uL⁻¹) · L⁻¹.
```
(Substituting `LA = p·uA⁻¹` etc., the four `p`'s cancel: `(LB-LA)/(LA·LB)·L = uA u_B u_D⁻¹ u_L⁻¹`.)
This is the algebraic heart of step 5; the genuine arithmetic content — that `LB − LA` carries the
*same* `(ζ-1)²` as `LA, LB, L` — is the `caseII_eta_trace_diff_associated_zeta_sub_one_sq` input
supplied below. -/
theorem washington_unit_quotient_core {LA LB L p : K} {uA uB uL uD : Kˣ}
    (hp : p ≠ 0)
    (hLA : LA * (uA : K) = p) (hLB : LB * (uB : K) = p)
    (hL : L * (uL : K) = p) (hD : (LB - LA) * (uD : K) = p) :
    LA⁻¹ - LB⁻¹ = ((uA * uB * uD⁻¹ * uL⁻¹ : Kˣ) : K) * L⁻¹ := by
  -- Each of `LA, LB, L` is nonzero (it is `p ≠ 0` divided by a unit).
  have hLA_ne : LA ≠ 0 := by
    rintro rfl; rw [zero_mul] at hLA; exact hp hLA.symm
  have hLB_ne : LB ≠ 0 := by
    rintro rfl; rw [zero_mul] at hLB; exact hp hLB.symm
  have hL_ne : L ≠ 0 := by
    rintro rfl; rw [zero_mul] at hL; exact hp hL.symm
  -- `LA⁻¹ = uA·p⁻¹`, `LB⁻¹ = uB·p⁻¹`, `L⁻¹ = uL·p⁻¹`, `(LB − LA) = p·uD⁻¹`.
  have eLA : LA⁻¹ = (uA : K) * p⁻¹ := by
    rw [eq_comm, ← hLA]; field_simp
  have eLB : LB⁻¹ = (uB : K) * p⁻¹ := by
    rw [eq_comm, ← hLB]; field_simp
  have eL : L⁻¹ = (uL : K) * p⁻¹ := by
    rw [eq_comm, ← hL]; field_simp
  -- The difference `LB − LA = (uA − uB)·p⁻¹·LA·LB`... instead use it directly via `hD`.
  -- We compute the RHS and match.  Coerce the witness unit.
  have hcoe : ((uA * uB * uD⁻¹ * uL⁻¹ : Kˣ) : K) =
      (uA : K) * (uB : K) * (uD : K)⁻¹ * (uL : K)⁻¹ := by
    push_cast; ring
  rw [hcoe, eLA, eLB, eL]
  -- Goal: `uA·p⁻¹ − uB·p⁻¹ = (uA uB uD⁻¹ uL⁻¹)·(uL·p⁻¹)`.
  -- Use `(LB − LA)·uD = p`, i.e. `(uB − uA)·p⁻¹ = uD⁻¹` after substituting `LB,LA`.
  -- From `eLA, eLB`: `LA = p·uA⁻¹`, `LB = p·uB⁻¹`, so `LB − LA = p·(uB⁻¹ − uA⁻¹)`.
  have hLAval : LA = p * (uA : K)⁻¹ := by
    rw [eq_comm, ← hLA]; field_simp
  have hLBval : LB = p * (uB : K)⁻¹ := by
    rw [eq_comm, ← hLB]; field_simp
  -- Substitute into `hD`: `p·(uB⁻¹ − uA⁻¹)·uD = p`, divide by `p`: `(uB⁻¹ − uA⁻¹)·uD = 1`.
  rw [hLBval, hLAval] at hD
  have hkey : ((uB : K)⁻¹ - (uA : K)⁻¹) * (uD : K) = 1 := by
    have hpD : p * (((uB : K)⁻¹ - (uA : K)⁻¹) * (uD : K)) = p * 1 := by
      rw [mul_one]; linear_combination hD
    exact mul_left_cancel₀ hp hpD
  -- Now `uL·(uL⁻¹) = 1` and `(uB⁻¹ − uA⁻¹)·uD = 1` close the goal by field algebra.
  have huA : (uA : K) ≠ 0 := uA.ne_zero
  have huB : (uB : K) ≠ 0 := uB.ne_zero
  have huD : (uD : K) ≠ 0 := uD.ne_zero
  have huL : (uL : K) ≠ 0 := uL.ne_zero
  field_simp
  field_simp at hkey
  linear_combination hkey

section Crux

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-- Abbreviation for the integer real prime factor `L_η = (1-η)(1-η^36) = 2 − (η + η^36)`. -/
local notation "𝓛(" η ")" => (1 - η) * (1 - η ^ 36)

/-- **`L_η = (1-η)(1-η^36)` is real** (σ-fixed) for a `37`-th root `η`.
`L_η = 2 − (η + η^36)`, and `σ(η + η^36) = η + η^36` (`caseII_eta_plus_etaInv_fixed`). -/
theorem washington_L_real {η : 𝓞 K} (hη : η ^ 37 = 1) :
    ringOfIntegersComplexConj K ((1 - η) * (1 - η ^ 36)) = (1 - η) * (1 - η ^ 36) := by
  -- `σ((1-η)(1-η^36)) = (1-η^36)(1-(η^36)^36) = (1-η^36)(1-η)` (since `(η^36)^36 = η`).
  have hpow : (η ^ 36) ^ 36 = η := by
    rw [← pow_mul, show 36 * 36 = 37 * 35 + 1 from by norm_num, pow_add, pow_mul, hη]; ring
  rw [map_mul, map_sub, map_one, map_sub, map_one, map_pow,
    caseII_ringOfIntegersComplexConj_root_of_unity hη, hpow]
  ring

/-- **`L_η = (1-η)(1-η^36) = γ_1 − γ_η` Associated `(ζ-1)²`** for a `37`-th root `η ≠ 1`.
`L_η = (1 + 1^36) − (η + η^36)`, so this is `caseII_eta_trace_diff_associated_zeta_sub_one_sq`
applied with `η₁ = 1`, `η₂ = η` (conditions `1 ≠ η` and `1·η ≠ 1`, both `η ≠ 1`). -/
theorem washington_L_associated {η : 𝓞 K} (hη : η ^ 37 = 1) (hη1 : η ≠ 1) :
    Associated ((1 - η) * (1 - η ^ 36)) (((zeta_spec 37 ℚ K).toInteger - 1) ^ 2) := by
  have hExpand : (1 - η) * (1 - η ^ 36) =
      ((1 : 𝓞 K) + (1 : 𝓞 K) ^ 36) - (η + η ^ 36) := by
    have : η * η ^ 36 = 1 := by rw [mul_comm, ← pow_succ]; exact hη
    linear_combination this
  rw [hExpand]
  exact caseII_eta_trace_diff_associated_zeta_sub_one_sq (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot
    (one_pow 37) hη (fun h ↦ hη1 h.symm) (by simpa using hη1)

/-- **Washington §9.1 step 5 — the crux unit identity** (for `K` cyclotomic of conductor `37`).

For two `37`-th roots `ηA, ηB` with `ηA, ηB ≠ 1`, `ηA ≠ ηB`, and `ηA·ηB ≠ 1` (i.e. `a ≢ ±b`), the
difference of inverses of the real factors `L_{ηA}, L_{ηB}` is a **real unit** times `L_ζ⁻¹`:
```
(L_{ηA})⁻¹ − (L_{ηB})⁻¹ = θ' · (L_ζ)⁻¹,    θ' : (𝓞 K)ˣ real,
```
where `L_η = (1-η)(1-η^36)` and `ζ = (zeta_spec 37 ℚ K).toInteger`.

This is the "easy calculation" on Washington p. 180.  The genuine content is that the **numerator**
`L_{ηB} − L_{ηA} = γ_{ηA} − γ_{ηB}` carries exactly the `(ζ-1)²` (`washington_L_associated` and
`caseII_eta_trace_diff_associated_zeta_sub_one_sq`) that cancels one of the four `(ζ-1)` in the
denominator `L_{ηA}·L_{ηB}`, leaving the single net `L_ζ⁻¹`.  Reality of `θ'` follows from
reality of `L_{ηA}, L_{ηB}, L_ζ` (`washington_L_real`), since `θ' = (L_{ηA}⁻¹ − L_{ηB}⁻¹)·L_ζ`
as a field element. -/
theorem washington_section91_crux_unit
    {ηA ηB : 𝓞 K} (hA : ηA ^ 37 = 1) (hB : ηB ^ 37 = 1)
    (hA1 : ηA ≠ 1) (hB1 : ηB ≠ 1) (hAB : ηA ≠ ηB) (hABp : ηA * ηB ≠ 1) :
    ∃ θ' : (𝓞 K)ˣ, ringOfIntegersComplexConj K θ' = θ' ∧
      (algebraMap (𝓞 K) K ((1 - ηA) * (1 - ηA ^ 36)))⁻¹ -
          (algebraMap (𝓞 K) K ((1 - ηB) * (1 - ηB ^ 36)))⁻¹ =
        (algebraMap (𝓞 K) K (θ' : 𝓞 K)) *
          (algebraMap (𝓞 K) K
            ((1 - (zeta_spec 37 ℚ K).toInteger) * (1 - (zeta_spec 37 ℚ K).toInteger ^ 36)))⁻¹ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set ζ : 𝓞 K := (zeta_spec 37 ℚ K).toInteger with hζ_def
  have hζpow : ζ ^ 37 = 1 := (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
  have hζ1 : ζ ≠ 1 := (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
  -- The four `Associated _ (ζ-1)²` facts (integer level).
  obtain ⟨uA, hAeq⟩ := washington_L_associated hA hA1
  obtain ⟨uB, hBeq⟩ := washington_L_associated hB hB1
  obtain ⟨uL, hLeq⟩ := washington_L_associated hζpow hζ1
  -- `L_{ηB} − L_{ηA} = γ_{ηA} − γ_{ηB} ~ (ζ-1)²`.
  obtain ⟨uD, hDeq⟩ :=
    caseII_eta_trace_diff_associated_zeta_sub_one_sq (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot hA hB hAB hABp
  -- Rewrite `γ_{ηA} − γ_{ηB} = L_{ηB} − L_{ηA}` (both equal `(2−γ_{ηA})−(2−γ_{ηB})`... = swap).
  have hLBA : (ηA + ηA ^ 36) - (ηB + ηB ^ 36) =
      (1 - ηB) * (1 - ηB ^ 36) - (1 - ηA) * (1 - ηA ^ 36) := by
    have ea : ηA * ηA ^ 36 = 1 := by rw [mul_comm, ← pow_succ]; exact hA
    have eb : ηB * ηB ^ 36 = 1 := by rw [mul_comm, ← pow_succ]; exact hB
    linear_combination ea - eb
  rw [hLBA] at hDeq
  -- Abbreviations for the field images of `L_{ηA}, L_{ηB}, L_ζ` and the content `(ζ-1)²`.
  set LA : K := algebraMap (𝓞 K) K ((1 - ηA) * (1 - ηA ^ 36)) with hLA_def
  set LB : K := algebraMap (𝓞 K) K ((1 - ηB) * (1 - ηB ^ 36)) with hLB_def
  set Lζ : K := algebraMap (𝓞 K) K ((1 - ζ) * (1 - ζ ^ 36)) with hLζ_def
  set p : K := algebraMap (𝓞 K) K (((zeta_spec 37 ℚ K).toInteger - 1) ^ 2) with hp_def
  -- The integer unit `θ'_int := uA·uB·uD⁻¹·uL⁻¹`, and its field-unit image.
  set θ'_int : (𝓞 K)ˣ := uA * uB * uD⁻¹ * uL⁻¹ with hθ'_def
  have hpne : p ≠ 0 := by
    rw [hp_def, Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    exact pow_ne_zero 2 ((zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide : 1 < 37))
  -- `washington_unit_quotient_core` with field witnesses `Units.map _ u…`.  Each content equation
  -- is the `algebraMap`-image of the corresponding `𝓞 K`-level `Associated` equation.
  have hCore := washington_unit_quotient_core (LA := LA) (LB := LB) (L := Lζ) (p := p)
    (uA := Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uA)
    (uB := Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uB)
    (uL := Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uL)
    (uD := Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uD)
    hpne
    (by rw [hLA_def, hp_def, Units.coe_map, MonoidHom.coe_coe, ← map_mul, hAeq])
    (by rw [hLB_def, hp_def, Units.coe_map, MonoidHom.coe_coe, ← map_mul, hBeq])
    (by rw [hLζ_def, hp_def, Units.coe_map, MonoidHom.coe_coe, ← map_mul, hLeq])
    (by rw [hLA_def, hLB_def, hp_def, Units.coe_map, MonoidHom.coe_coe, ← map_sub, ← map_mul, hDeq])
  -- The field unit `↑(Units.map _ (θ'_int))` equals `algebraMap (↑θ'_int)`.
  have hθ'coe : ((Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uA *
      Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uB *
      (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uD)⁻¹ *
      (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uL)⁻¹ : Kˣ) : K) =
      algebraMap (𝓞 K) K (θ'_int : 𝓞 K) := by
    have : (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uA *
        Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uB *
        (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uD)⁻¹ *
        (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) uL)⁻¹ : Kˣ) =
        Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) θ'_int := by
      rw [hθ'_def]; simp only [map_mul, map_inv]
    rw [this, Units.coe_map, MonoidHom.coe_coe]
  rw [hθ'coe] at hCore
  -- The crux identity (matches the goal).
  refine ⟨θ'_int, ?_, hCore⟩
  -- Reality of `θ'_int`: `algebraMap θ'_int = (LA⁻¹ − LB⁻¹)·Lζ` is σ-fixed (LA, LB, Lζ all real).
  have hLζne : Lζ ≠ 0 := by
    intro h
    apply hpne
    rw [hp_def, ← hLeq, map_mul, ← hLζ_def, h, zero_mul]
  -- `algebraMap θ'_int = (LA⁻¹ − LB⁻¹)·Lζ`.
  have hθ'val : algebraMap (𝓞 K) K (θ'_int : 𝓞 K) = (LA⁻¹ - LB⁻¹) * Lζ := by
    rw [hCore]; field_simp
  -- `LA, LB, Lζ` are σ-fixed (`washington_L_real` + `coe_ringOfIntegersComplexConj`).
  have hLAreal : complexConj K LA = LA := by
    rw [hLA_def, ← coe_ringOfIntegersComplexConj, washington_L_real hA]
  have hLBreal : complexConj K LB = LB := by
    rw [hLB_def, ← coe_ringOfIntegersComplexConj, washington_L_real hB]
  have hLζreal : complexConj K Lζ = Lζ := by
    rw [hLζ_def, ← coe_ringOfIntegersComplexConj, washington_L_real hζpow]
  -- Hence the field image is σ-fixed; transport to the integer unit.
  have hreal_field : complexConj K (algebraMap (𝓞 K) K (θ'_int : 𝓞 K)) =
      algebraMap (𝓞 K) K (θ'_int : 𝓞 K) := by
    rw [hθ'val, map_mul, map_sub, map_inv₀, map_inv₀, hLAreal, hLBreal, hLζreal]
  -- `complexConj ∘ algebraMap = algebraMap ∘ ringOfIntegersComplexConj`, then inject.
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [← coe_ringOfIntegersComplexConj] at hreal_field
  exact hreal_field

/-! ## 4. The combined descended equation (crux fed into the reassembly)

We compose `washington_section91_crux_unit` (step 5) with `washington_section91_reassembly`
(steps 1–4, 6): from the factor + anchor + Assumption II data alone — with the root powers being the
field images of integer `37`-th roots `ηA = ζ^a`, `ηB = ζ^b` — the descended Fermat equation holds,
with **no** crux hypothesis (it is now discharged) and a σ-fixed unit `δ`. -/

/-- **Washington §9.1 descended Fermat equation** (crux discharged; `K` cyclotomic conductor `37`).

Let `ηA, ηB : 𝓞 K` be two `37`-th roots with `ηA, ηB ≠ 1`, `ηA ≠ ηB`, `ηA·ηB ≠ 1` (i.e. `a ≢ ±b`),
and let the factor-equation root powers be their field images (`zpa = ηA`, `zna = ηA^36`, etc.).
Given the four factor equations, the anchor `x+y = η_0·λ^e·ρ_0³⁷`, and Assumption II
`η_a = u³⁷·η_b`, the descended Fermat equation
```
ω³⁷ + θ³⁷ = δ · λ^{2e-1} · ξ³⁷,    ω = u²ρ_aσρ_a, θ = -ρ_bσρ_b, ξ = ρ_0²,
```
holds for a **σ-fixed** unit `δ : Kˣ` (the descended content `λ^{2e-1}`, `(ζ-1)`-content `2(2e-1)`,
even).  The crux unit identity (step 5) is supplied internally by `washington_section91_crux_unit`,
so this is unconditional given the factor/anchor/Assumption-II data. -/
theorem washington_section91_descended_equation
    {x y ρa ρb ρ0 : K} {ηa ηb η0 u : Kˣ} {ηA ηB : 𝓞 K}
    {Λa Λb Λ : Kˣ} {e : ℕ}
    (he : 1 ≤ e)
    (hA : ηA ^ 37 = 1) (hB : ηB ^ 37 = 1)
    (hA1 : ηA ≠ 1) (hB1 : ηB ≠ 1) (hAB : ηA ≠ ηB) (hABp : ηA * ηB ≠ 1)
    (hΛa : (Λa : K) = algebraMap (𝓞 K) K ((1 - ηA) * (1 - ηA ^ 36)))
    (hΛb : (Λb : K) = algebraMap (𝓞 K) K ((1 - ηB) * (1 - ηB ^ 36)))
    (hΛ : (Λ : K) = algebraMap (𝓞 K) K
      ((1 - (zeta_spec 37 ℚ K).toInteger) * (1 - (zeta_spec 37 ℚ K).toInteger ^ 36)))
    (hfa_pos : x + algebraMap (𝓞 K) K ηA * y =
      (1 - algebraMap (𝓞 K) K ηA) * (ηa : K) * ρa ^ 37)
    (hfa_neg : x + algebraMap (𝓞 K) K (ηA ^ 36) * y =
      (1 - algebraMap (𝓞 K) K (ηA ^ 36)) * (ηa : K) * (complexConj K ρa) ^ 37)
    (hfb_pos : x + algebraMap (𝓞 K) K ηB * y =
      (1 - algebraMap (𝓞 K) K ηB) * (ηb : K) * ρb ^ 37)
    (hfb_neg : x + algebraMap (𝓞 K) K (ηB ^ 36) * y =
      (1 - algebraMap (𝓞 K) K (ηB ^ 36)) * (ηb : K) * (complexConj K ρb) ^ 37)
    (hanchor : x + y = (η0 : K) * (Λ : K) ^ e * ρ0 ^ 37)
    (hII : (ηa : Kˣ) = u ^ 37 * ηb)
    (hη0real : complexConj K (η0 : K) = (η0 : K))
    (hηbreal : complexConj K (ηb : K) = (ηb : K)) :
    ∃ δ : Kˣ, complexConj K (δ : K) = (δ : K) ∧
      ((u : K) ^ 2 * (ρa * complexConj K ρa)) ^ 37 +
          (-(ρb * complexConj K ρb)) ^ 37 =
        (δ : K) * (Λ : K) ^ (2 * e - 1) * (ρ0 ^ 2) ^ 37 := by
  -- Discharge the crux (step 5): get the real integer unit `θ'`.
  obtain ⟨θ', hθ'real, hθ'id⟩ := washington_section91_crux_unit hA hB hA1 hB1 hAB hABp
  -- The field unit `θ'_field := Units.map (algebraMap) θ'`, σ-fixed.
  set θ'_field : Kˣ := Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) θ' with hθ'f_def
  have hθ'f_coe : (θ'_field : K) = algebraMap (𝓞 K) K (θ' : 𝓞 K) := by
    rw [hθ'f_def, Units.coe_map, MonoidHom.coe_coe]
  have hθ'f_real : complexConj K (θ'_field : K) = (θ'_field : K) := by
    rw [hθ'f_coe]
    rw [show algebraMap (𝓞 K) K (θ' : 𝓞 K) = ((θ' : 𝓞 K) : K) from rfl,
      ← coe_ringOfIntegersComplexConj, hθ'real]
  -- Translate the crux identity into the reassembly's `Λa, Λb, Λ`.
  have hcrux : (Λa : K)⁻¹ - (Λb : K)⁻¹ = (θ'_field : K) * (Λ : K)⁻¹ := by
    rw [hΛa, hΛb, hΛ, hθ'f_coe]; exact hθ'id
  -- The two root-power products are `1` (since `ηA·ηA^36 = ηA^37 = 1`).
  have hza : algebraMap (𝓞 K) K ηA * algebraMap (𝓞 K) K (ηA ^ 36) = 1 := by
    rw [← map_mul, mul_comm, ← pow_succ, hA, map_one]
  have hzb : algebraMap (𝓞 K) K ηB * algebraMap (𝓞 K) K (ηB ^ 36) = 1 := by
    rw [← map_mul, mul_comm, ← pow_succ, hB, map_one]
  -- `↑Λa = (1 - ↑ηA)(1 - ↑(ηA^36))` (push `algebraMap` through the product).
  have hΛa' : (Λa : K) = (1 - algebraMap (𝓞 K) K ηA) * (1 - algebraMap (𝓞 K) K (ηA ^ 36)) := by
    rw [hΛa, map_mul, map_sub, map_sub, map_one]
  have hΛb' : (Λb : K) = (1 - algebraMap (𝓞 K) K ηB) * (1 - algebraMap (𝓞 K) K (ηB ^ 36)) := by
    rw [hΛb, map_mul, map_sub, map_sub, map_one]
  -- Apply the reassembly.
  refine ⟨η0 ^ 2 * θ'_field * ηb⁻¹ ^ 2, ?_, ?_⟩
  · -- `δ = η_0²·θ'·η_b⁻²` is σ-fixed: each factor is real (`σ(a⁻¹) = (σa)⁻¹`).
    have hcoe : ((η0 ^ 2 * θ'_field * ηb⁻¹ ^ 2 : Kˣ) : K) =
        (η0 : K) ^ 2 * (θ'_field : K) * ((ηb : K) ^ 2)⁻¹ := by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow]
    rw [hcoe, map_mul, map_mul, map_pow, map_inv₀, map_pow, hη0real, hθ'f_real, hηbreal]
  · exact washington_section91_reassembly he hza hzb hΛa' hΛb'
      hfa_pos hfa_neg hfb_pos hfb_neg hanchor hII hcrux

end Crux

end BernoulliRegular.FLT37.Eichler

end

end
