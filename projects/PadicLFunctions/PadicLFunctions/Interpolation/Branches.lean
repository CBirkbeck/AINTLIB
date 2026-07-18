/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.Padics.AddChar
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Teichmuller
import PadicLFunctions.KubotaLeopoldt.ZetaP

/-!
# Branches of the p-adic zeta function (RJW §5.3, TeX 1885–1979)

For odd `p`, the unit group decomposes as `ℤ_p^× ≅ μ_{p−1} × (1+pℤ_p)` via the
Teichmüller character `ω` and `⟨x⟩ := ω(x)⁻¹x` (RJW Def 5.15). For
`y ∈ 1+pℤ_p` and `s ∈ ℤ_p` the power `y^s` is the unique continuous character
`s ↦ y^s` with value `y` at `1` — built on mathlib's
`PadicInt.addChar_of_value_at_one` (the source defines it as `exp(s·log x)`,
Lem 5.14; `p`-adic exp/log are not yet in mathlib, and the two definitions
agree by uniqueness of continuous characters — recorded replan, decomposition
L5.3.3). The `i`-th branch of the Kubota–Leopoldt `p`-adic L-function is
`ζ_{p,i}(s) = ∫_{ℤ_p^×} ω(x)^i⟨x⟩^{1−s}·ζ_p` (Def 5.16) with interpolation
`ζ_{p,i}(1−k) = (1−p^{k−1})ζ(1−k)` for `k ≡ i mod (p−1)` (Thm 5.17).
-/

open Filter Topology

namespace PadicInt

variable (p : ℕ) [hp : Fact p.Prime]

section teichmuller

open IsLocalRing

/-- `ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+* ZMod p`: mathlib's `PadicInt.residueField`
(whose codomain `IsLocalRing.ResidueField ℤ_[p]` is definitionally this
quotient), restated on the raw quotient to avoid typeclass-resolution friction
through the wrapper. -/
noncomputable def maximalIdealQuotientEquivZMod :
    ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+* ZMod p :=
  PadicInt.residueField

instance : CharP (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) p :=
  charP_of_injective_ringHom (f := (maximalIdealQuotientEquivZMod p).symm.toRingHom)
    (maximalIdealQuotientEquivZMod p).symm.injective p

instance : Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) :=
  Finite.of_equiv _ (maximalIdealQuotientEquivZMod p).symm.toEquiv

/-- L5.3.1 (residue form): the Teichmüller map `ω : ZMod p →*₀ ℤ_[p]`, sending
a nonzero residue to the unique `(p−1)`-th root of unity reducing to it, and
`0` to `0`. Built from mathlib's `Perfection.teichmuller₀` through the
identification of `ZMod p` with (the perfection of) the residue field of
`ℤ_[p]`; mathlib's construction is the adic limit of `p^n`-th powers of lifts
— RJW Def 5.15's `lim_n x^{p^n}`. -/
noncomputable def teichmullerZMod : ZMod p →*₀ ℤ_[p] :=
  (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])).comp <|
    ((PerfectionMap.id p
        (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv.toRingHom.toMonoidWithZeroHom).comp
      (maximalIdealQuotientEquivZMod p).symm.toRingHom.toMonoidWithZeroHom

/-- `ω(a) ≡ a (mod p)`: the Teichmüller lift is a section of reduction. -/
@[simp]
lemma toZMod_teichmullerZMod (a : ZMod p) : toZMod (teichmullerZMod p a) = a := by
  change toZMod
    (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])
      ((PerfectionMap.id p (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv
        ((maximalIdealQuotientEquivZMod p).symm a))) = a
  rw [PadicInt.toZMod_eq_residueField_comp_residue, RingHom.comp_apply]
  change PadicInt.residueField (Ideal.Quotient.mk _ _) = a
  rw [Perfection.mk_teichmuller₀, PerfectionMap.comp_equiv]
  exact (maximalIdealQuotientEquivZMod p).apply_symm_apply a

lemma teichmullerZMod_pow_card_sub_one {a : ZMod p} (ha : a ≠ 0) :
    teichmullerZMod p a ^ (p - 1) = 1 := by
  rw [← map_pow, ZMod.pow_card_sub_one_eq_one ha, map_one]

/-- `ℤ_p` contains a primitive `(p−1)`-th root of unity: the Teichmüller lift
of a generator of `(ZMod p)ˣ` (the prime-to-`p` part of the roots of unity
needed for character orthogonality in the §5.2 determinacy). -/
theorem exists_primitiveRoot_card_sub_one :
    ∃ ζ : ℤ_[p], IsPrimitiveRoot ζ (p - 1) := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  refine ⟨teichmullerZMod p ((g : ZMod p)), ?_, fun l hl => ?_⟩
  · exact teichmullerZMod_pow_card_sub_one p g.ne_zero
  · have htoZ : (g : ZMod p) ^ l = 1 := by
      have h := congrArg (toZMod (p := p)) hl
      rwa [map_pow, toZMod_teichmullerZMod, map_one] at h
    have hgl : g ^ l = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, htoZ, Units.val_one])
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hgl

/-- L5.3.1: the Teichmüller lift `ω(x) ∈ ℤ_[p]` of the reduction of `x` mod `p`
(RJW Def 5.15: "ω(x) ≔ Teichmüller lift of the reduction modulo p of x");
through `teichmullerZMod` this is the limit `lim_n x^{p^n}` of the source. -/
noncomputable def teichmullerFun (x : ℤ_[p]) : ℤ_[p] := teichmullerZMod p (toZMod x)

@[simp]
lemma teichmullerFun_pow_card_sub_one (x : ℤ_[p]ˣ) :
    teichmullerFun p (x : ℤ_[p]) ^ (p - 1) = 1 :=
  teichmullerZMod_pow_card_sub_one p (x.isUnit.map toZMod).ne_zero

lemma teichmullerFun_sub_self_mem (x : ℤ_[p]) :
    teichmullerFun p x - x ∈ Ideal.span {(p : ℤ_[p])} := by
  rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub,
    teichmullerFun, toZMod_teichmullerZMod, sub_self]

lemma teichmullerFun_mul (x y : ℤ_[p]) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y := by
  simp [teichmullerFun]

/-- `ω` is locally constant: it only depends on `x mod p`. -/
lemma teichmullerFun_eq_of_sub_mem {x y : ℤ_[p]}
    (h : x - y ∈ Ideal.span {(p : ℤ_[p])}) :
    teichmullerFun p x = teichmullerFun p y := by
  rw [teichmullerFun, teichmullerFun, show toZMod x = toZMod y by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p]
    exact h]

/-- `ω(x)` is a unit for `x` a unit. -/
lemma isUnit_teichmullerFun (x : ℤ_[p]ˣ) :
    IsUnit (teichmullerFun p (x : ℤ_[p])) :=
  IsUnit.of_pow_eq_one (teichmullerFun_pow_card_sub_one p x)
    (Nat.sub_ne_zero_of_lt hp.1.one_lt)

/-- `ω` is locally constant as a function `ℤ_p → ℤ_p` (it factors through
the reduction mod `p`). -/
lemma isLocallyConstant_teichmullerFun :
    IsLocallyConstant (teichmullerFun p) := by
  intro s
  have hfib : ∀ a : ZMod p, IsOpen {x : ℤ_[p] | toZMod x = a} := by
    intro a
    rw [Metric.isOpen_iff]
    intro x hx
    refine ⟨(p : ℝ) ^ (-1 : ℤ), zpow_pos (by exact_mod_cast hp.out.pos) _,
      fun y hy => ?_⟩
    have hmem : y - x ∈ Ideal.span {((p : ℤ_[p])) ^ 1} := by
      rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact_mod_cast hy.le
    rw [pow_one] at hmem
    have h0 : toZMod (y - x) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
        PadicInt.maximalIdeal_eq_span_p]
      exact hmem
    rw [map_sub, sub_eq_zero] at h0
    simpa only [Set.mem_setOf_eq, h0] using hx
  have hpre : (teichmullerFun p) ⁻¹' s
      = ⋃ a ∈ {a : ZMod p | teichmullerZMod p a ∈ s},
          {x : ℤ_[p] | toZMod x = a} := by
    ext x
    constructor
    · intro hx
      exact Set.mem_biUnion
        (show toZMod x ∈ {a : ZMod p | teichmullerZMod p a ∈ s} from hx) rfl
    · intro hmem
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hmem
      have hxa' : toZMod x = a := hxa
      rw [Set.mem_preimage,
        show teichmullerFun p x = teichmullerZMod p (toZMod x) from rfl, hxa']
      exact ha
  rw [hpre]
  exact isOpen_biUnion fun a _ => hfib a

/-- L5.3.1 (packaged): the Teichmüller character `ω : ℤ_[p]ˣ →* ℤ_[p]ˣ`. -/
noncomputable def teichmuller : ℤ_[p]ˣ →* ℤ_[p]ˣ where
  toFun x := (isUnit_teichmullerFun p x).unit
  map_one' := by
    ext
    simp [teichmullerFun]
  map_mul' x y := by
    ext
    simp [teichmullerFun_mul]

@[simp]
lemma teichmuller_coe (x : ℤ_[p]ˣ) :
    (teichmuller p x : ℤ_[p]) = teichmullerFun p (x : ℤ_[p]) := rfl

/-- Reduction mod `p^M` followed by the cast down to `ZMod p` is reduction
mod `p` (the `toZMod`/`toZModPow` bridge for the `ω`-as-Dirichlet-character
evaluations of T520). -/
lemma castHom_toZModPow_eq_toZMod {M : ℕ} (hM : M ≠ 0) (x : ℤ_[p]) :
    ZMod.castHom (dvd_pow_self p hM) (ZMod p) (toZModPow M x) = toZMod x := by
  have happr : x - appr x M ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ hM) (appr_spec M x)
  calc ZMod.castHom (dvd_pow_self p hM) (ZMod p) (toZModPow M x)
      = ((appr x M : ℕ) : ZMod p) := by
        rw [show toZModPow M x = ((appr x M : ℕ) : ZMod (p ^ M)) from rfl,
          map_natCast]
    _ = ((zmodRepr x : ℕ) : ZMod p) :=
        zmod_congr_of_sub_mem_max_ideal x _ _ happr (sub_zmodRepr_mem x)
    _ = toZMod x := rfl

/-- L5.3.7 sub-leaf (T520): the Teichmüller character `ω` as a Dirichlet
character mod `p` (its values on `(ZMod p)ˣ` are the `(p−1)`-th roots of
unity; non-units of `ZMod p` — i.e. `0` — go to `0`). -/
noncomputable def teichmullerChar : DirichletCharacter ℤ_[p] p :=
  { (teichmullerZMod p).toMonoidHom with
    map_nonunit' := fun a ha => by
      rw [isUnit_iff_ne_zero, not_not] at ha
      simp [ha] }

@[simp]
lemma teichmullerChar_apply (a : ZMod p) :
    teichmullerChar p a = teichmullerZMod p a := rfl

/-- The defining compatibility `ω(x mod p) = ω(x)` (decomposition L5.3.7
attack [1]). -/
@[simp]
lemma teichmullerChar_toZMod (x : ℤ_[p]) :
    teichmullerChar p (toZMod x) = teichmullerFun p x := rfl

end teichmuller

section angleBracket

/-- L5.3.2: the projection `⟨·⟩ : ℤ_[p]ˣ → 1 + pℤ_[p]`, `⟨x⟩ = ω(x)⁻¹·x`
(RJW Def 5.15). Valued in units; the `1 + pℤ_p` membership is the lemma
below. -/
noncomputable def angleUnit (x : ℤ_[p]ˣ) : ℤ_[p]ˣ := (teichmuller p x)⁻¹ * x

lemma angleUnit_sub_one_mem (x : ℤ_[p]ˣ) :
    (angleUnit p x : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])} := by
  rw [show (angleUnit p x : ℤ_[p]) - 1
      = (((teichmuller p x)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
          * ((x : ℤ_[p]) - teichmullerFun p (x : ℤ_[p])) by
    rw [← teichmuller_coe, mul_sub, Units.inv_mul, angleUnit, Units.val_mul],
    ← neg_sub, mul_neg]
  exact neg_mem (Ideal.mul_mem_left _ _ (teichmullerFun_sub_self_mem p _))

lemma angleUnit_mul (x y : ℤ_[p]ˣ) :
    angleUnit p (x * y) = angleUnit p x * angleUnit p y := by
  simp only [angleUnit, map_mul]
  rw [mul_inv_rev, mul_comm (teichmuller p y)⁻¹ (teichmuller p x)⁻¹]
  exact mul_mul_mul_comm (teichmuller p x)⁻¹ (teichmuller p y)⁻¹ x y

/-- The decomposition `x = ω(x)·⟨x⟩` (RJW Def 5.15: "If `x ∈ ℤ_p^×`, then we
can write `x = ω(x)⟨x⟩`"). -/
lemma teichmuller_mul_angleUnit (x : ℤ_[p]ˣ) :
    teichmuller p x * angleUnit p x = x := mul_inv_cancel_left _ _

end angleBracket

section onePAdicPow

/-- Elements of `1 + pℤ_p` are topologically unipotent: `(y−1)^n → 0`. -/
lemma tendsto_pow_atTop_nhds_zero_of_mem_span {w : ℤ_[p]}
    (hw : w ∈ Ideal.span {(p : ℤ_[p])}) :
    Filter.Tendsto (w ^ ·) Filter.atTop (nhds 0) := by
  have h1 : ‖w‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow w 1).mpr (by simpa using hw)
  have h2 : (p : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
    rw [zpow_neg, Nat.cast_one, zpow_one, inv_lt_one_iff₀]
    exact .inr (by exact_mod_cast hp.1.one_lt)
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (h1.trans_lt h2)

/-- The ideal `pℤ_p` is closed (it is the closed ball of radius `p⁻¹`). -/
lemma isClosed_span_p : IsClosed {x : ℤ_[p] | x ∈ Ideal.span {(p : ℤ_[p])}} := by
  rw [show {x : ℤ_[p] | x ∈ Ideal.span {(p : ℤ_[p])}}
      = {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ))} by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, PadicInt.norm_le_pow_iff_mem_span_pow x 1, pow_one]]
  exact isClosed_le continuous_norm continuous_const

/-- L5.3.3: for `y ∈ 1 + pℤ_p` (witnessed by `hy`), the power function
`s ↦ y^s : ℤ_[p] → ℤ_[p]` — the unique continuous additive character with
value `y` at `1` (mathlib `PadicInt.addChar_of_value_at_one`).

Source (Lem 5.14, TeX 1892–1894) defines `x^s := exp(s·log x)`; the two agree
by uniqueness of continuous characters (recorded replan L5.3.3 — the exp/log
development is not in mathlib). -/
noncomputable def onePAdicPow (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    AddChar ℤ_[p] ℤ_[p] :=
  PadicInt.addChar_of_value_at_one (y - 1)
    (tendsto_pow_atTop_nhds_zero_of_mem_span p hy)

@[simp]
lemma onePAdicPow_apply_one (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    onePAdicPow p y hy 1 = y := by
  rw [onePAdicPow, PadicInt.addChar_of_value_at_one_def]
  ring

@[simp]
lemma onePAdicPow_natCast (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (k : ℕ) : onePAdicPow p y hy (k : ℤ_[p]) = y ^ k := by
  rw [← nsmul_one k, AddChar.map_nsmul_eq_pow, onePAdicPow_apply_one]

lemma continuous_onePAdicPow (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    Continuous (onePAdicPow p y hy) :=
  PadicInt.continuous_addChar_of_value_at_one _

/-- Transport of `onePAdicPow` along an equality of bases. -/
lemma onePAdicPow_congr {y z : ℤ_[p]} (h : y = z)
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (s : ℤ_[p]) :
    onePAdicPow p y hy s = onePAdicPow p z (h ▸ hy) s := by
  subst h
  rfl

lemma onePAdicPow_sub_one_mem (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (s : ℤ_[p]) :
    onePAdicPow p y hy s - 1 ∈ Ideal.span {(p : ℤ_[p])} := by
  have hclosed : IsClosed {x : ℤ_[p] |
      onePAdicPow p y hy x - 1 ∈ Ideal.span {(p : ℤ_[p])}} :=
    (isClosed_span_p p).preimage
      ((continuous_onePAdicPow p y hy).sub continuous_const)
  have hnat : Set.range ((↑) : ℕ → ℤ_[p]) ⊆ {x : ℤ_[p] |
      onePAdicPow p y hy x - 1 ∈ Ideal.span {(p : ℤ_[p])}} := by
    rintro _ ⟨k, rfl⟩
    have hq : Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p])}) y = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hy
    simp only [Set.mem_setOf_eq, onePAdicPow_natCast]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, hq, one_pow,
      sub_self]
  exact closure_minimal hnat hclosed
    (by rw [(PadicInt.denseRange_natCast (p := p)).closure_eq]; trivial)

/-- The strengthened congruence: if `y ≡ 1 mod p^m` then `y^s ≡ 1 mod p^m`
for every `s ∈ ℤ_p` (the same density/closure argument as
`onePAdicPow_sub_one_mem`, run modulo `p^m`). -/
lemma onePAdicPow_sub_one_mem_pow {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) {m : ℕ}
    (hym : y - 1 ∈ Ideal.span {((p : ℤ_[p])) ^ m}) (s : ℤ_[p]) :
    onePAdicPow p y hy s - 1 ∈ Ideal.span {((p : ℤ_[p])) ^ m} := by
  have hclosed : IsClosed {x : ℤ_[p] |
      onePAdicPow p y hy x - 1 ∈ Ideal.span {((p : ℤ_[p])) ^ m}} := by
    refine IsClosed.preimage
      ((continuous_onePAdicPow p y hy).sub continuous_const) ?_
    rw [show Ideal.span {((p : ℤ_[p])) ^ m}
        = {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ))} by
      ext z
      rw [Set.mem_setOf_eq, PadicInt.norm_le_pow_iff_mem_span_pow]
      rfl]
    exact isClosed_le continuous_norm continuous_const
  have hnat : Set.range ((↑) : ℕ → ℤ_[p]) ⊆ {x : ℤ_[p] |
      onePAdicPow p y hy x - 1 ∈ Ideal.span {((p : ℤ_[p])) ^ m}} := by
    rintro _ ⟨k, rfl⟩
    have hq : Ideal.Quotient.mk (Ideal.span {((p : ℤ_[p])) ^ m}) y = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hym
    simp only [Set.mem_setOf_eq, onePAdicPow_natCast]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, hq,
      one_pow, sub_self]
  exact closure_minimal hnat hclosed
    (by rw [(PadicInt.denseRange_natCast (p := p)).closure_eq]; trivial)

/-- `y·z − 1 ∈ pℤ_p` whenever `y − 1, z − 1 ∈ pℤ_p`: `1 + pℤ_p` is closed
under multiplication. -/
lemma mul_sub_one_mem {y z : ℤ_[p]} (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (hz : z - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    y * z - 1 ∈ Ideal.span {(p : ℤ_[p])} := by
  rw [show y * z - 1 = (y - 1) * z + (z - 1) by ring]
  exact add_mem (Ideal.mul_mem_right _ _ hy) hz

/-- Multiplicativity in the base. -/
lemma onePAdicPow_mul_base (y z : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (hz : z - 1 ∈ Ideal.span {(p : ℤ_[p])}) (s : ℤ_[p]) :
    onePAdicPow p (y * z) (mul_sub_one_mem p hy hz) s
      = onePAdicPow p y hy s * onePAdicPow p z hz s := by
  have hcont : Continuous (onePAdicPow p y hy * onePAdicPow p z hz) :=
    ((continuous_onePAdicPow p y hy).mul (continuous_onePAdicPow p z hz)).congr
      fun a => (AddChar.mul_apply _ _ _).symm
  have heq : onePAdicPow p y hy * onePAdicPow p z hz
      = onePAdicPow p (y * z) (mul_sub_one_mem p hy hz) := by
    refine PadicInt.eq_addChar_of_value_at_one _ hcont ?_
    rw [AddChar.mul_apply, onePAdicPow_apply_one, onePAdicPow_apply_one]
    ring
  exact (DFunLike.congr_fun heq s).symm.trans (AddChar.mul_apply _ _ _)

/-- Uniqueness of the decomposition: an element of `μ_{p−1} ∩ (1+pℤ_p)` is `1`.
For `p = 2` this is degenerate-but-true (`p − 1 = 1`); the substantive odd-`p`
case rests on `(1+pℤ_p)` being torsion-free for prime-to-`p` exponents
(RJW TeX 1900: "Recall that we assume `p` to be odd"). Proved through the
character `s ↦ u^s`: `u^{(p−1)s}` is the trivial character by uniqueness, and
evaluating at `(p−1)⁻¹` gives `u = 1`. -/
lemma eq_one_of_pow_card_sub_one {u : ℤ_[p]ˣ} (hu : u ^ (p - 1) = 1)
    (hmem : (u : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])}) : u = 1 := by
  haveI : Fact (1 < p) := ⟨hp.1.one_lt⟩
  -- `p − 1` is a unit of `ℤ_p` (its residue is `−1 ≠ 0`)
  have hc : IsUnit ((p - 1 : ℕ) : ℤ_[p]) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker,
      map_natCast, Nat.cast_sub hp.1.one_le, ZMod.natCast_self, zero_sub, Nat.cast_one]
    simp
  obtain ⟨c, hc'⟩ := hc
  -- the character `s ↦ u^{(p−1)s}` is trivial…
  have h0 : Filter.Tendsto ((0 : ℤ_[p]) ^ ·) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simp)
  have hshift : Continuous ((onePAdicPow p (u : ℤ_[p]) hmem).mulShift
      ((p - 1 : ℕ) : ℤ_[p])) :=
    ((continuous_onePAdicPow p _ hmem).comp (continuous_const.mul continuous_id)).congr
      fun a => AddChar.mulShift_apply.symm
  have hlam : (onePAdicPow p (u : ℤ_[p]) hmem).mulShift ((p - 1 : ℕ) : ℤ_[p])
      = PadicInt.addChar_of_value_at_one 0 h0 := by
    refine PadicInt.eq_addChar_of_value_at_one _ hshift ?_
    rw [AddChar.mulShift_apply, mul_one, onePAdicPow_natCast,
      ← Units.val_pow_eq_pow_val, hu, Units.val_one, add_zero]
  have htriv : (1 : AddChar ℤ_[p] ℤ_[p]) = PadicInt.addChar_of_value_at_one 0 h0 := by
    refine PadicInt.eq_addChar_of_value_at_one _ ?_ (by rw [AddChar.one_apply, add_zero])
    exact continuous_const.congr fun a => (AddChar.one_apply _).symm
  -- …so evaluating it at `(p−1)⁻¹` gives `u = u^{(p−1)(p−1)⁻¹} = 1`
  have heval := DFunLike.congr_fun (hlam.trans htriv.symm) ((c⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
  rw [AddChar.mulShift_apply, ← hc', Units.mul_inv, onePAdicPow_apply_one,
    AddChar.one_apply] at heval
  exact Units.ext (by rw [heval, Units.val_one])

end onePAdicPow

end PadicInt

namespace PadicLFunctions

open PadicInt

variable (p : ℕ) [hp : Fact p.Prime]

/-- The angle map is continuous as an `ℤ_p`-valued map on `ℤ_pˣ`
(Teichmüller is locally constant and units-inversion is continuous). -/
lemma continuous_angleUnit_val :
    Continuous (fun x : ℤ_[p]ˣ => ((angleUnit p x : ℤ_[p]))) := by
  rw [show (fun x : ℤ_[p]ˣ => ((angleUnit p x : ℤ_[p])))
      = fun x => teichmullerFun p (((x⁻¹ : ℤ_[p]ˣ)) : ℤ_[p]) * (x : ℤ_[p]) by
    funext x
    rw [angleUnit, Units.val_mul, ← map_inv, teichmuller_coe]]
  exact ((isLocallyConstant_teichmullerFun p).continuous.comp
    (PadicMeasure.continuous_units_inv_val p)).mul Units.continuous_val

/-- Base-continuity of the power map: `x ↦ ⟨x⟩^s` is continuous on `ℤ_pˣ`
for each fixed `s ∈ ℤ_p` (via the strengthened congruence
`onePAdicPow_sub_one_mem_pow` at the multiplicative decomposition
`⟨x⟩ = ⟨x₀⟩·w`). -/
lemma continuous_onePAdicPow_angleUnit (s : ℤ_[p]) :
    Continuous (fun x : ℤ_[p]ˣ =>
      onePAdicPow p (angleUnit p x : ℤ_[p]) (angleUnit_sub_one_mem p x) s) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m₀, hm₀⟩ := PadicInt.exists_pow_neg_lt p hε
  set m : ℕ := max m₀ 1
  have hmm : (p : ℝ) ^ (-(m : ℤ)) ≤ (p : ℝ) ^ (-(m₀ : ℤ)) := by
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_lt.le
    exact zpow_le_zpow_right₀ hp1
      (neg_le_neg (by exact_mod_cast le_max_left m₀ 1))
  have hev : ∀ᶠ x in nhds x₀,
      dist ((angleUnit p x : ℤ_[p])) ((angleUnit p x₀ : ℤ_[p]))
        < (p : ℝ) ^ (-(m : ℤ)) :=
    Metric.tendsto_nhds.mp (continuous_angleUnit_val p).continuousAt _
      (zpow_pos (by exact_mod_cast hp.out.pos) _)
  refine hev.mono fun x hclose => ?_
  -- the multiplicative increment `w = ⟨x⟩·⟨x₀⟩⁻¹`
  set w : ℤ_[p] := (angleUnit p x : ℤ_[p])
      * (((angleUnit p x₀)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) with hw
  have hdiff : (angleUnit p x : ℤ_[p]) - (angleUnit p x₀ : ℤ_[p])
      ∈ Ideal.span {((p : ℤ_[p])) ^ m} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [dist_eq_norm] at hclose
    exact hclose.le
  have hw1 : w - 1 ∈ Ideal.span {((p : ℤ_[p])) ^ m} := by
    have hkey : w - 1 = (((angleUnit p x₀)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
        * ((angleUnit p x : ℤ_[p]) - (angleUnit p x₀ : ℤ_[p])) := by
      rw [hw, mul_sub]
      rw [show (((angleUnit p x₀)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
          * (angleUnit p x₀ : ℤ_[p]) = 1 from by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
      ring
    rw [hkey]
    exact Ideal.mul_mem_left _ _ hdiff
  have hwp : w - 1 ∈ Ideal.span {(p : ℤ_[p])} :=
    Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ (by omega)) hw1
  have hxw : (angleUnit p x : ℤ_[p]) = (angleUnit p x₀ : ℤ_[p]) * w := by
    rw [hw, mul_comm ((angleUnit p x : ℤ_[p]))]
    exact (Units.mul_inv_cancel_left _ _).symm
  rw [dist_eq_norm,
    onePAdicPow_congr p hxw (angleUnit_sub_one_mem p x) s,
    show (hxw ▸ angleUnit_sub_one_mem p x : (angleUnit p x₀ : ℤ_[p]) * w - 1
        ∈ Ideal.span {(p : ℤ_[p])})
      = mul_sub_one_mem p (angleUnit_sub_one_mem p x₀) hwp from rfl,
    onePAdicPow_mul_base p _ _ (angleUnit_sub_one_mem p x₀) hwp s]
  have hws := onePAdicPow_sub_one_mem_pow p hwp hw1 s
  calc ‖onePAdicPow p (angleUnit p x₀ : ℤ_[p]) (angleUnit_sub_one_mem p x₀) s
        * onePAdicPow p w hwp s
      - onePAdicPow p (angleUnit p x₀ : ℤ_[p])
          (angleUnit_sub_one_mem p x₀) s‖
      = ‖onePAdicPow p (angleUnit p x₀ : ℤ_[p]) (angleUnit_sub_one_mem p x₀) s‖
        * ‖onePAdicPow p w hwp s - 1‖ := by
        rw [← norm_mul, mul_sub, mul_one]
    _ ≤ 1 * ‖onePAdicPow p w hwp s - 1‖ :=
        mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
    _ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
        rw [one_mul]
        exact (PadicInt.norm_le_pow_iff_mem_span_pow _ m).mpr hws
    _ < ε := lt_of_le_of_lt hmm hm₀

/-- L5.3.4: the continuous character `x ↦ ω(x)^i·⟨x⟩^s` on `ℤ_[p]ˣ`, as a
continuous map into `ℤ_[p]` (RJW TeX 1907–1910). -/
noncomputable def branchChar (i : ℕ) (s : ℤ_[p]) : C(ℤ_[p]ˣ, ℤ_[p]) :=
  ⟨fun x => (teichmuller p x : ℤ_[p]) ^ i
      * onePAdicPow p (angleUnit p x : ℤ_[p]) (angleUnit_sub_one_mem p x) s,
    by
      refine Continuous.mul ?_ (continuous_onePAdicPow_angleUnit p s)
      rw [show (fun x : ℤ_[p]ˣ => ((teichmuller p x : ℤ_[p])) ^ i)
          = fun x : ℤ_[p]ˣ => (teichmullerFun p (Units.val x)) ^ i by
        funext x
        rw [teichmuller_coe]]
      exact ((isLocallyConstant_teichmullerFun p).continuous.comp
        Units.continuous_val).pow i⟩

@[simp]
lemma branchChar_apply (i : ℕ) (s : ℤ_[p]) (x : ℤ_[p]ˣ) :
    branchChar p i s x = (teichmuller p x : ℤ_[p]) ^ i
      * onePAdicPow p (angleUnit p x : ℤ_[p]) (angleUnit_sub_one_mem p x) s :=
  rfl

/-- On the congruence class `k ≡ i mod (p−1)`, the branch character at the
integer `s = k` is `x^k` (RJW TeX 1919: "the character `x^k` can be written in
the form `ω(x)^i⟨x⟩^k` if and only if `k ≡ i mod (p−1)`"; we need the "if").
`PadicMeasure.unitsPowCM` is §4's `x^k`-on-units. -/
lemma branchChar_natCast {i k : ℕ} (hik : (k : ZMod (p - 1)) = (i : ZMod (p - 1))) :
    branchChar p i (k : ℤ_[p]) = PadicMeasure.unitsPowCM p k := by
  ext x
  rw [branchChar_apply, onePAdicPow_natCast,
    show PadicMeasure.unitsPowCM p k x = ((x : ℤ_[p])) ^ k from rfl]
  -- units-level: `ω(x)^i·(ω(x)⁻¹x)^k = x^k` since `ω(x)^i = ω(x)^k`
  have hord : orderOf (teichmuller p x) ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one (Units.ext (by
      rw [Units.val_pow_eq_pow_val, teichmuller_coe,
        teichmullerFun_pow_card_sub_one, Units.val_one]))
  have hmodEq : k ≡ i [MOD p - 1] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hik
  have hpow : (teichmuller p x) ^ k = (teichmuller p x) ^ i :=
    pow_eq_pow_iff_modEq.mpr (hmodEq.of_dvd hord)
  have hunits : (teichmuller p x) ^ i * (angleUnit p x) ^ k = x ^ k := by
    rw [angleUnit, mul_pow, inv_pow, ← mul_assoc, ← hpow, mul_inv_cancel,
      one_mul]
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using congrArg Units.val hunits

/-- L5.3.5/L5.3.6: the `i`-th branch of the Kubota–Leopoldt `p`-adic
L-function: `ζ_{p,i}(s) = ∫_{ℤ_p^×} ω(x)^i⟨x⟩^{1−s}·ζ_p`
(RJW Def 5.16, TeX 1912–1918), realised through the pseudo-measure pairing at
the §4 topological generator and its canonical witness `zetaNum` (junk value
where the pairing degenerates, i.e. at the pole `(i,s) = (0,1)` — RJW's
"meromorphic"). -/
noncomputable def zetaPBranch (hp2 : p ≠ 2) (i : ℕ) (s : ℤ_[p]) : ℚ_[p] :=
  (((branchChar p i (1 - s)
        ((PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose)
      : ℤ_[p]) : ℚ_[p]) - 1)⁻¹
    * ((PadicMeasure.zetaNum p
          (PadicMeasure.exists_nat_topological_generator p hp2).choose
          (branchChar p i (1 - s)) : ℤ_[p]) : ℚ_[p])

/-- **RJW Theorem 5.17** (`thm:kubota leopoldt analytic`, TeX 1921–1924):
"For all `k ≥ 1` with `k ≡ i mod (p−1)`, we have
`ζ_{p,i}(1−k) = (1−p^{k−1})ζ(1−k)`." The right-hand side is §4's rational
`zetaNeg (k−1)` (the same value object as `PadicMeasure.kubotaLeopoldt`; the identification
with the Riemann zeta function is `zetaNeg_eq_riemannZeta` in
`KubotaLeopoldt/ZetaValuesComplex.lean`). -/
theorem zetaPBranch_interpolation (hp2 : p ≠ 2) {i k : ℕ} (hk : 0 < k)
    (hik : (k : ZMod (p - 1)) = (i : ZMod (p - 1))) :
    zetaPBranch p hp2 i ((1 : ℤ_[p]) - (k : ℤ_[p]))
      = (1 - (p : ℚ_[p]) ^ ((k : ℤ) - 1)) * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) := by
  classical
  obtain ⟨hpm, huv, hgen⟩ :=
    (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose_spec
  set m := (PadicMeasure.exists_nat_topological_generator p hp2).choose
  set u := (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose
  have harg : (1 : ℤ_[p]) - ((1 : ℤ_[p]) - (k : ℤ_[p])) = (k : ℤ_[p]) := by ring
  have hbr : branchChar p i ((1 : ℤ_[p]) - ((1 : ℤ_[p]) - (k : ℤ_[p])))
      = PadicMeasure.unitsPowCM p k := by
    rw [harg]
    exact branchChar_natCast p hik
  -- the canonical witness relation `([u]−1)·ζ_p = zetaNum m`
  have hspec : algebraMap _ (PadicMeasure.QuotientField p)
        (PadicMeasure.dirac p u - 1) * PadicMeasure.padicZeta p hp2
      = algebraMap _ _ (PadicMeasure.zetaNum p m) := by
    rw [PadicMeasure.padicZeta]
    exact IsLocalization.mk'_spec' (PadicMeasure.QuotientField p) _ _
  have hmom := PadicMeasure.padicZeta_moments p hp2 u hk
    (PadicMeasure.zetaNum p m) hspec
  rw [zetaPBranch, hbr]
  rw [show PadicMeasure.unitsPowCM p k u = ((u : ℤ_[p])) ^ k from rfl, hmom]
  have hne : (((u : ℤ_[p]) : ℚ_[p])) ^ k - 1 ≠ 0 := by
    refine sub_ne_zero.2 fun h => PadicMeasure.topGen_pow_ne_one p hgen k hk ?_
    exact Subtype.coe_injective (by push_cast; exact h)
  rw [show ((((u : ℤ_[p])) ^ k : ℤ_[p]) : ℚ_[p])
      = (((u : ℤ_[p]) : ℚ_[p])) ^ k from by push_cast; rfl]
  field_simp
  rw [show ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) from by omega, zpow_natCast]
  ring

end PadicLFunctions
