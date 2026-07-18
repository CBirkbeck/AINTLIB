module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup


/-!
# Galois action on the trace-form additive character

This file connects the cyclotomic Galois action on `R'` to the
Stickelberger psi-shift compatibility for trace-form bundles. The key
input is:

  *Hypothesis*: `σ : R' →+* R'` is a ring hom satisfying
  `σ S.zeta_ell = S.zeta_ell ^ c.val` for some `c : (ZMod ℓ)ˣ`.

The output is a unit `a' : kˣ` (the image of `c` in `kˣ` via the
algebra structure `Algebra (ZMod ℓ) k`) such that
`σ.toMonoidHom.compAddChar S.psi = AddChar.mulShift S.psi a'`.

This discharges the **psi-shift content** of `IsGalCompatible`
restricted to the trace-form refinement. Since the trace form is the
canonical form of every primitive additive character on a finite field,
the trace-form proof handles the substantive case.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- An injective ring endomorphism sends a primitive `ℓ`-th root of unity `ζ` to `ζ ^ c.val`
for some unit `c : (ZMod ℓ)ˣ`: it must send `ζ` to some power `ζ ^ i`, and `i` is coprime to
`ℓ` because the image is again primitive. -/
private theorem exists_zmodUnit_map_eq_pow {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    {R' : Type w} [CommRing R'] [IsDomain R'] {ζ : R'} (hζ : IsPrimitiveRoot ζ ℓ)
    (f : R' →+* R') (hf : Function.Injective f) :
    ∃ c : (ZMod ℓ)ˣ, f ζ = ζ ^ (c : ZMod ℓ).val := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hf_pow : (f ζ) ^ ℓ = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨i, hi_lt, hi⟩ := hζ.eq_pow_of_pow_eq_one hf_pow
  have hi_coprime : i.Coprime ℓ :=
    (hζ.pow_iff_coprime (Fact.out : ℓ.Prime).pos i).mp (hi ▸ hζ.map_of_injective hf)
  refine ⟨ZMod.unitOfCoprime i hi_coprime, ?_⟩
  rw [← hi]
  congr 1
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi_lt]

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

/-- The unit in `kˣ` corresponding to a unit in `(ZMod ℓ)ˣ` via the
algebra map `ZMod ℓ → k`. -/
noncomputable def kUnitOfZModUnit (c : (ZMod ℓ)ˣ) : kˣ :=
  Units.map (algebraMap (ZMod ℓ) k).toMonoidHom c

omit [Fintype k] in
@[simp]
theorem kUnitOfZModUnit_val (c : (ZMod ℓ)ˣ) :
    ((kUnitOfZModUnit (k := k) c : kˣ) : k) =
      algebraMap (ZMod ℓ) k (c : ZMod ℓ) := rfl

omit [Fintype k] in
/-- Trace identity: `Tr(t · (a' · x)) = c · Tr(t · x)` (in `ZMod ℓ`), where
`a' = (algebraMap (ZMod ℓ) k) c`. The product is associated as `t * (a' * x)`
to match the shape arising from `mulShift` in the psi-shift theorems. -/
private theorem trace_mul_kUnit_mul_eq (t : k) (c : (ZMod ℓ)ˣ) (x : k) :
    Algebra.trace (ZMod ℓ) k (t * (((kUnitOfZModUnit (k := k) c : kˣ) : k) * x)) =
      (c : ZMod ℓ) * Algebra.trace (ZMod ℓ) k (t * x) := by
  rw [show t * (((kUnitOfZModUnit (k := k) c : kˣ) : k) * x) = (c : ZMod ℓ) • (t * x) from ?_]
  · rw [(Algebra.trace (ZMod ℓ) k).map_smul]
    rfl
  · rw [kUnitOfZModUnit_val, Algebra.smul_def]
    ring

/-- Trace identity: `Tr(scale · (a' · x)) = c · Tr(scale · x)` (in ZMod ℓ),
where `a' = (algebraMap (ZMod ℓ) k) c`. Used in the psi-shift derivation.
The product is associated as `(traceScale * (a' * x))` to match the shape
arising from `mulShift` in the psi-shift theorem. -/
theorem trace_traceScale_mul_kUnit_mul_eq
    (c : (ZMod ℓ)ˣ) (x : k) :
    Algebra.trace (ZMod ℓ) k
        ((S.traceScale : k) * (((kUnitOfZModUnit (k := k) c : kˣ) : k) * x)) =
      (c : ZMod ℓ) * Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x) :=
  trace_mul_kUnit_mul_eq (S.traceScale : k) c x

/-- Order of `S.zeta_ell` in `R'` equals `ℓ`. -/
theorem orderOf_zeta_ell : orderOf S.zeta_ell = ℓ :=
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  S.hzeta_ell.eq_orderOf.symm

/-- **Trace-form psi-shift derivation.** For `σ : R' →+* R'` whose
action on `S.zeta_ell` is `ζ_ℓ ↦ ζ_ℓ^c.val` for some `c : (ZMod ℓ)ˣ`,
the additive character `S.psi = ζ_ℓ ^ Tr(scale·x).val` is shifted by
`a' = (algebraMap (ZMod ℓ) k) c ∈ kˣ`. -/
theorem psi_shift_of_zetaEll_action
    (σ : R' →+* R') (c : (ZMod ℓ)ˣ)
    (h_act : σ S.zeta_ell = S.zeta_ell ^ (c : ZMod ℓ).val) :
    σ.toMonoidHom.compAddChar S.psi =
      AddChar.mulShift S.psi (kUnitOfZModUnit (k := k) c) := by
  ext x
  change σ (S.psi x) = S.psi ((kUnitOfZModUnit (k := k) c : kˣ) * x)
  -- Unfold both sides via the trace form.
  rw [psi_eq_zeta_ell_pow_trace, psi_eq_zeta_ell_pow_trace,
    map_pow, h_act, ← pow_mul]
  -- Reduce both sides modulo orderOf zeta_ell = ℓ via pow_mod_orderOf.
  rw [← pow_mod_orderOf S.zeta_ell ((c : ZMod ℓ).val *
        (Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val),
      ← pow_mod_orderOf S.zeta_ell
        ((Algebra.trace (ZMod ℓ) k
          ((S.traceScale : k) *
            (((kUnitOfZModUnit (k := k) c : kˣ) : k) * x))).val),
      S.orderOf_zeta_ell]
  -- Goal: ζ_ℓ^((c.val * Tr.val) % ℓ) = ζ_ℓ^(Tr_alt.val % ℓ).
  congr 1
  -- Apply the trace identity: Tr(scale · (a'·x)) = c · Tr(scale·x).
  rw [S.trace_traceScale_mul_kUnit_mul_eq c x]
  -- Goal: (c.val * Tr.val) % ℓ = (c * Tr).val % ℓ.
  rw [ZMod.val_mul, Nat.mod_mod]

/-- For any K-algebra automorphism `f : R' ≃ₐ[K] R'`, there is a unit
`a' : kˣ` with `f.compAddChar S.psi = mulShift S.psi a'`. This is the
psi-shift compatibility for trace-form bundles. -/
theorem isGalPsiShiftCompatible_traceForm
    (f : R' ≃ₐ[K] R') :
    ∃ a' : kˣ,
      (f : R' →+* R').toMonoidHom.compAddChar S.psi =
        AddChar.mulShift S.psi a' := by
  obtain ⟨c, hc⟩ :=
    exists_zmodUnit_map_eq_pow S.hzeta_ell (f : R' →+* R') f.injective
  exact ⟨kUnitOfZModUnit (k := k) c,
    S.psi_shift_of_zetaEll_action (f : R' →+* R') c hc⟩

/-- Bridge: every trace-form bundle satisfies the
`IsGalPsiShiftCompatible` predicate of `ConcreteStickelbergerSetup`. -/
theorem isGalPsiShiftCompatible :
    S.toConcreteStickelbergerSetup.IsGalPsiShiftCompatible :=
  S.isGalPsiShiftCompatible_traceForm

/-- **Closure of c.1.4 for trace-form bundles.** Given a trace-form
bundle and the standard step-2 hypotheses (1 ≤ a ≤ p-1, gaussSumInt^p
≠ 0), produce `γ ∈ 𝓞 K` nonzero with `algebraMap γ = gaussSumInt^p`
AND `γ ∈ descentPrime^(p/e)`. No additional Galois/structural
hypotheses needed; everything is derived from the bundle's data. -/
theorem exists_descentPrime_pow_div
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.toConcreteStickelbergerSetup.gaussSumInt a ^ p ≠ 0) :
    ∃ γ : 𝓞 K, γ ≠ 0 ∧
      algebraMap (𝓞 K) (𝓞 R') γ = S.toConcreteStickelbergerSetup.gaussSumInt a ^ p ∧
      γ ∈ S.toConcreteStickelbergerSetup.descentPrime ^
        (p / S.toConcreteStickelbergerSetup.descentRamificationIdx) :=
  S.toConcreteStickelbergerSetup.exists_descentPrime_pow_div_of_isGalPsiShiftCompatible
    ha₁ ha₂ S.isGalPsiShiftCompatible h_ne_zero

end TraceFormStickelbergerSetup

namespace ConductorFlexibleTraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R')

/-- Order of `S.zeta_ell` in `R'` equals `ℓ`, in the conductor-flexible
trace-form setup. -/
theorem orderOf_zeta_ell : orderOf S.zeta_ell = ℓ :=
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  S.hzeta_ell.eq_orderOf.symm

/-- Flexible trace-form psi-shift derivation.  For `σ : R' →+* R'` whose
action on `S.zeta_ell` is `ζ_ℓ ↦ ζ_ℓ^c.val`, the additive character is
shifted by the corresponding unit of `k`. -/
theorem psi_shift_of_zetaEll_action
    (σ : R' →+* R') (c : (ZMod ℓ)ˣ)
    (h_act : σ S.zeta_ell = S.zeta_ell ^ (c : ZMod ℓ).val) :
    σ.toMonoidHom.compAddChar S.psi =
      AddChar.mulShift S.psi
        (TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c) := by
  ext x
  change σ (S.psi x) =
    S.psi ((TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c : kˣ) * x)
  rw [ConductorFlexibleTraceFormStickelbergerSetup.psi_eq_zeta_ell_pow_trace,
    ConductorFlexibleTraceFormStickelbergerSetup.psi_eq_zeta_ell_pow_trace,
    map_pow, h_act, ← pow_mul]
  rw [← pow_mod_orderOf S.zeta_ell ((c : ZMod ℓ).val *
        (Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val),
      ← pow_mod_orderOf S.zeta_ell
        ((Algebra.trace (ZMod ℓ) k
          ((S.traceScale : k) *
            (((TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c : kˣ)
              : k) * x))).val),
      S.orderOf_zeta_ell]
  congr 1
  rw [TraceFormStickelbergerSetup.trace_mul_kUnit_mul_eq (S.traceScale : k) c x,
    ZMod.val_mul, Nat.mod_mod]

/-- Every conductor-flexible trace-form bundle satisfies the psi-shift
compatibility predicate needed by flexible Galois descent. -/
theorem isGalPsiShiftCompatible :
    S.concrete.IsGalPsiShiftCompatible := by
  intro f
  obtain ⟨c, hc⟩ :=
    exists_zmodUnit_map_eq_pow S.hzeta_ell (f : R' →+* R') f.injective
  exact ⟨TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c,
    S.psi_shift_of_zetaEll_action (f : R' →+* R') c hc⟩

end ConductorFlexibleTraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular
