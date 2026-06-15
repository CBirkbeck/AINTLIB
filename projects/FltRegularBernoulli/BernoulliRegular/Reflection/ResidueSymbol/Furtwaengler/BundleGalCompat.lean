module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.BundleConstruction
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.BundleFromCyclotomic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormGalois

/-!
# Galois ψ-shift compatibility for `mkConcreteSetup` bundles (REF-18c2c5-b)

For a `ConcreteStickelbergerSetup` whose `psi` field equals the canonical
trace-form additive character `psiTraceForm`, the Galois ψ-shift
compatibility predicate `IsGalPsiShiftCompatible` is unconditional.

This file packages that fact for the high-level constructor
`CyclotomicLocalSetup.mkConcreteSetup`, which builds its bundle by
calling `ConcreteStickelbergerSetup.mkFromTrace` internally — so its
`psi` is `psiTraceForm` by definition, and the trace-form Galois result
applies. The downstream consumer of `IsGalPsiShiftCompatible` therefore
no longer needs to discharge it manually for any bundle assembled
through the cyclotomic local setup pipeline.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- **Generic ψ-shift derivation for trace-form bundles (no scale).**
For any `ConcreteStickelbergerSetup` whose `psi` is the canonical
trace-form character `psiTraceForm` (i.e., scale = 1) and whose
`psiExponent` is the matching `psiTraceFormExponent`, the Galois
ψ-shift identity holds: every ring hom `σ : R' →+* R'` whose action on
`S.zeta_ell` is `ζ_ℓ ↦ ζ_ℓ^c.val` shifts `S.psi` by the unit
`a' = (algebraMap (ZMod ℓ) k) c ∈ kˣ`. -/
theorem psi_shift_of_zetaEll_action_traceForm
    (S : ConcreteStickelbergerSetup ℓ p k K R')
    (h_psi : S.psi = BundleConstruction.psiTraceForm ℓ k R' S.hzeta_ell)
    (σ : R' →+* R') (c : (ZMod ℓ)ˣ)
    (h_act : σ S.zeta_ell = S.zeta_ell ^ (c : ZMod ℓ).val) :
    σ.toMonoidHom.compAddChar S.psi =
      AddChar.mulShift S.psi
        (TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  ext x
  change σ (S.psi x) = S.psi
    ((TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c : kˣ) * x)
  -- Unfold both sides via the trace-form identity (scale = 1).
  rw [h_psi, BundleConstruction.psiTraceForm_apply,
      BundleConstruction.psiTraceForm_apply]
  rw [map_pow, h_act, ← pow_mul]
  -- Reduce both sides modulo `orderOf S.zeta_ell = ℓ`.
  have h_ord : orderOf S.zeta_ell = ℓ := S.hzeta_ell.eq_orderOf.symm
  rw [← pow_mod_orderOf S.zeta_ell ((c : ZMod ℓ).val *
        (Algebra.trace (ZMod ℓ) k x).val),
      ← pow_mod_orderOf S.zeta_ell
        ((Algebra.trace (ZMod ℓ) k
          (((TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c : kˣ)
              : k) * x)).val),
      h_ord]
  congr 1
  -- Apply the trace identity Tr(a' · x) = c · Tr x (no scale).
  have h_trace :
      Algebra.trace (ZMod ℓ) k
          (((TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c : kˣ)
              : k) * x) =
        (c : ZMod ℓ) * Algebra.trace (ZMod ℓ) k x := by
    rw [show
          (((TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c : kˣ)
              : k) * x) =
            (c : ZMod ℓ) • x from ?_]
    · rw [(Algebra.trace (ZMod ℓ) k).map_smul]
      rfl
    · rw [TraceFormStickelbergerSetup.kUnitOfZModUnit_val, Algebra.smul_def]
  rw [h_trace, ZMod.val_mul, Nat.mod_mod]

/-- **Generic ψ-shift compatibility for trace-form bundles (no scale).**
If `S.psi = psiTraceForm`, then `S.IsGalPsiShiftCompatible` holds: for
every K-algebra automorphism `f : R' ≃ₐ[K] R'`, there is a unit
`a' : kˣ` with `f.compAddChar S.psi = mulShift S.psi a'`. -/
theorem isGalPsiShiftCompatible_of_psi_eq_psiTraceForm
    (S : ConcreteStickelbergerSetup ℓ p k K R')
    (h_psi : S.psi = BundleConstruction.psiTraceForm ℓ k R' S.hzeta_ell) :
    S.IsGalPsiShiftCompatible := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  intro f
  -- Apply f to the equation S.zeta_ell^ℓ = 1 to get (f S.zeta_ell)^ℓ = 1.
  have hf_pow : ((f : R' →+* R') S.zeta_ell) ^ ℓ = 1 := by
    rw [← map_pow, S.hzeta_ell.pow_eq_one]
    exact map_one _
  -- f S.zeta_ell = S.zeta_ell^i for some i < ℓ.
  obtain ⟨i, hi_lt, hi⟩ := S.hzeta_ell.eq_pow_of_pow_eq_one hf_pow
  -- f S.zeta_ell is also a primitive ℓ-th root, so i is coprime to ℓ.
  have h_prim : IsPrimitiveRoot ((f : R' →+* R') S.zeta_ell) ℓ :=
    S.hzeta_ell.map_of_injective f.injective
  have hi_coprime : i.Coprime ℓ := by
    have h_prim' : IsPrimitiveRoot (S.zeta_ell ^ i) ℓ := hi ▸ h_prim
    exact (S.hzeta_ell.pow_iff_coprime (Fact.out : ℓ.Prime).pos i).mp h_prim'
  -- Build c : (ZMod ℓ)ˣ from i.
  let c : (ZMod ℓ)ˣ := ZMod.unitOfCoprime i hi_coprime
  refine ⟨TraceFormStickelbergerSetup.kUnitOfZModUnit (k := k) c, ?_⟩
  -- Apply the generic trace-form ψ-shift derivation.
  apply S.psi_shift_of_zetaEll_action_traceForm h_psi (f : R' →+* R') c
  -- Need: f S.zeta_ell = S.zeta_ell ^ (c : ZMod ℓ).val.
  rw [← hi]
  congr 1
  change i = ((ZMod.unitOfCoprime i hi_coprime : (ZMod ℓ)ˣ) : ZMod ℓ).val
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi_lt]

end ConcreteStickelbergerSetup

namespace CyclotomicLocalSetup

variable (p ℓ : ℕ) [hp : Fact p.Prime] [hℓ : Fact ℓ.Prime]
variable (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (R' : Type w) [Field R'] [NumberField R'] [Algebra K R']
  [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- **Unconditional Galois ψ-shift compatibility for `mkConcreteSetup`.**
Every `ConcreteStickelbergerSetup` produced by the high-level cyclotomic
constructor `CyclotomicLocalSetup.mkConcreteSetup` satisfies
`IsGalPsiShiftCompatible`. The proof reduces to the generic trace-form
result: `mkConcreteSetup` calls `mkFromTrace` internally, which sets
`psi := psiTraceForm`, so the trace-form ψ-shift derivation applies. -/
theorem mkConcreteSetup_isGalPsiShiftCompatible
    (Q : Ideal (𝓞 R')) [hQprime : Q.IsPrime] (hQ : (ℓ : 𝓞 R') ∈ Q)
    (hℓ_ne_p : ℓ ≠ p)
    (algZMod :
      letI : Field (𝓞 R' ⧸ Q) := residueFieldOfHQ ℓ R' Q hQ
      @Algebra (ZMod ℓ) (𝓞 R' ⧸ Q) _
        (Field.toSemifield.toDivisionSemiring.toSemiring))
    (f : ℕ)
    (card_k :
      letI : Field (𝓞 R' ⧸ Q) := residueFieldOfHQ ℓ R' Q hQ
      letI : Fintype (𝓞 R' ⧸ Q) := residueFieldFintype ℓ R' Q hQ
      Fintype.card (𝓞 R' ⧸ Q) = ℓ ^ f)
    (zeta_k_val : 𝓞 R' ⧸ Q)
    (hzeta_k_val :
      letI : Field (𝓞 R' ⧸ Q) := residueFieldOfHQ ℓ R' Q hQ
      IsPrimitiveRoot zeta_k_val p)
    (hdiv :
      letI : Fintype (𝓞 R' ⧸ Q) := residueFieldFintype ℓ R' Q hQ
      p ∣ Fintype.card (𝓞 R' ⧸ Q) - 1)
    (zeta_p : R'ˣ) (hzeta_p : IsPrimitiveRoot zeta_p p)
    (zeta_p_int : 𝓞 R')
    (zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ))
    (zeta_p_int_residue : (residueMap R' Q) zeta_p_int = zeta_k_val)
    (h_ringChar :
      letI : Field (𝓞 R' ⧸ Q) := residueFieldOfHQ ℓ R' Q hQ
      ringChar (𝓞 R' ⧸ Q) = ℓ) :
    letI : Field (𝓞 R' ⧸ Q) := residueFieldOfHQ ℓ R' Q hQ
    letI : Fintype (𝓞 R' ⧸ Q) := residueFieldFintype ℓ R' Q hQ
    (mkConcreteSetup (K := K) p ℓ R' Q hQ hℓ_ne_p algZMod f card_k zeta_k_val
        hzeta_k_val hdiv zeta_p hzeta_p zeta_p_int zeta_p_int_spec
        zeta_p_int_residue h_ringChar).IsGalPsiShiftCompatible := by
  letI : Field (𝓞 R' ⧸ Q) := residueFieldOfHQ ℓ R' Q hQ
  letI : Fintype (𝓞 R' ⧸ Q) := residueFieldFintype ℓ R' Q hQ
  letI : Algebra (ZMod ℓ) (𝓞 R' ⧸ Q) := algZMod
  -- The bundle's `psi` is `psiTraceForm` by definition (via `mkFromTrace`).
  apply ConcreteStickelbergerSetup.isGalPsiShiftCompatible_of_psi_eq_psiTraceForm
  rfl

end CyclotomicLocalSetup

end Furtwaengler

end BernoulliRegular
