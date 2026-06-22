module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormSetup
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Trace-form bundle constructor (REF-18c2c5-b deferred closure)

This file constructs the trace-form additive character

  `ψ : AddChar k R'`,  `ψ(x) = ζ_ℓ ^ (Algebra.trace (ZMod ℓ) k x).val`

together with its primitivity and exponent witnesses, then assembles the
remaining `ConcreteStickelbergerSetup`-bundle fields that depend on `ψ`.

The construction is the standard one from
`Mathlib.NumberTheory.LegendreSymbol.AddCharacter`:

1. From a primitive ℓ-th root `ζ_ℓ ∈ R'` and `[NeZero ℓ]`, we obtain an
   additive character `zmodChar ℓ (·) : AddChar (ZMod ℓ) R'`.
2. Composition with the additive part of `Algebra.trace (ZMod ℓ) k`
   gives an additive character on `k`.
3. Primitivity follows from `IsPrimitive.of_ne_one` once we exhibit a
   single `b : k` whose trace is non-zero (provided by
   `FiniteField.trace_to_zmod_nondegenerate`).

The output is packaged as standalone definitions/lemmas — `psiTraceForm`,
`psiTraceForm_isPrimitive`, `psiTraceFormExponent`,
`psiTraceForm_eq_zeta_ell_pow` — that downstream constructors of
`ConcreteStickelbergerSetup` / `TraceFormStickelbergerSetup` can plug in.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

namespace BundleConstruction

universe u v w

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
variable (k : Type u) [Field k] [Algebra (ZMod ℓ) k]
variable (R' : Type v) [Field R']
variable {zeta_ell : R'}

/-- The additive character `ZMod ℓ → R'` given by `a ↦ ζ_ℓ ^ a.val`,
where `ζ_ℓ` is a primitive `ℓ`-th root of unity. This is the
`AddChar.zmodChar` from mathlib applied to the present setting. -/
noncomputable def zmodCharOfPrimitiveRoot
    (hzeta : IsPrimitiveRoot zeta_ell ℓ) :
    AddChar (ZMod ℓ) R' :=
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  AddChar.zmodChar ℓ hzeta.pow_eq_one

@[simp]
theorem zmodCharOfPrimitiveRoot_apply
    (hzeta : IsPrimitiveRoot zeta_ell ℓ) (a : ZMod ℓ) :
    zmodCharOfPrimitiveRoot ℓ R' hzeta a = zeta_ell ^ a.val := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  unfold zmodCharOfPrimitiveRoot
  rw [AddChar.zmodChar_apply]

/-- The trace-form additive character on the residue field `k`:
`ψ(x) = ζ_ℓ ^ Tr_{k/𝔽_ℓ}(x).val`. -/
noncomputable def psiTraceForm (hzeta : IsPrimitiveRoot zeta_ell ℓ) :
    AddChar k R' :=
  (zmodCharOfPrimitiveRoot ℓ R' hzeta).compAddMonoidHom
    (Algebra.trace (ZMod ℓ) k).toAddMonoidHom

@[simp]
theorem psiTraceForm_apply (hzeta : IsPrimitiveRoot zeta_ell ℓ) (x : k) :
    psiTraceForm ℓ k R' hzeta x =
      zeta_ell ^ (Algebra.trace (ZMod ℓ) k x).val := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  unfold psiTraceForm
  rw [AddChar.compAddMonoidHom_apply, zmodCharOfPrimitiveRoot_apply]
  rfl

/-- Exponent function paired with `psiTraceForm`: `psiExponent x = (Tr x).val`. -/
noncomputable def psiTraceFormExponent : k → ℕ :=
  fun x ↦ (Algebra.trace (ZMod ℓ) k x).val

@[simp]
theorem psiTraceFormExponent_apply (x : k) :
    psiTraceFormExponent ℓ k x = (Algebra.trace (ZMod ℓ) k x).val :=
  rfl

/-- The defining equation `ψ(x) = ζ_ℓ ^ psiExponent(x)`. -/
theorem psiTraceForm_eq_zeta_ell_pow
    (hzeta : IsPrimitiveRoot zeta_ell ℓ) (x : k) :
    psiTraceForm ℓ k R' hzeta x = zeta_ell ^ psiTraceFormExponent ℓ k x := by
  rw [psiTraceForm_apply]
  rfl

/-! ### Primitivity

We use `AddChar.IsPrimitive.of_ne_one`: on a field `k`, every non-trivial
additive character is primitive. To show non-triviality, we exhibit
`b : k` with `Tr(b) ≠ 0` and observe that
`zeta_ell ^ (Tr(b)).val ≠ 1` whenever `ζ_ℓ` is a primitive ℓ-th root.
-/

/-- Non-triviality: there is `b ∈ k` with `ψ(b) ≠ 1`. The witness comes from
`FiniteField.trace_to_zmod_nondegenerate` applied to `1 : k` after
identifying `ringChar k = ℓ` (from the algebra structure and primality of ℓ).
-/
theorem psiTraceForm_ne_one [Finite k]
    (hzeta : IsPrimitiveRoot zeta_ell ℓ)
    (h_ringChar : ringChar k = ℓ) :
    psiTraceForm ℓ k R' hzeta ≠ 1 := by
  -- Substitute `ringChar k = ℓ` so the trace map matches our algebra structure.
  subst h_ringChar
  -- Pick a witness `b` with non-vanishing trace.
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate k (a := 1) one_ne_zero
  rw [one_mul] at hb
  -- ψ(b) = ζ_ℓ ^ (Tr b).val. Non-trivial iff (Tr b).val ≠ 0 (mod ringChar k).
  refine AddChar.ne_one_iff.mpr ⟨b, ?_⟩
  rw [psiTraceForm_apply]
  intro h_eq_one
  -- ζ_ℓ^n = 1 ↔ ℓ ∣ n. So (Tr b).val must be divisible by ringChar k.
  have hdvd : ringChar k ∣ (Algebra.trace (ZMod (ringChar k)) k b).val :=
    (hzeta.pow_eq_one_iff_dvd _).mp h_eq_one
  -- But (Tr b).val < ringChar k, so divisibility forces (Tr b).val = 0.
  haveI : NeZero (ringChar k) := ⟨hℓ.out.ne_zero⟩
  have hlt : (Algebra.trace (ZMod (ringChar k)) k b).val < ringChar k :=
    ZMod.val_lt _
  have hzero : (Algebra.trace (ZMod (ringChar k)) k b).val = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd hlt
  -- And val = 0 ↔ x = 0 in ZMod (ringChar k).
  apply hb
  rw [← ZMod.val_eq_zero]
  exact hzero

/-- Primitivity of `psiTraceForm` (in a field target with `ringChar k = ℓ`). -/
theorem psiTraceForm_isPrimitive [Finite k]
    (hzeta : IsPrimitiveRoot zeta_ell ℓ)
    (h_ringChar : ringChar k = ℓ) :
    (psiTraceForm ℓ k R' hzeta).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one
    (psiTraceForm_ne_one ℓ k R' hzeta h_ringChar)

end BundleConstruction

/-! ### Application: `psi`-side bundle constructor

Given the data of `ConcreteStickelbergerSetup` *minus* the four
`psi`-related fields, plus an `[Algebra (ZMod ℓ) k]` instance and the
ringChar witness, we assemble those four fields. The resulting
`mkConcreteFromTrace` constructor produces a full
`ConcreteStickelbergerSetup`.

This isolates the trace-form `psi` choice as the canonical one and
removes it from the user's burden when assembling a bundle. -/

open BundleConstruction

universe u v w

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- **Constructor** for `ConcreteStickelbergerSetup` from the
non-`psi` data plus an `[Algebra (ZMod ℓ) k]` instance and a
characteristic witness, using the canonical trace-form additive
character. -/
noncomputable def mkFromTrace
    (hℓ_ne_p : ℓ ≠ p)
    (f : ℕ) (card_k : Fintype.card k = ℓ ^ f)
    (zeta_k : kˣ) (hzeta_k : IsPrimitiveRoot zeta_k p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_p : R'ˣ) (hzeta_p : IsPrimitiveRoot zeta_p p)
    (zeta_p_int : 𝓞 R')
    (zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ))
    (zeta_ell : R') (hzeta_ell : IsPrimitiveRoot zeta_ell ℓ)
    (zeta_ell_int : 𝓞 R')
    (zeta_ell_int_spec : algebraMap (𝓞 R') R' zeta_ell_int = zeta_ell)
    (π : 𝓞 R') (hπ : π = zeta_ell_int - 1)
    (Q : Ideal (𝓞 R')) (hQ_prime : Q.IsPrime) (hQ : (ℓ : 𝓞 R') ∈ Q)
    (residueMap : 𝓞 R' →+* k)
    (residueMap_surjective : Function.Surjective residueMap)
    (residueMap_ker : RingHom.ker residueMap = Q)
    (zeta_p_int_residue : residueMap zeta_p_int = (zeta_k : k))
    (h_ringChar : ringChar k = ℓ) :
    ConcreteStickelbergerSetup ℓ p k K R' where
  hℓ_ne_p := hℓ_ne_p
  f := f
  card_k := card_k
  zeta_k := zeta_k
  hzeta_k := hzeta_k
  hdiv := hdiv
  zeta_p := zeta_p
  hzeta_p := hzeta_p
  zeta_p_int := zeta_p_int
  zeta_p_int_spec := zeta_p_int_spec
  zeta_ell := zeta_ell
  hzeta_ell := hzeta_ell
  zeta_ell_int := zeta_ell_int
  zeta_ell_int_spec := zeta_ell_int_spec
  π := π
  hπ := hπ
  Q := Q
  hQ_prime := hQ_prime
  hQ := hQ
  residueMap := residueMap
  residueMap_surjective := residueMap_surjective
  residueMap_ker := residueMap_ker
  zeta_p_int_residue := zeta_p_int_residue
  psi := psiTraceForm ℓ k R' hzeta_ell
  hpsi := psiTraceForm_isPrimitive ℓ k R' hzeta_ell h_ringChar
  psiExponent := psiTraceFormExponent ℓ k
  psi_eq_zeta_ell_pow := psiTraceForm_eq_zeta_ell_pow ℓ k R' hzeta_ell

/-- For a bundle built via `mkFromTrace`, the `psi` field equals
`psiTraceForm`. (Definitional, but exposed for downstream use.) -/
@[simp]
theorem mkFromTrace_psi
    (hℓ_ne_p : ℓ ≠ p)
    (f : ℕ) (card_k : Fintype.card k = ℓ ^ f)
    (zeta_k : kˣ) (hzeta_k : IsPrimitiveRoot zeta_k p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_p : R'ˣ) (hzeta_p : IsPrimitiveRoot zeta_p p)
    (zeta_p_int : 𝓞 R')
    (zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ))
    (zeta_ell : R') (hzeta_ell : IsPrimitiveRoot zeta_ell ℓ)
    (zeta_ell_int : 𝓞 R')
    (zeta_ell_int_spec : algebraMap (𝓞 R') R' zeta_ell_int = zeta_ell)
    (π : 𝓞 R') (hπ : π = zeta_ell_int - 1)
    (Q : Ideal (𝓞 R')) (hQ_prime : Q.IsPrime) (hQ : (ℓ : 𝓞 R') ∈ Q)
    (residueMap : 𝓞 R' →+* k)
    (residueMap_surjective : Function.Surjective residueMap)
    (residueMap_ker : RingHom.ker residueMap = Q)
    (zeta_p_int_residue : residueMap zeta_p_int = (zeta_k : k))
    (h_ringChar : ringChar k = ℓ) :
    (mkFromTrace (K := K) hℓ_ne_p f card_k zeta_k hzeta_k hdiv zeta_p hzeta_p
        zeta_p_int zeta_p_int_spec zeta_ell hzeta_ell zeta_ell_int
        zeta_ell_int_spec π hπ Q hQ_prime hQ residueMap residueMap_surjective
        residueMap_ker zeta_p_int_residue h_ringChar).psi =
      psiTraceForm ℓ k R' hzeta_ell :=
  rfl

end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular
