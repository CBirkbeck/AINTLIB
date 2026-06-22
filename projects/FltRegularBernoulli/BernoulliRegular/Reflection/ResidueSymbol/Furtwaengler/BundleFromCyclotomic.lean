module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.BundleConstruction
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.FullTeichSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer


/-!
# High-level bundle constructor from cyclotomic local data

This file ties together `CyclotomicLocalSetup` (which packages the
cyclotomic primitive roots, integral lifts, and residue field
infrastructure at a chosen prime `Q ⊂ 𝓞 R'` above `ℓ`) with
`BundleConstruction.ConcreteStickelbergerSetup.mkFromTrace` (which
assembles a `ConcreteStickelbergerSetup` from non-`psi` data plus a
trace-form additive character).

The result is a single high-level constructor

  `CyclotomicLocalSetup.mkConcreteSetup`

that takes the chosen prime `Q`, the witness `ℓ ∈ Q`, the user-supplied
arithmetic data, and an explicit `Algebra (ZMod ℓ) (𝓞 R' ⧸ Q)` witness,
and produces a full `ConcreteStickelbergerSetup ℓ p (𝓞 R' ⧸ Q) K R'`.

The `Field` instance on `𝓞 R' ⧸ Q` is fixed internally to
`Ideal.Quotient.field Q` (via `Q_isMaximal hQ`) and the `Fintype` to
`Fintype.ofFinite _` derived from `Ideal.absNorm_ne_zero_of_nonZeroDivisors`,
matching the choices used elsewhere in `CyclotomicLocalSetup`. This avoids
an instance diamond on the `Monoid (𝓞 R' ⧸ Q)` between an
`Ideal.Quotient.commRing`-derived path and a `Field`-derived path.

The residue-field generator `zeta_k` is taken as a plain element together
with its primitive-root witness; the unit form expected by `mkFromTrace`
is constructed locally via `IsPrimitiveRoot.isUnit`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

namespace CyclotomicLocalSetup

universe u v w

variable (p ℓ : ℕ) [hp : Fact p.Prime] [hℓ : Fact ℓ.Prime]
variable (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (R' : Type w) [Field R'] [NumberField R'] [Algebra K R']
  [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- High-level constructor for `ConcreteStickelbergerSetup` starting from a
prime `Q ⊂ 𝓞 R'` above `ℓ`.

The cyclotomic data (`zeta_p`, `zeta_ell`, their integral lifts,
`π = ζ_ℓ - 1`, the residue map) is taken from `CyclotomicLocalSetup`. The
`Field` and `Fintype` instances on `𝓞 R' ⧸ Q` are constructed internally
from `hQ` (`Q_isMaximal` plus `Ideal.absNorm_ne_zero_of_nonZeroDivisors`),
matching `residueFieldOfHQ` and `residueFieldFintype`.

The caller supplies:

* an `Algebra (ZMod ℓ) (𝓞 R' ⧸ Q)` witness (in the bracketed form below;
  the bracket appears after the `Field` `letI` so the `Algebra`'s
  underlying `Semiring` resolves through the canonical
  `Ideal.Quotient.commRing`-path);
* the residue-field arithmetic data: `f`, `card_k`, the primitive root
  `zeta_k_val`, its primitive-root witness, the `hdiv` divisibility, and
  the `ringChar` witness;
* the `p`-th root data `zeta_p`, `hzeta_p`, `zeta_p_int`,
  `zeta_p_int_spec`, plus the `zeta_p_int_residue` compatibility witness.

To avoid an instance diamond on `Monoid (𝓞 R' ⧸ Q)`, the residue-field
generator is taken as a plain element `zeta_k_val : 𝓞 R' ⧸ Q`, and the
`Units` form needed by `mkFromTrace` is built inside the body via
`IsPrimitiveRoot.isUnit`. -/
noncomputable def mkConcreteSetup
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
    ConcreteStickelbergerSetup ℓ p (𝓞 R' ⧸ Q) K R' :=
  letI : Field (𝓞 R' ⧸ Q) := residueFieldOfHQ ℓ R' Q hQ
  letI : Fintype (𝓞 R' ⧸ Q) := residueFieldFintype ℓ R' Q hQ
  letI : Algebra (ZMod ℓ) (𝓞 R' ⧸ Q) := algZMod
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- Build the unit form of the residue-field primitive p-th root.
  let zeta_k : (𝓞 R' ⧸ Q)ˣ := (hzeta_k_val.isUnit hp.out.pos.ne').unit
  have hzeta_k : IsPrimitiveRoot zeta_k p := by
    refine (IsPrimitiveRoot.coe_units_iff (k := p) (ζ := zeta_k)).mp ?_
    change IsPrimitiveRoot ((hzeta_k_val.isUnit hp.out.pos.ne').unit : 𝓞 R' ⧸ Q) p
    rw [IsUnit.unit_spec]
    exact hzeta_k_val
  have zeta_p_int_residue' :
      (residueMap R' Q) zeta_p_int = (zeta_k : 𝓞 R' ⧸ Q) := by
    change (residueMap R' Q) zeta_p_int = ((hzeta_k_val.isUnit hp.out.pos.ne').unit : 𝓞 R' ⧸ Q)
    rw [IsUnit.unit_spec]
    exact zeta_p_int_residue
  ConcreteStickelbergerSetup.mkFromTrace
    (K := K)
    hℓ_ne_p f card_k zeta_k hzeta_k hdiv
    zeta_p hzeta_p zeta_p_int zeta_p_int_spec
    (zetaEll p ℓ R') (zetaEll_isPrimitiveRoot p ℓ R')
    (zetaEllInt p ℓ R') (algebraMap_zetaEllInt p ℓ R')
    (piEll p ℓ R') rfl
    Q hQprime hQ
    (residueMap R' Q)
    (residueMap_surjective R' Q)
    (residueMap_ker R' Q)
    zeta_p_int_residue'
    h_ringChar

/-! ### High-level constructor at a split prime `P` of `𝓞 K`

When the chosen prime `Q ⊂ 𝓞 R'` over `P` has residue degree one
(i.e., the map `𝓞 K ⧸ P → 𝓞 R' ⧸ Q` is a ring iso), the bundle's
residue field can be taken as `𝓞 K ⧸ P` directly. This is the form
required by `K2_2SourceData S` in `PhiPrimeElement.lean`. -/

/-- High-level constructor for `ConcreteStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R'`
from a maximal `P ⊂ 𝓞 K` containing `ℓ` (but not `p`), a chosen prime
`Q ⊂ 𝓞 R'` containing `ℓ`, a splitting iso
`iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)`, and a zeta-residue compatibility
witness.

Assembled witnesses:
* `card_k = ℓ^(inertiaDeg P)` from `cardResidueField_eq_pow_ell_inertiaDeg`,
* `zeta_k = canonicalResidueZetaP P` (with primitivity from
  `canonicalResidueZetaP_isPrimitiveRoot`),
* `hdiv : p ∣ #(𝓞 K ⧸ P) − 1` from `p_dvd_card_residueField_sub_one`,
* `[Algebra (ZMod ℓ) (𝓞 K ⧸ P)]` from `algebra_zmod_residueField`,
* `h_ringChar = ringChar_residueField_eq_ell`,
* `residueMap = residueMap_of_split Q P iso`. -/
noncomputable def mkConcreteSetup_ofSplitPrime
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (zeta_p : R'ˣ) (hzeta_p : IsPrimitiveRoot zeta_p p)
    (zeta_p_int : 𝓞 R')
    (zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ))
    (zeta_p_int_residue_canon :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      residueMap_of_split (K₀ := K) Q P iso zeta_p_int =
        ((BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P
            : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    ConcreteStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R' :=
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : P.IsPrime := hP_max.isPrime
  have card_k :
      Fintype.card (𝓞 K ⧸ P) =
        ℓ ^ ((Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDeg P) :=
    cardResidueField_eq_pow_ell_inertiaDeg P hℓ_in_P
  have hdiv : p ∣ Fintype.card (𝓞 K ⧸ P) - 1 :=
    p_dvd_card_residueField_sub_one P hP_ne_bot hp_notin_P
  have h_ringChar : ringChar (𝓞 K ⧸ P) = ℓ :=
    ringChar_residueField_eq_ell P hℓ_in_P
  let zeta_k_unit : (𝓞 K ⧸ P)ˣ :=
    BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P
  have hzeta_k : IsPrimitiveRoot zeta_k_unit p :=
    BernoulliRegular.Furtwaengler.canonicalResidueZetaP_isPrimitiveRoot
      hP_ne_bot hp_notin_P
  ConcreteStickelbergerSetup.mkFromTrace
    (K := K)
    hℓ_ne_p _ card_k zeta_k_unit hzeta_k hdiv
    zeta_p hzeta_p zeta_p_int zeta_p_int_spec
    (zetaEll p ℓ R') (zetaEll_isPrimitiveRoot p ℓ R')
    (zetaEllInt p ℓ R') (algebraMap_zetaEllInt p ℓ R')
    (piEll p ℓ R') rfl
    Q hQ_prime hQ_in
    (residueMap_of_split (K₀ := K) Q P iso)
    (residueMap_of_split_surjective (K₀ := K) Q P iso)
    (residueMap_of_split_ker (K₀ := K) Q P iso)
    zeta_p_int_residue_canon
    h_ringChar

/-- High-level constructor for `TraceFormStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R'`
extending `mkConcreteSetup_ofSplitPrime`.

Adds:
* `traceScale := 1`,
* `psiExponent_trace`: the exponent equals `(Tr (1 · x)).val`, automatic
  from `psiTraceFormExponent`,
* `pi_not_mem_Q_sq`: from `pi_not_mem_Q_sq_of_ramification` (cyclotomic
  ramification of `ζ_ℓ - 1` at the prime over `ℓ`). -/
noncomputable def mkTraceForm_ofSplitPrime
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (zeta_p : R'ˣ) (hzeta_p : IsPrimitiveRoot zeta_p p)
    (zeta_p_int : 𝓞 R')
    (zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ))
    (zeta_p_int_residue_canon :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      residueMap_of_split (K₀ := K) Q P iso zeta_p_int =
        ((BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P
            : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    TraceFormStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R' :=
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let S₀ : ConcreteStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R' :=
    mkConcreteSetup_ofSplitPrime (K := K) (R' := R') p ℓ
      P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
      Q hQ_in iso zeta_p hzeta_p zeta_p_int zeta_p_int_spec
      zeta_p_int_residue_canon
  have hQ_ne_bot : Q ≠ ⊥ := Q_ne_bot ℓ R' Q hQ_in
  have h_pi_not_in_Q_sq : zetaEllInt p ℓ R' - 1 ∉ Q ^ 2 :=
    pi_not_mem_Q_sq_of_ramification hℓ_ne_p.symm
      (zetaEllInt p ℓ R') (zetaEllInt_isPrimitiveRoot p ℓ R')
      Q hQ_ne_bot hQ_in
  { toConcreteStickelbergerSetup := S₀
    traceScale := 1
    psiExponent_trace := by
      intro x
      change BundleConstruction.psiTraceFormExponent ℓ (𝓞 K ⧸ P) x =
        (Algebra.trace (ZMod ℓ) (𝓞 K ⧸ P) (((1 : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) * x)).val
      rw [BundleConstruction.psiTraceFormExponent_apply, Units.val_one, one_mul]
    pi_not_mem_Q_sq := h_pi_not_in_Q_sq }

/-! ### Canonical-zeta variant of the split-prime constructor

For use with `K2_2SourceData` whose `h_zeta_p_int_eq` requires
`S.zeta_p_int = algebraMap (cyclotomicZetaInteger K)`, we provide a
specialization that fixes the bundle's `zeta_p_int` to that exact
value.

The `zeta_p` field is set to the unit form of the field-level
algebraMap of `cyclotomicZetaInteger`. -/

/-- The image of `cyclotomicZetaInteger K` in `𝓞 R'`. -/
noncomputable def canonical_zeta_p_int : 𝓞 R' :=
  algebraMap (𝓞 K) (𝓞 R') (BernoulliRegular.cyclotomicZetaInteger (p := p) K)

omit [NumberField R'] [IsScalarTower ℚ K R'] in
/-- The image of `cyclotomicZetaInteger K` is a primitive `p`-th root in `𝓞 R'`. -/
theorem canonical_zeta_p_int_isPrimitiveRoot :
    IsPrimitiveRoot (canonical_zeta_p_int p K R') p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : FaithfulSMul (𝓞 K) (𝓞 R') :=
    FaithfulSMul.of_field_isFractionRing (𝓞 K) (𝓞 R') K R'
  unfold canonical_zeta_p_int
  exact (BernoulliRegular.cyclotomicZetaInteger_isPrimitiveRoot
    (p := p) (K := K)).map_of_injective
    (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 R'))

/-- The unit form of `canonical_zeta_p_int` mapped to `R'`. -/
noncomputable def canonical_zeta_p : R'ˣ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  (((canonical_zeta_p_int_isPrimitiveRoot p K R').map_of_injective
    (FaithfulSMul.algebraMap_injective (𝓞 R') R')).isUnit
    (Fact.out : p.Prime).ne_zero).unit

omit [NumberField R'] [IsScalarTower ℚ K R'] in
theorem algebraMap_canonical_zeta_p_int :
    algebraMap (𝓞 R') R' (canonical_zeta_p_int p K R') =
      (canonical_zeta_p p K R' : R'ˣ) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rfl

omit [NumberField R'] [IsScalarTower ℚ K R'] in
/-- The unit form of `canonical_zeta_p` is a primitive `p`-th root. -/
theorem canonical_zeta_p_isPrimitiveRoot :
    IsPrimitiveRoot (canonical_zeta_p p K R') p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine (IsPrimitiveRoot.coe_units_iff (k := p)
    (ζ := canonical_zeta_p p K R')).mp ?_
  rw [← algebraMap_canonical_zeta_p_int]
  exact (canonical_zeta_p_int_isPrimitiveRoot p K R').map_of_injective
    (FaithfulSMul.algebraMap_injective (𝓞 R') R')

omit [IsScalarTower ℚ K R'] in
/-- **Canonical zeta residue compatibility under K-algebra compat**:
under `IsKAlgebraCompatibleSplittingIso`, the residue map of the
canonical `zeta_p_int = algebraMap (cyclotomicZetaInteger K)` equals
the canonical residue zeta `canonicalResidueZetaP P`. Discharges the
`zeta_p_int_residue_canon` hypothesis of
`mkConcreteSetup_ofSplitPrime_canonical`. -/
theorem canonical_zeta_p_int_residue_of_kAlgebraCompat
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    (Q : Ideal (𝓞 R')) [Q.IsPrime]
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (h_compat : IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    residueMap_of_split (K₀ := K) Q P iso (canonical_zeta_p_int p K R') =
      ((BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P
          : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold canonical_zeta_p_int
  rw [residueMap_of_split_algebraMap (K₀ := K) Q P iso h_compat]
  rfl

/-- **Canonical-zeta split-prime constructor**: builds
`ConcreteStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R'` with
`zeta_p_int := algebraMap (cyclotomicZetaInteger K)` so the
`K2_2SourceData.h_zeta_p_int_eq` field holds by `rfl`. -/
noncomputable def mkConcreteSetup_ofSplitPrime_canonical
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (h_residueMap_zeta :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      residueMap_of_split (K₀ := K) Q P iso (canonical_zeta_p_int p K R') =
        ((BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P
            : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    ConcreteStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R' :=
  mkConcreteSetup_ofSplitPrime (K := K) (R' := R') p ℓ
    P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso
    (canonical_zeta_p p K R')
    (canonical_zeta_p_isPrimitiveRoot p K R')
    (canonical_zeta_p_int p K R')
    (algebraMap_canonical_zeta_p_int p K R')
    h_residueMap_zeta

/-- **Canonical-zeta split-prime constructor (K-algebra compat form)**:
takes only `IsKAlgebraCompatibleSplittingIso` (no explicit
`zeta_p_int_residue_canon`). The compatibility is derived via
`canonical_zeta_p_int_residue_of_kAlgebraCompat`. -/
noncomputable def mkConcreteSetup_ofSplitPrime_canonical_compat
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (h_compat : IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    ConcreteStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R' :=
  mkConcreteSetup_ofSplitPrime_canonical (K := K) (R' := R') p ℓ
    P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso
    (canonical_zeta_p_int_residue_of_kAlgebraCompat (K := K) (R' := R') p P Q iso h_compat)

/-- **Canonical trace-form split-prime constructor (K-algebra compat form)**:
extends `mkConcreteSetup_ofSplitPrime_canonical_compat` to a
`TraceFormStickelbergerSetup`, using the trace-form additive character and the
canonical `p`-th root data. -/
noncomputable def mkTraceForm_ofSplitPrime_canonical_compat
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (h_compat : IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    TraceFormStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R' :=
  mkTraceForm_ofSplitPrime (K := K) (R' := R') p ℓ
    P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso
    (canonical_zeta_p p K R')
    (canonical_zeta_p_isPrimitiveRoot p K R')
    (canonical_zeta_p_int p K R')
    (algebraMap_canonical_zeta_p_int p K R')
    (canonical_zeta_p_int_residue_of_kAlgebraCompat
      (K := K) (R' := R') p P Q iso h_compat)

/-- The concrete bundle under the canonical trace-form constructor is the
canonical compatible split-prime concrete setup. -/
@[simp] theorem mkTraceForm_ofSplitPrime_canonical_compat_toConcrete
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (h_compat : IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    (mkTraceForm_ofSplitPrime_canonical_compat (K := K) (R' := R') p ℓ
      P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso
      h_compat).toConcreteStickelbergerSetup =
      mkConcreteSetup_ofSplitPrime_canonical_compat (K := K) (R' := R') p ℓ
        P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso h_compat := rfl

/-- The canonical bundle's `zeta_p_int` field is `algebraMap
(cyclotomicZetaInteger K)`. -/
@[simp] theorem mkConcreteSetup_ofSplitPrime_canonical_zeta_p_int
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (h_residueMap_zeta :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      residueMap_of_split (K₀ := K) Q P iso (canonical_zeta_p_int p K R') =
        ((BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P
            : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    (mkConcreteSetup_ofSplitPrime_canonical (K := K) (R' := R') p ℓ
      P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso
      h_residueMap_zeta).zeta_p_int =
      algebraMap (𝓞 K) (𝓞 R')
        (BernoulliRegular.cyclotomicZetaInteger (p := p) K) := rfl

/-! ### Field accessors for the split-prime bundle -/

/-- `Q` field of `mkConcreteSetup_ofSplitPrime` is the input `Q`. -/
@[simp] theorem mkConcreteSetup_ofSplitPrime_Q
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (zeta_p : R'ˣ) (hzeta_p : IsPrimitiveRoot zeta_p p)
    (zeta_p_int : 𝓞 R')
    (zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ))
    (zeta_p_int_residue_canon :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      residueMap_of_split (K₀ := K) Q P iso zeta_p_int =
        ((BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P
            : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    (mkConcreteSetup_ofSplitPrime (K := K) (R' := R') p ℓ
      P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso
      zeta_p hzeta_p zeta_p_int zeta_p_int_spec
      zeta_p_int_residue_canon).Q = Q := rfl

/-- `zeta_p_int` field of `mkConcreteSetup_ofSplitPrime` is the input
`zeta_p_int`. -/
@[simp] theorem mkConcreteSetup_ofSplitPrime_zeta_p_int
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (zeta_p : R'ˣ) (hzeta_p : IsPrimitiveRoot zeta_p p)
    (zeta_p_int : 𝓞 R')
    (zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ))
    (zeta_p_int_residue_canon :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      residueMap_of_split (K₀ := K) Q P iso zeta_p_int =
        ((BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P
            : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    (mkConcreteSetup_ofSplitPrime (K := K) (R' := R') p ℓ
      P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso
      zeta_p hzeta_p zeta_p_int zeta_p_int_spec
      zeta_p_int_residue_canon).zeta_p_int = zeta_p_int := rfl

/-- `residueMap` field of `mkConcreteSetup_ofSplitPrime` is
`residueMap_of_split Q P iso`. -/
@[simp] theorem mkConcreteSetup_ofSplitPrime_residueMap
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (zeta_p : R'ˣ) (hzeta_p : IsPrimitiveRoot zeta_p p)
    (zeta_p_int : 𝓞 R')
    (zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ))
    (zeta_p_int_residue_canon :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      residueMap_of_split (K₀ := K) Q P iso zeta_p_int =
        ((BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P
            : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    (mkConcreteSetup_ofSplitPrime (K := K) (R' := R') p ℓ
      P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso
      zeta_p hzeta_p zeta_p_int zeta_p_int_spec
      zeta_p_int_residue_canon).residueMap =
      residueMap_of_split (K₀ := K) Q P iso := rfl

/-- `zeta_k` field of `mkConcreteSetup_ofSplitPrime` is
`canonicalResidueZetaP P`. -/
@[simp] theorem mkConcreteSetup_ofSplitPrime_zeta_k
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (zeta_p : R'ˣ) (hzeta_p : IsPrimitiveRoot zeta_p p)
    (zeta_p_int : 𝓞 R')
    (zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ))
    (zeta_p_int_residue_canon :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      residueMap_of_split (K₀ := K) Q P iso zeta_p_int =
        ((BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P
            : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    (mkConcreteSetup_ofSplitPrime (K := K) (R' := R') p ℓ
      P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso
      zeta_p hzeta_p zeta_p_int zeta_p_int_spec
      zeta_p_int_residue_canon).zeta_k =
      BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P := rfl

/-- `descentPrime` of `mkConcreteSetup_ofSplitPrime` equals `P` whenever
the splitting iso is K-algebra compatible. -/
theorem mkConcreteSetup_ofSplitPrime_descentPrime_eq
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (h_compat : IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    (zeta_p : R'ˣ) (hzeta_p : IsPrimitiveRoot zeta_p p)
    (zeta_p_int : 𝓞 R')
    (zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ))
    (zeta_p_int_residue_canon :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      residueMap_of_split (K₀ := K) Q P iso zeta_p_int =
        ((BernoulliRegular.Furtwaengler.canonicalResidueZetaP (p := p) (K := K) P
            : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    (mkConcreteSetup_ofSplitPrime (K := K) (R' := R') p ℓ
      P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso
      zeta_p hzeta_p zeta_p_int zeta_p_int_spec
      zeta_p_int_residue_canon).descentPrime = P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  unfold ConcreteStickelbergerSetup.descentPrime
  rw [mkConcreteSetup_ofSplitPrime_Q]
  exact under_eq_P_of_kAlgebraCompat (K₀ := K) Q P iso h_compat

/-- `descentPrime` of `mkConcreteSetup_ofSplitPrime_canonical_compat`
equals `P` (since K-algebra compat is the input). -/
theorem mkConcreteSetup_ofSplitPrime_canonical_compat_descentPrime
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (h_compat : IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    (mkConcreteSetup_ofSplitPrime_canonical_compat (K := K) (R' := R') p ℓ
      P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso h_compat).descentPrime = P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  unfold mkConcreteSetup_ofSplitPrime_canonical_compat mkConcreteSetup_ofSplitPrime_canonical
  exact mkConcreteSetup_ofSplitPrime_descentPrime_eq (K := K) (R' := R') p ℓ
    P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p Q hQ_in iso h_compat
    (canonical_zeta_p p K R')
    (canonical_zeta_p_isPrimitiveRoot p K R')
    (canonical_zeta_p_int p K R')
    (algebraMap_canonical_zeta_p_int p K R')
    (canonical_zeta_p_int_residue_of_kAlgebraCompat (K := K) (R' := R') p P Q iso h_compat)

/-! ### FullTeichStickelbergerSetup constructor (data-carrying)

A constructor that takes a `TraceFormStickelbergerSetup` plus
user-supplied `teichUnitFull` and compatibility data, producing a
`FullTeichStickelbergerSetup`. This is pure structure projection;
the substantive Teichmüller construction (requiring `R'` to contain
`(q-1)`-th roots of unity) is left to the consumer. -/

variable {ℓ' p' : ℕ} [Fact p'.Prime] [Fact ℓ'.Prime]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ') k]
variable {K' : Type v} [Field K'] [NumberField K'] [IsCyclotomicExtension {p'} ℚ K']
variable {R'' : Type w} [Field R''] [NumberField R''] [Algebra K' R'']
  [IsScalarTower ℚ K' R''] [IsCyclotomicExtension {p', ℓ'} ℚ R'']

/-- **Constructor for `FullTeichStickelbergerSetup`** packaging an
existing `TraceFormStickelbergerSetup` together with user-supplied
Teichmüller section data. -/
def mkFullTeich_ofTraceForm
    (S : TraceFormStickelbergerSetup ℓ' p' k K' R'')
    (teichUnitFull : kˣ →* (𝓞 R'')ˣ)
    (teichUnitFull_residue :
      ∀ x : kˣ,
        S.toConcreteStickelbergerSetup.residueQuotientEquiv
            (Ideal.Quotient.mk S.toConcreteStickelbergerSetup.Q
              (teichUnitFull x : 𝓞 R'')) =
          (x : k))
    (residueCharInt_eq_teichUnitFull_pow_d :
      ∀ x : kˣ,
        S.toConcreteStickelbergerSetup.residueCharInt (x : k) =
          ((teichUnitFull x : 𝓞 R'') ^
            ((Fintype.card k - 1) / p') : 𝓞 R'')) :
    FullTeichStickelbergerSetup ℓ' p' k K' R'' where
  toTraceFormStickelbergerSetup := S
  teichUnitFull := teichUnitFull
  teichUnitFull_residue := teichUnitFull_residue
  residueCharInt_eq_teichUnitFull_pow_d := residueCharInt_eq_teichUnitFull_pow_d

@[simp] theorem mkFullTeich_ofTraceForm_toTraceFormStickelbergerSetup
    (S : TraceFormStickelbergerSetup ℓ' p' k K' R'')
    (teichUnitFull : kˣ →* (𝓞 R'')ˣ)
    (teichUnitFull_residue :
      ∀ x : kˣ,
        S.toConcreteStickelbergerSetup.residueQuotientEquiv
            (Ideal.Quotient.mk S.toConcreteStickelbergerSetup.Q
              (teichUnitFull x : 𝓞 R'')) =
          (x : k))
    (residueCharInt_eq_teichUnitFull_pow_d :
      ∀ x : kˣ,
        S.toConcreteStickelbergerSetup.residueCharInt (x : k) =
          ((teichUnitFull x : 𝓞 R'') ^
            ((Fintype.card k - 1) / p') : 𝓞 R'')) :
    (mkFullTeich_ofTraceForm S teichUnitFull
      teichUnitFull_residue residueCharInt_eq_teichUnitFull_pow_d).toTraceFormStickelbergerSetup
      = S := rfl

/-! ### FullTeichDworkSetup constructor (data-carrying)

A constructor that takes a `FullTeichStickelbergerSetup` plus
user-supplied Dwork coefficient data, producing a
`FullTeichDworkSetup`. Pure structure projection. -/

/-- **Constructor for `FullTeichDworkSetup`** packaging an existing
`FullTeichStickelbergerSetup` together with user-supplied Dwork
coefficient data: the coefficient sequence and the three
Dwork-expansion hypotheses (`Q^n` containment,
factorial-leading-coefficient identity for `n < ℓ`, and the
multi-index Dwork factorisation of `psiInt` on residue-field units). -/
def mkDwork_ofFullTeich
    (S : FullTeichStickelbergerSetup ℓ' p' k K' R'')
    (dworkCoeff : ℕ → ℕ → 𝓞 R'')
    (dworkCoeff_mem_Q_pow : ∀ N n : ℕ,
      dworkCoeff N n ∈ S.toConcreteStickelbergerSetup.Q ^ n)
    (dworkCoeff_lt_ell_leading : ∀ N n : ℕ, n ≤ N → n < ℓ' →
      ((Nat.factorial n : ℕ) : 𝓞 R'') * dworkCoeff N n -
          S.toConcreteStickelbergerSetup.π ^ n ∈
        S.toConcreteStickelbergerSetup.Q ^ (n + 1))
    (psi_dwork_factorization : ∀ (N : ℕ) (y : kˣ),
      S.toConcreteStickelbergerSetup.psiInt (y : k) -
        (∑ m ∈ multiIndexLE
            S.toConcreteStickelbergerSetup.f N,
          (∏ i : Fin
              S.toConcreteStickelbergerSetup.f,
            dworkCoeff N (m i)) *
          ((S.teichUnitFull
              (S.traceScale * y) : 𝓞 R'') ^
            multiIndexValue ℓ' m)) ∈
      S.toConcreteStickelbergerSetup.Q ^ (N + 1)) :
    FullTeichDworkSetup ℓ' p' k K' R'' where
  toFullTeichStickelbergerSetup := S
  dworkCoeff := dworkCoeff
  dworkCoeff_mem_Q_pow := dworkCoeff_mem_Q_pow
  dworkCoeff_lt_ell_leading := dworkCoeff_lt_ell_leading
  psi_dwork_factorization := psi_dwork_factorization

@[simp] theorem mkDwork_ofFullTeich_toFullTeichStickelbergerSetup
    (S : FullTeichStickelbergerSetup ℓ' p' k K' R'')
    (dworkCoeff : ℕ → ℕ → 𝓞 R'')
    (dworkCoeff_mem_Q_pow : ∀ N n : ℕ,
      dworkCoeff N n ∈ S.toConcreteStickelbergerSetup.Q ^ n)
    (dworkCoeff_lt_ell_leading : ∀ N n : ℕ, n ≤ N → n < ℓ' →
      ((Nat.factorial n : ℕ) : 𝓞 R'') * dworkCoeff N n -
          S.toConcreteStickelbergerSetup.π ^ n ∈
        S.toConcreteStickelbergerSetup.Q ^ (n + 1))
    (psi_dwork_factorization : ∀ (N : ℕ) (y : kˣ),
      S.toConcreteStickelbergerSetup.psiInt (y : k) -
        (∑ m ∈ multiIndexLE
            S.toConcreteStickelbergerSetup.f N,
          (∏ i : Fin
              S.toConcreteStickelbergerSetup.f,
            dworkCoeff N (m i)) *
          ((S.teichUnitFull
              (S.traceScale * y) : 𝓞 R'') ^
            multiIndexValue ℓ' m)) ∈
      S.toConcreteStickelbergerSetup.Q ^ (N + 1)) :
    (mkDwork_ofFullTeich S dworkCoeff dworkCoeff_mem_Q_pow
      dworkCoeff_lt_ell_leading
      psi_dwork_factorization).toFullTeichStickelbergerSetup = S := rfl

end CyclotomicLocalSetup

end Furtwaengler

end BernoulliRegular
