import HasseWeil.Curves.NormValuation
import HasseWeil.Curves.IntegralClosure

/-!
# SmoothPoint ↔ HeightOneSpectrum bridge

Under `[IsAlgClosed F]` + `[C.toAffine.IsElliptic]` (which gives
`IsIntegrallyClosed C.CoordinateRing`, hence `IsDedekindDomain`), the map
`SmoothPoint.toHeightOneSpectrum` sending each smooth F-rational point to its
associated height-one prime of `F[C]` is a bijection.

Combines `maximalIdealAt_injective` + `exists_smoothPoint_of_isMaximal`
(both worker-K, in `NormValuation.lean`) with the fact that in a Dedekind
domain every nonzero prime is maximal (from `DimensionLEOne`) and every
maximal ideal of a non-field is nonzero.

## Main results

* `toHeightOneSpectrum_injective` — the embedding is injective (no hypotheses).
* `toHeightOneSpectrum_surjective` — the embedding is surjective (under
  `[IsAlgClosed F]` + `[IsElliptic]` + `IsIntegrallyClosed`).
* `smoothPointEquivHeightOneSpectrum` — packaged bijection.
-/

open scoped nonZeroDivisors

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- `SmoothPoint.toHeightOneSpectrum` is injective: two smooth points with the
same associated height-one prime have the same coordinates. -/
theorem toHeightOneSpectrum_injective
    [IsIntegrallyClosed C.CoordinateRing] :
    Function.Injective
      (SmoothPoint.toHeightOneSpectrum (C := C)) := by
  intro P Q hPQ
  exact C.maximalIdealAt_injective (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hPQ)

/-- `SmoothPoint.toHeightOneSpectrum` is surjective under `[IsAlgClosed F]`
+ `[C.toAffine.IsElliptic]`: every height-one prime of `F[C]` equals
`maximalIdealAt P` for some smooth F-rational point `P`. -/
theorem toHeightOneSpectrum_surjective
    [IsAlgClosed F] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing] :
    Function.Surjective
      (SmoothPoint.toHeightOneSpectrum (C := C)) := by
  intro v
  have hmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  obtain ⟨P, hP⟩ := C.exists_smoothPoint_of_isMaximal hmax
  exact ⟨P, IsDedekindDomain.HeightOneSpectrum.ext hP⟩

/-- **Packaged bijection**: under `[IsAlgClosed F]` + `[IsElliptic]`, smooth
F-rational points of `C` correspond bijectively to height-one primes of
`C.CoordinateRing`. -/
noncomputable def smoothPointEquivHeightOneSpectrum
    [IsAlgClosed F] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing] :
    C.SmoothPoint ≃ IsDedekindDomain.HeightOneSpectrum C.CoordinateRing :=
  Equiv.ofBijective _ ⟨C.toHeightOneSpectrum_injective,
    C.toHeightOneSpectrum_surjective⟩

@[simp] theorem smoothPointEquivHeightOneSpectrum_apply_asIdeal
    [IsAlgClosed F] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing] (P : C.SmoothPoint) :
    (C.smoothPointEquivHeightOneSpectrum P).asIdeal =
      C.maximalIdealAt P := rfl

end SmoothPlaneCurve

/-! ### A2.1 — Function definition: nonzero ideal → Finsupp on HeightOneSpectrum

For a Dedekind domain `R`, the nonzero ideal `I` factors uniquely as a product
of height-one prime ideals with natural multiplicities. The function
`Ideal.toHeightOneFinsuppNonzero` packages this factorisation as a
`HeightOneSpectrum R →₀ ℕ`.

This is sub-piece A2.1 of the X.2 Pic⁰ chain. Subsequent sub-pieces (A2.2:
multiplicativity, A2.3: extension to `(Ideal R)⁰` as a monoid hom, etc.)
build on this function definition. -/

/-- **A2.1**: for a Dedekind domain `R` and nonzero ideal `I`, package the
    height-one prime factorisation of `I` as a `Finsupp`. The multiplicity
    at `v` is `(Associates.mk v.asIdeal).count (Associates.mk I).factors`.
    Finite support follows from `Ideal.finite_factors`. -/
noncomputable def Ideal.toHeightOneFinsuppNonzero
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ≠ 0) :
    IsDedekindDomain.HeightOneSpectrum R →₀ ℕ := by
  classical
  exact Finsupp.onFinset (Ideal.finite_factors hI).toFinset
    (fun v ↦ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
    (by
      intro v hv_ne_zero
      rw [Set.Finite.mem_toFinset]
      exact (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hv_ne_zero)

@[simp] theorem Ideal.toHeightOneFinsuppNonzero_apply
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    Ideal.toHeightOneFinsuppNonzero hI v =
      (Associates.mk v.asIdeal).count (Associates.mk I).factors :=
  rfl

/-- **A2.2 — multiplicativity at the Finsupp level**: for nonzero ideals
    `I, J` in a Dedekind domain, the Finsupp factorisation of `I·J` is the
    pointwise sum of the factorisations of `I` and `J`.

    Direct from `Associates.count_mul` (`UniqueFactorizationDomain/FactorSet.lean:496`)
    and `Associates.mk_mul_mk`. -/
theorem Ideal.toHeightOneFinsuppNonzero_mul
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I J : Ideal R} (hI : I ≠ 0) (hJ : J ≠ 0) :
    Ideal.toHeightOneFinsuppNonzero (mul_ne_zero hI hJ) =
      Ideal.toHeightOneFinsuppNonzero hI +
        Ideal.toHeightOneFinsuppNonzero hJ := by
  ext v
  rw [Finsupp.add_apply, Ideal.toHeightOneFinsuppNonzero_apply,
    Ideal.toHeightOneFinsuppNonzero_apply, Ideal.toHeightOneFinsuppNonzero_apply,
    ← Associates.mk_mul_mk]
  exact Associates.count_mul (Associates.mk_ne_zero.mpr hI)
    (Associates.mk_ne_zero.mpr hJ) (Associates.irreducible_mk.mpr v.irreducible)

/-- **A2.3 — identity at the Finsupp level**: the unit ideal `(1)` factors as
    the zero Finsupp (no prime divisors). Direct from `Associates.factors_one`. -/
theorem Ideal.toHeightOneFinsuppNonzero_one
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] :
    Ideal.toHeightOneFinsuppNonzero (one_ne_zero : (1 : Ideal R) ≠ 0) = 0 := by
  ext v
  rw [Ideal.toHeightOneFinsuppNonzero_apply, Finsupp.coe_zero, Pi.zero_apply,
    Associates.mk_one, Associates.factors_one]
  exact Associates.count_zero (Associates.irreducible_mk.mpr v.irreducible)

/-! ### A2.4 — Reverse direction: Finsupp → Ideal via finite product

Given a Finsupp `f : HeightOneSpectrum R →₀ ℕ`, the corresponding ideal is the
finite product `∏ v.asIdeal ^ f v` over the support of `f`. -/

/-- **A2.4 def**: Reverse map from `HeightOneSpectrum →₀ ℕ` to `Ideal R` via
    finite product `∏ v.asIdeal ^ f v`. -/
noncomputable def Ideal.fromHeightOneFinsupp
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (f : IsDedekindDomain.HeightOneSpectrum R →₀ ℕ) : Ideal R :=
  f.prod fun v n ↦ v.asIdeal ^ n

/-- **A2.4 zero**: the zero Finsupp maps to the unit ideal (empty product = 1). -/
@[simp] theorem Ideal.fromHeightOneFinsupp_zero
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] :
    Ideal.fromHeightOneFinsupp (0 : IsDedekindDomain.HeightOneSpectrum R →₀ ℕ) = 1 :=
  Finsupp.prod_zero_index

/-- **A2.4 add**: addition on Finsupps maps to multiplication on ideals. -/
theorem Ideal.fromHeightOneFinsupp_add
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (f g : IsDedekindDomain.HeightOneSpectrum R →₀ ℕ) :
    Ideal.fromHeightOneFinsupp (f + g) =
      Ideal.fromHeightOneFinsupp f * Ideal.fromHeightOneFinsupp g := by
  classical
  let h : IsDedekindDomain.HeightOneSpectrum R → ℕ → Ideal R :=
    fun v n ↦ v.asIdeal ^ n
  exact Finsupp.prod_add_index' (h := h)
    (fun v ↦ pow_zero v.asIdeal)
    (fun v m n ↦ pow_add v.asIdeal m n)

/-! ### Helper: Finsupp.prod ↔ finprod bridge

For `f : α →₀ M` and `g : α → M → N` with `g a 0 = 1`, the Finsupp.prod equals
the corresponding finprod. The hypothesis `g a 0 = 1` ensures off-support values
contribute trivially. -/

/-- **Helper** (general-purpose): Finsupp.prod = finprod when off-support values
    are trivial (`g a 0 = 1`). General-purpose; possible mathlib upstream
    contribution candidate. -/
theorem Finsupp.prod_eq_finprod_of_zero_eq_one
    {α : Type*} {M : Type*} [Zero M] {N : Type*} [CommMonoid N]
    (f : α →₀ M) (g : α → M → N) (h_zero : ∀ a, g a 0 = 1) :
    f.prod g = ∏ᶠ a, g a (f a) := by
  classical
  rw [Finsupp.prod]
  refine (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
  intro a ha
  rw [Function.mem_mulSupport] at ha
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h_zero_a
  apply ha
  rw [h_zero_a, h_zero a]

/-! ### A2.5 forward iso: fromHeightOneFinsupp ∘ toHeightOneFinsuppNonzero = id -/

/-- **A2.5 forward**: `fromHeightOneFinsupp ∘ toHeightOneFinsuppNonzero = id` for
    nonzero ideals in a Dedekind domain. Composes the helper with mathlib's
    `Ideal.finprod_heightOneSpectrum_factorization`. -/
theorem Ideal.fromHeightOneFinsupp_toHeightOneFinsuppNonzero
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ≠ 0) :
    Ideal.fromHeightOneFinsupp (Ideal.toHeightOneFinsuppNonzero hI) = I := by
  rw [Ideal.fromHeightOneFinsupp,
    Finsupp.prod_eq_finprod_of_zero_eq_one (Ideal.toHeightOneFinsuppNonzero hI)
      (fun v n ↦ v.asIdeal ^ n) (fun v ↦ pow_zero v.asIdeal)]
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  refine finprod_congr (fun v ↦ ?_)
  rw [Ideal.toHeightOneFinsuppNonzero_apply]
  rfl

/-! ### A3 — FractionalIdeal-level Finsupp ↔ ideal bridge (ℤ-coefficient) -/

/-- **A3 reverse**: fractional ideal from a Finsupp on height-one primes via
    finite zpow product `∏ v.asIdeal ^ f v`. The integer-coefficient version
    of `Ideal.fromHeightOneFinsupp`. -/
noncomputable def FractionalIdeal.fromHeightOneFinsupp
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (f : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) : FractionalIdeal R⁰ K :=
  f.prod (fun v n ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ n)

/-- **A3 reverse zero**: empty Finsupp maps to unit ideal. -/
@[simp] theorem FractionalIdeal.fromHeightOneFinsupp_zero
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    FractionalIdeal.fromHeightOneFinsupp
      (R := R) (K := K) (0 : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) = 1 :=
  Finsupp.prod_zero_index

/-- **A3 reverse add**: addition on Finsupps maps to multiplication on
    FractionalIdeals (zpow_add for integer powers). -/
theorem FractionalIdeal.fromHeightOneFinsupp_add
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (f g : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :
    FractionalIdeal.fromHeightOneFinsupp (R := R) (K := K) (f + g) =
      FractionalIdeal.fromHeightOneFinsupp (K := K) f *
        FractionalIdeal.fromHeightOneFinsupp (K := K) g := by
  classical
  let h : IsDedekindDomain.HeightOneSpectrum R → ℤ → FractionalIdeal R⁰ K :=
    fun v n ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ n
  have hzpow : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      ((v.asIdeal : FractionalIdeal R⁰ K)) ≠ 0 := fun v ↦
    FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot
  exact Finsupp.prod_add_index' (h := h)
    (fun v ↦ zpow_zero _)
    (fun v m n ↦ zpow_add₀ (hzpow v) m n)

/-- **A3 forward iso (count formula)**: for any Finsupp `f`, the count of
    `fromHeightOneFinsupp f` at `v` recovers `f v`. Direct from mathlib's
    `FractionalIdeal.count_finsuppProd` (Factorization.lean:509). -/
theorem FractionalIdeal.count_fromHeightOneFinsupp
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : IsDedekindDomain.HeightOneSpectrum R)
    (f : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :
    FractionalIdeal.count K v (FractionalIdeal.fromHeightOneFinsupp f) = f v :=
  FractionalIdeal.count_finsuppProd K v f

/-! ### Nonzero helper: `Ideal.fromHeightOneFinsupp f ≠ 0`

Each `v.asIdeal` is nonzero (`HeightOneSpectrum.ne_bot`); products of nonzero
ideals are nonzero in a domain. The Finsupp.prod over support has nonzero
value. -/

/-- **Helper**: `Ideal.fromHeightOneFinsupp f ≠ 0` for any Finsupp on
    HeightOneSpectrum. Each prime ideal is nonzero, powers of nonzero ideals
    are nonzero, and Finset.prod of nonzero ideals is nonzero (in a domain). -/
theorem Ideal.fromHeightOneFinsupp_ne_zero
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (f : IsDedekindDomain.HeightOneSpectrum R →₀ ℕ) :
    Ideal.fromHeightOneFinsupp f ≠ 0 := by
  rw [Ideal.fromHeightOneFinsupp, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun v _ ↦ pow_ne_zero _ v.ne_bot

/-! ### A4 foundational: (FractionalIdeal R⁰ K)ˣ → Finsupp bridge

The first sub-piece of A4 (ClassGroup ≃+ Pic): map an invertible fractional
ideal to a Finsupp on height-one primes via the integer-valued count. The
finite support comes from `FractionalIdeal.finite_factors`. -/

/-- **A4 foundational**: for an invertible fractional ideal `I` over a Dedekind
    domain, package the height-one prime count as a `Finsupp ℤ`. -/
noncomputable def FractionalIdeal.unitsToHeightOneFinsupp
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (I : (FractionalIdeal R⁰ K)ˣ) :
    IsDedekindDomain.HeightOneSpectrum R →₀ ℤ := by
  classical
  have h_finite : {v : IsDedekindDomain.HeightOneSpectrum R |
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (I : FractionalIdeal R⁰ K))
  exact Finsupp.onFinset h_finite.toFinset
    (fun v ↦ FractionalIdeal.count K v (I : FractionalIdeal R⁰ K))
    (fun v hv ↦ (Set.Finite.mem_toFinset _).mpr hv)

@[simp] theorem FractionalIdeal.unitsToHeightOneFinsupp_apply
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (I : (FractionalIdeal R⁰ K)ˣ)
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    FractionalIdeal.unitsToHeightOneFinsupp I v =
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) :=
  rfl

/-- **A4 group hom property**: `unitsToHeightOneFinsupp` sends multiplication
    of invertible fractional ideals to addition of Finsupps. Direct from
    `FractionalIdeal.count_mul` + `Units.ne_zero`. -/
theorem FractionalIdeal.unitsToHeightOneFinsupp_mul
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : (FractionalIdeal R⁰ K)ˣ) :
    FractionalIdeal.unitsToHeightOneFinsupp (I * J) =
      FractionalIdeal.unitsToHeightOneFinsupp I +
        FractionalIdeal.unitsToHeightOneFinsupp J := by
  ext v
  rw [FractionalIdeal.unitsToHeightOneFinsupp_apply, Finsupp.add_apply,
    FractionalIdeal.unitsToHeightOneFinsupp_apply,
    FractionalIdeal.unitsToHeightOneFinsupp_apply, Units.val_mul]
  exact FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J)

/-- **A4 identity property**: `unitsToHeightOneFinsupp 1 = 0`. Direct from
    `FractionalIdeal.count_one` (count at v of unit ideal is 0). -/
theorem FractionalIdeal.unitsToHeightOneFinsupp_one
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    FractionalIdeal.unitsToHeightOneFinsupp (1 : (FractionalIdeal R⁰ K)ˣ) = 0 := by
  ext v
  rw [FractionalIdeal.unitsToHeightOneFinsupp_apply, Finsupp.coe_zero, Pi.zero_apply,
    Units.val_one]
  exact FractionalIdeal.count_one K v

/-- **A4 packaged MonoidHom**: `unitsToHeightOneFinsupp` as a structured
    `MonoidHom` from `(FractionalIdeal R⁰ K)ˣ` to `Multiplicative (Finsupp ℤ)`.
    Combines the foundational map with `_mul` and `_one` lemmas. -/
noncomputable def FractionalIdeal.unitsToHeightOneFinsuppMonoidHom
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    (FractionalIdeal R⁰ K)ˣ →*
      Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) where
  toFun I := Multiplicative.ofAdd (FractionalIdeal.unitsToHeightOneFinsupp I)
  map_one' := by
    show Multiplicative.ofAdd (FractionalIdeal.unitsToHeightOneFinsupp 1) = 1
    rw [FractionalIdeal.unitsToHeightOneFinsupp_one]
    rfl
  map_mul' I J := by
    show Multiplicative.ofAdd (FractionalIdeal.unitsToHeightOneFinsupp (I * J)) =
      Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [FractionalIdeal.unitsToHeightOneFinsupp_mul]
    rfl

/-- **A4 principal-ideal bridge (apply form)**: for `x : Kˣ`, the count Finsupp
    of the principal fractional ideal `(x)` at `v` equals the count of the
    `spanSingleton`-form. Direct from `coe_toPrincipalIdeal` +
    `unitsToHeightOneFinsupp_apply`. -/
theorem FractionalIdeal.unitsToHeightOneFinsupp_toPrincipalIdeal_apply
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (x : Kˣ) (v : IsDedekindDomain.HeightOneSpectrum R) :
    FractionalIdeal.unitsToHeightOneFinsupp (toPrincipalIdeal R K x) v =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x : K)) := by
  rw [FractionalIdeal.unitsToHeightOneFinsupp_apply, coe_toPrincipalIdeal]

/-- **Count of a principal fractional ideal `(n/d)`**: for `n ∈ R` nonzero,
    `d ∈ R⁰`, `count K v (spanSingleton R⁰ (n/d))` equals the difference of
    `Associates.count` on the numerator and denominator's principal ideals.
    Direct application of `count_well_defined` with `a := d`, `J := Ideal.span {n}`. -/
theorem FractionalIdeal.count_spanSingleton_mk'
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {n : R} (hn : n ≠ 0) (d : ↥R⁰)
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K n d : K)) =
      ((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {n} : Ideal R)).factors -
        (Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {(d : R)} : Ideal R)).factors : ℤ) := by
  have h_dne : (algebraMap R K) (d : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) d.property
  have h0 : FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K n d : K) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff, IsFractionRing.mk'_eq_div, ne_eq,
      div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hn, h_dne⟩
  have hI : FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K n d : K) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (d : R))⁻¹ *
        ↑(Ideal.span {n} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  exact FractionalIdeal.count_well_defined K v h0 hI

/-- **Principal-to-Finsupp homomorphism**: composition of `toPrincipalIdeal R K`
    with `unitsToHeightOneFinsuppMonoidHom`. Sends `x : Kˣ` to its count
    Finsupp via the principal fractional ideal `(x)`. -/
noncomputable def FractionalIdeal.principalToHeightOneFinsuppMonoidHom
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    Kˣ →* Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :=
  FractionalIdeal.unitsToHeightOneFinsuppMonoidHom.comp (toPrincipalIdeal R K)

/-- **Principal-to-Finsupp on coordinates**: applying the principal-to-Finsupp
    homomorphism at `v` yields `count K v (spanSingleton R⁰ x)`. -/
theorem FractionalIdeal.principalToHeightOneFinsuppMonoidHom_apply
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (x : Kˣ) (v : IsDedekindDomain.HeightOneSpectrum R) :
    Multiplicative.toAdd
        (FractionalIdeal.principalToHeightOneFinsuppMonoidHom (R := R) (K := K) x) v =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x : K)) := by
  show FractionalIdeal.unitsToHeightOneFinsupp (toPrincipalIdeal R K x) v = _
  exact FractionalIdeal.unitsToHeightOneFinsupp_toPrincipalIdeal_apply x v

/-- **Principal-image subgroup**: the range of `principalToHeightOneFinsuppMonoidHom`
    inside `Multiplicative (Finsupp ℤ)`. This is the kernel of the natural
    ClassGroup → Multiplicative-Finsupp-quotient descent. -/
noncomputable def FractionalIdeal.principalImageSubgroup
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    Subgroup (Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ)) :=
  (FractionalIdeal.principalToHeightOneFinsuppMonoidHom (R := R) (K := K)).range

/-- **`principalImageSubgroup` is normal** (since the ambient group is commutative). -/
instance FractionalIdeal.principalImageSubgroup_normal
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    (FractionalIdeal.principalImageSubgroup (R := R) (K := K)).Normal :=
  Subgroup.normal_of_isMulCommutative _

/-- **A4 ClassGroup descent**: `unitsToHeightOneFinsuppMonoidHom` descends to a
    well-defined homomorphism on the quotient group
    `(FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range`, landing in
    `Multiplicative (Finsupp ℤ) ⧸ principalImageSubgroup`. This is the
    ClassGroup → Pic-Finsupp-quotient morphism (modulo `ClassGroup.equiv`). -/
noncomputable def FractionalIdeal.classToFinsuppQuotient
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    (FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range →*
      Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) ⧸
        FractionalIdeal.principalImageSubgroup (R := R) (K := K) := by
  refine QuotientGroup.lift (toPrincipalIdeal R K).range
    ((QuotientGroup.mk' (FractionalIdeal.principalImageSubgroup (R := R) (K := K))).comp
      FractionalIdeal.unitsToHeightOneFinsuppMonoidHom) ?_
  rintro y ⟨x, rfl⟩
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact ⟨x, rfl⟩

/-- **A4 ClassGroup → Pic-Finsupp-quotient morphism** (natural form).
    Compose `classToFinsuppQuotient` with `ClassGroup.equiv K` to land at the
    abstract `ClassGroup R` (independent of the choice of fraction field).
    This is the morphism whose injectivity gives `ClassGroup R ↪ Pic_div_principal`. -/
noncomputable def ClassGroup.toFinsuppQuotient
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    ClassGroup R →*
      Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) ⧸
        FractionalIdeal.principalImageSubgroup (R := R) (K := K) :=
  FractionalIdeal.classToFinsuppQuotient.comp (ClassGroup.equiv K).toMonoidHom

/-- **Equality of nonzero fractional ideals from equal `count` Finsupp**.
    Two nonzero fractional ideals with the same height-one count function are
    equal, by reconstructing each via `finprod_heightOneSpectrum_factorization'`. -/
theorem FractionalIdeal.eq_of_count_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v ↦ by rw [h v]

/-- **A4 kernel-trivial**: `unitsToHeightOneFinsuppMonoidHom` is injective on
    `(FractionalIdeal R⁰ K)ˣ`. Two units with the same count Finsupp factor as
    the same product over height-one primes, hence are equal. -/
theorem FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_injective
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Injective
      (FractionalIdeal.unitsToHeightOneFinsuppMonoidHom (R := R) (K := K)) := by
  intro I J h
  apply Units.ext
  refine FractionalIdeal.eq_of_count_eq (Units.ne_zero I) (Units.ne_zero J) ?_
  intro v
  have := DFunLike.congr_fun (Multiplicative.ofAdd.injective h) v
  rwa [FractionalIdeal.unitsToHeightOneFinsupp_apply,
    FractionalIdeal.unitsToHeightOneFinsupp_apply] at this

/-- **A4 classToFinsuppQuotient is injective**. Kernel-trivial argument:
    if `unitsToHeightOneFinsuppMonoidHom I ∈ principalImageSubgroup`, write it
    as `principalToHeightOneFinsuppMonoidHom x = unitsToHeightOneFinsuppMonoidHom (toPrincipalIdeal x)`,
    then `unitsToHeightOneFinsuppMonoidHom_injective` gives `I = toPrincipalIdeal x`,
    so `I ∈ toPrincipalIdeal.range` and `[I] = 1` in the source quotient. -/
theorem FractionalIdeal.classToFinsuppQuotient_injective
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Injective
      (FractionalIdeal.classToFinsuppQuotient (R := R) (K := K)) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ?_
  rw [eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  revert hy
  refine QuotientGroup.induction_on y ?_
  intro I hI
  change (QuotientGroup.mk' FractionalIdeal.principalImageSubgroup
      (FractionalIdeal.unitsToHeightOneFinsuppMonoidHom I)) = 1 at hI
  simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hI
  obtain ⟨x, hx⟩ := hI
  -- `principalToHeightOneFinsuppMonoidHom x` is defeq `uthsf (toPrincipalIdeal x)`, so `hx` retypes:
  have hx' : FractionalIdeal.unitsToHeightOneFinsuppMonoidHom (toPrincipalIdeal R K x) =
      FractionalIdeal.unitsToHeightOneFinsuppMonoidHom I := hx
  have hI_eq : toPrincipalIdeal R K x = I :=
    FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_injective hx'
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  exact ⟨x, hI_eq⟩

/-- **Surjectivity helper**: any Finsupp on height-one primes arises as the count
    Finsupp of `f.prod (asIdeal · ^ ·)`, which is nonzero. -/
theorem FractionalIdeal.fromFinsupp_ne_zero
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (f : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :
    f.prod (fun w n ↦ (w.asIdeal : FractionalIdeal R⁰ K) ^ n) ≠ 0 := by
  rw [Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr
    (fun v _ ↦ zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))

/-- **A4 surjectivity of `unitsToHeightOneFinsuppMonoidHom`**: every Finsupp on
    height-one primes is the count Finsupp of some unit fractional ideal.
    Constructively: `f` corresponds to `f.prod (asIdeal · ^ ·)`, lifted to a unit
    via `Units.mk0` since the product is nonzero. -/
theorem FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_surjective
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Surjective
      (FractionalIdeal.unitsToHeightOneFinsuppMonoidHom (R := R) (K := K)) := by
  intro mf
  classical
  set f : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ := Multiplicative.toAdd mf
  set I_f : FractionalIdeal R⁰ K :=
    f.prod (fun w n ↦ (w.asIdeal : FractionalIdeal R⁰ K) ^ n)
  have hI_ne : I_f ≠ 0 := FractionalIdeal.fromFinsupp_ne_zero f
  refine ⟨Units.mk0 I_f hI_ne, ?_⟩
  apply Multiplicative.ofAdd.injective
  ext v
  show FractionalIdeal.count K v (I_f : FractionalIdeal R⁰ K) = f v
  exact FractionalIdeal.count_finsuppProd K v f

/-- **A4 classToFinsuppQuotient surjectivity**: the descended map is surjective.
    Follows from `lift_surjective_of_surjective` since the composition
    `mk'_{principalImageSubgroup} ∘ unitsToHeightOneFinsuppMonoidHom` is
    surjective (composition of two surjective maps). -/
theorem FractionalIdeal.classToFinsuppQuotient_surjective
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Surjective
      (FractionalIdeal.classToFinsuppQuotient (R := R) (K := K)) := by
  apply QuotientGroup.lift_surjective_of_surjective
  exact (QuotientGroup.mk'_surjective _).comp
    FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_surjective

/-- **A4 classToFinsuppQuotient bijective**: combined with injectivity, the
    descended map is bijective. Direct combination of `_injective` and
    `_surjective`. -/
theorem FractionalIdeal.classToFinsuppQuotient_bijective
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Bijective
      (FractionalIdeal.classToFinsuppQuotient (R := R) (K := K)) :=
  ⟨FractionalIdeal.classToFinsuppQuotient_injective,
   FractionalIdeal.classToFinsuppQuotient_surjective⟩

/-- **A4 packaged MulEquiv (affine form)**: the `(FracId)ˣ ⧸ (toPrincipalIdeal).range`
    quotient is multiplicatively equivalent to `Multiplicative (Finsupp ℤ) ⧸
    principalImageSubgroup`, by `MulEquiv.ofBijective` from the bijective
    `classToFinsuppQuotient`. -/
noncomputable def FractionalIdeal.classToFinsuppMulEquiv
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    (FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range ≃*
      Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) ⧸
        FractionalIdeal.principalImageSubgroup (R := R) (K := K) :=
  MulEquiv.ofBijective FractionalIdeal.classToFinsuppQuotient
    FractionalIdeal.classToFinsuppQuotient_bijective

/-- **A4 packaged MulEquiv (ClassGroup form)**: the abstract `ClassGroup R` is
    multiplicatively equivalent to `Multiplicative (Finsupp ℤ) ⧸ principalImageSubgroup`.
    Combines `ClassGroup.equiv K` with `classToFinsuppMulEquiv`. -/
noncomputable def ClassGroup.toFinsuppMulEquiv
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    ClassGroup R ≃*
      Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) ⧸
        FractionalIdeal.principalImageSubgroup (R := R) (K := K) :=
  (ClassGroup.equiv K).trans FractionalIdeal.classToFinsuppMulEquiv

/-- **A4 unit-level MulEquiv**: the foundational `(FractionalIdeal R⁰ K)ˣ ≃*
    Multiplicative (Finsupp ℤ)` (without quotients). Direct from `unitsToHeightOneFinsuppMonoidHom`
    being bijective (injective + surjective). -/
noncomputable def FractionalIdeal.unitsToHeightOneFinsuppMulEquiv
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    (FractionalIdeal R⁰ K)ˣ ≃*
      Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :=
  MulEquiv.ofBijective FractionalIdeal.unitsToHeightOneFinsuppMonoidHom
    ⟨FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_injective,
     FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_surjective⟩

/-- **A4 unit-level MulEquiv apply**: the unit-level MulEquiv sends `I` to
    `ofAdd (unitsToHeightOneFinsupp I)`. Direct from definition. -/
@[simp] theorem FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_apply
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (I : (FractionalIdeal R⁰ K)ˣ) :
    FractionalIdeal.unitsToHeightOneFinsuppMulEquiv I =
      Multiplicative.ofAdd (FractionalIdeal.unitsToHeightOneFinsupp I) :=
  rfl

/-- **A4 affine quotient apply on `mk`**: the affine MulEquiv sends `mk I` to
    `mk' principalImageSubgroup (unitsToHeightOneFinsuppMonoidHom I)`. Direct
    from the definition of `classToFinsuppQuotient` via `QuotientGroup.lift`. -/
theorem FractionalIdeal.classToFinsuppMulEquiv_mk
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (I : (FractionalIdeal R⁰ K)ˣ) :
    FractionalIdeal.classToFinsuppMulEquiv (R := R) (K := K)
        (QuotientGroup.mk I : (FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range) =
      QuotientGroup.mk' (FractionalIdeal.principalImageSubgroup (R := R) (K := K))
        (FractionalIdeal.unitsToHeightOneFinsuppMonoidHom I) :=
  rfl

/-- **A4 unit-level MulEquiv inverse (symm)**: the inverse of the bijection
    sends `mf : Multiplicative (Finsupp ℤ)` to the unit fractional ideal
    `Units.mk0 (toAdd mf).prod ...`. Explicit constructive inverse. -/
theorem FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_symm_apply
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (mf : Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ)) :
    (FractionalIdeal.unitsToHeightOneFinsuppMulEquiv (R := R) (K := K)).symm mf =
      Units.mk0
        ((Multiplicative.toAdd mf).prod
          (fun w n ↦ (w.asIdeal : FractionalIdeal R⁰ K) ^ n))
        (FractionalIdeal.fromFinsupp_ne_zero (Multiplicative.toAdd mf)) := by
  classical
  apply (FractionalIdeal.unitsToHeightOneFinsuppMulEquiv (R := R) (K := K)).injective
  rw [MulEquiv.apply_symm_apply]
  have hf : FractionalIdeal.unitsToHeightOneFinsupp
      (Units.mk0
        ((Multiplicative.toAdd mf).prod
          (fun w n ↦ (w.asIdeal : FractionalIdeal R⁰ K) ^ n))
        (FractionalIdeal.fromFinsupp_ne_zero (Multiplicative.toAdd mf))) =
      Multiplicative.toAdd mf := by
    ext v
    rw [FractionalIdeal.unitsToHeightOneFinsupp_apply]
    exact FractionalIdeal.count_finsuppProd K v (Multiplicative.toAdd mf)
  rw [FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_apply, hf]
  rfl

end HasseWeil.Curves
