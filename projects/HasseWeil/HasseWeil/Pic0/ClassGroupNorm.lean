import Mathlib

/-!
# The class-group relative norm

For a finite extension `S / R` of Dedekind domains, mathlib's relative ideal norm
`Ideal.relNorm R : Ideal S →*₀ Ideal R` is multiplicative.  Because the norm of a principal
ideal is principal
(`Ideal.relNorm_singleton`), it descends to a group homomorphism on ideal class groups.

## Main definitions

* `HasseWeil.ClassGroup.relNorm : ClassGroup S →* ClassGroup R`: the induced relative norm on
  class groups.

## Main results

* `HasseWeil.ClassGroup.relNorm_mk0`: the value of `relNorm` on the class of an integral ideal.
-/

open scoped nonZeroDivisors

namespace HasseWeil

variable {R S : Type*}
variable [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R]
variable [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [IsDedekindDomain S]
variable [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

/-- The relative norm of an integral ideal, packaged as a homomorphism of `nonZeroDivisors`
monoids `(Ideal S)⁰ →* (Ideal R)⁰`, using that `relNorm` sends nonzero ideals to nonzero ideals
(`Ideal.relNorm_eq_bot_iff`). -/
noncomputable def relNorm0 : (Ideal S)⁰ →* (Ideal R)⁰ where
  toFun I := ⟨Ideal.relNorm R (I : Ideal S), by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, ← bot_eq_zero, Ideal.relNorm_eq_bot_iff,
      bot_eq_zero, ← ne_eq, ← mem_nonZeroDivisors_iff_ne_zero]
    exact I.2⟩
  map_one' := by
    ext
    simp
  map_mul' I J := by
    ext
    simp

/-- The composite "norm then take the class", as a homomorphism `(Ideal S)⁰ →* ClassGroup R`. -/
noncomputable def mk0CompRelNorm0 : (Ideal S)⁰ →* ClassGroup R :=
  (ClassGroup.mk0 (R := R)).comp relNorm0

@[simp]
theorem mk0CompRelNorm0_apply (I : (Ideal S)⁰) :
    mk0CompRelNorm0 (R := R) I = ClassGroup.mk0 (relNorm0 I) := rfl

/-- Well-definedness of the descent: if two integral ideals have the same class in `ClassGroup S`,
their relative norms have the same class in `ClassGroup R`.

The proof reduces, via the principal-difference criterion `ClassGroup.mk0_eq_mk0_iff`, to the
fact that the norm of a principal ideal is principal (`Ideal.relNorm_singleton`): from
`span{x} * I = span{y} * J` (`x, y ≠ 0`) we obtain, by multiplicativity of `relNorm`,
`span{N x} * (relNorm I) = span{N y} * (relNorm J)` with `N x, N y ≠ 0` by
`Algebra.intNorm_ne_zero`. -/
theorem mk0CompRelNorm0_eq_of_mk0_eq {I J : (Ideal S)⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    mk0CompRelNorm0 (R := R) I = mk0CompRelNorm0 (R := R) J := by
  -- Provide the (deliberately non-instance) lift algebra on the fraction fields, so that
  -- `Algebra.intNorm_ne_zero` (which assumes `FiniteDimensional (FractionRing R) (FractionRing S)`)
  -- is available.
  letI : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  haveI : IsScalarTower R (FractionRing R) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization R (FractionRing R) (FractionRing S) S
  haveI : IsScalarTower R S (FractionRing S) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite.of_isLocalization R S R⁰
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  simp only [mk0CompRelNorm0_apply, ClassGroup.mk0_eq_mk0_iff]
  refine ⟨Algebra.intNorm R S x, Algebra.intNorm R S y,
    Algebra.intNorm_ne_zero.mpr hx, Algebra.intNorm_ne_zero.mpr hy, ?_⟩
  change Ideal.span {Algebra.intNorm R S x} * Ideal.relNorm R (I : Ideal S) =
    Ideal.span {Algebra.intNorm R S y} * Ideal.relNorm R (J : Ideal S)
  rw [← Ideal.relNorm_singleton (R := R) x, ← Ideal.relNorm_singleton (R := R) y,
    ← map_mul, ← map_mul, hxy]

/-- The **class-group relative norm**: the monoid homomorphism `ClassGroup S →* ClassGroup R`
induced by `Ideal.relNorm R`.

Since `ClassGroup.mk0 : (Ideal S)⁰ →* ClassGroup S` is surjective, every class has an integral
representative; we send the class of `I` to the class of `Ideal.relNorm R I`.  This is well
defined by `mk0CompRelNorm0_eq_of_mk0_eq`. -/
noncomputable def ClassGroup.relNorm : ClassGroup S →* ClassGroup R where
  toFun c := mk0CompRelNorm0 (Function.surjInv ClassGroup.mk0_surjective c)
  map_one' := by
    rw [← map_one (mk0CompRelNorm0 (R := R) (S := S))]
    apply mk0CompRelNorm0_eq_of_mk0_eq
    rw [Function.surjInv_eq ClassGroup.mk0_surjective, map_one]
  map_mul' a b := by
    rw [← map_mul]
    apply mk0CompRelNorm0_eq_of_mk0_eq
    rw [map_mul, Function.surjInv_eq ClassGroup.mk0_surjective,
      Function.surjInv_eq ClassGroup.mk0_surjective,
      Function.surjInv_eq ClassGroup.mk0_surjective]

/-- The defining computation of `ClassGroup.relNorm` on an integral representative: the relative
norm of the class of `I` is the class of `Ideal.relNorm R I` (which lies in `(Ideal R)⁰` by
`Ideal.relNorm_eq_bot_iff`, here packaged as `relNorm0 I`). -/
@[simp]
theorem ClassGroup.relNorm_mk0 (I : (Ideal S)⁰) :
    ClassGroup.relNorm (ClassGroup.mk0 I) = ClassGroup.mk0 (relNorm0 (R := R) I) := by
  refine (mk0CompRelNorm0_eq_of_mk0_eq ?_).trans (mk0CompRelNorm0_apply I)
  rw [Function.surjInv_eq ClassGroup.mk0_surjective]

/-- `ClassGroup.relNorm` on an integral representative, written with the underlying ideal
`Ideal.relNorm R I` and its membership proof spelled out via `Ideal.relNorm_eq_bot_iff`. -/
theorem ClassGroup.relNorm_mk0' (I : (Ideal S)⁰) :
    ClassGroup.relNorm (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨Ideal.relNorm R (I : Ideal S), by
        rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, ← bot_eq_zero, Ideal.relNorm_eq_bot_iff,
          bot_eq_zero, ← ne_eq, ← mem_nonZeroDivisors_iff_ne_zero]
        exact I.2⟩ :=
  ClassGroup.relNorm_mk0 I

/-! ### The residue-degree-one identity `relNorm 𝔭 = comap 𝔭` (Silverman III.4.10(a), `f = 1`)

The pushforward `φ_*` (the relative norm `relNorm`) and the set-theoretic point image (the
contraction `comap (algebraMap R S) = Ideal.under R`) differ, on a single maximal prime `𝔭`, only
by the **inertia/residue degree** `f`: by `Ideal.relNorm_eq_pow_of_isMaximal` (over a perfect
residue base),

```
relNorm R 𝔭 = (𝔭.under R) ^ inertiaDeg (𝔭.under R) 𝔭 .
```

When `f = inertiaDeg (𝔭.under R) 𝔭 = 1` — which holds at an `F`-rational point of an elliptic
curve, where the residue field is `F` itself, so the entire inseparability of an isogeny (e.g.
Frobenius) lives in the *ramification* `e`, **not** in `f` (Silverman III.4.10(a)) — the power
collapses and `relNorm R 𝔭 = 𝔭.under R = comap (algebraMap R S) 𝔭`.  This is the exact
`relNorm`-vs-`comap` bridge the `Pic⁰` naturality (`Naturality`/`hnat`) needs.

`PerfectField (FractionRing R)` holds for `R = E.CoordinateRing` over a finite field (a finite field
and its function fields are perfect), so the hypothesis is dischargeable in the intended use. -/

/-! #### Unconditional `relNorm 𝔪 = 𝔪.under^f` over a **local** base extension (no `PerfectField`)

Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal`
(`relNorm R P = (P.under R) ^ inertiaDeg (P.under R) P`)
is gated on `PerfectField (FractionRing R)`: its proof reduces to the **Galois** case via the normal
closure, which needs separability.  This is *unnecessary* for the identity itself, but the
obstruction is real for our intended use — a function field over a *finite* field is **imperfect**,
and the isogenies we care about (Frobenius) are **purely inseparable**, so the
normal-closure-Galois trick genuinely does not apply.

The fundamental identity `e · f = [Frac S : Frac R]` (`Ideal.ramificationIdx_mul_inertiaDeg_…`)
holds with **no** separability hypothesis.  When `S` is moreover **local** (a DVR, so a *unique*
prime lies over `p`), this single relation pins the relative-norm exponent **unconditionally**:
`p · S = 𝔪^e` (only prime), `relNorm (p · S) = p^{[Frac S : Frac R]} = p^{e·f}`
(`Ideal.relNorm_algebraMap`, also unconditional), and `relNorm (𝔪^e) = (relNorm 𝔪)^e`, so
`(relNorm 𝔪)^e = (p^f)^e`; comparing with `relNorm 𝔪 = p^s` (`exists_relNorm_eq_pow_of_isPrime`)
and cancelling the prime power gives `s · e = e · f`, i.e. `s = f`.

This is the **`PerfectField`-free** heart of the residue-degree bridge; over a finite base it is
exactly the missing ingredient.  (The general — non-local — base reduces to this by localising at
the prime; mathlib's `Localization.AtPrime` extension API
`Localization.AtPrime.inertiaDeg_map_eq_inertiaDeg` / `…ramificationIdx_map_eq_ramificationIdx`
transports `e`, `f` across the localisation, leaving only the relative-norm/localisation
compatibility — see the residual note after `Ideal.relNorm_eq_under_of_inertiaDeg_one`.) -/

set_option maxHeartbeats 800000 in
-- The `S/R` fraction-field tower + residue-degree `finrank` bookkeeping need elaboration room.
/-- **`relNorm 𝔪 = p ^ inertiaDeg p 𝔪` over a local base extension, unconditionally** (no
`PerfectField`).  For a **local** Dedekind domain `S` (a DVR) module-finite over a Dedekind domain
`R`, with `𝔪 = IsLocalRing.maximalIdeal S` lying over a maximal `p ≠ ⊥` of `R`, the relative norm
of `𝔪` is `p ^ inertiaDeg p 𝔪`.

Proof (see the section note): `p · S = 𝔪^e` (unique prime, via
`Ideal.map_algebraMap_eq_finset_prod_pow` + `IsLocalRing.primesOver_eq`); applying `relNorm` and
`Ideal.relNorm_algebraMap` gives `(relNorm 𝔪)^e = p^{e·f}` using
`Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` (`e·f = [Frac S : Frac R]`); writing
`relNorm 𝔪 = p^s` (`Ideal.exists_relNorm_eq_pow_of_isPrime`) and cancelling the prime power
(`pow_injective_of_not_isUnit`) pins `s = f`.  **No separability / Galois / `PerfectField`.** -/
theorem Ideal.relNorm_maximalIdeal_eq_pow_inertiaDeg_of_isLocalRing
    {R S : Type*}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [IsDedekindDomain S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥)
    [(IsLocalRing.maximalIdeal S).LiesOver p] :
    Ideal.relNorm R (IsLocalRing.maximalIdeal S) =
      p ^ p.inertiaDeg (IsLocalRing.maximalIdeal S) := by
  set m := IsLocalRing.maximalIdeal S with hm
  set e := Ideal.ramificationIdx p m with he_def
  set f := p.inertiaDeg m with hf_def
  haveI : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal S
  have he0 : e ≠ 0 := Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver m hp0
  -- `p · S = 𝔪^e` (the *unique* prime over `p`, so the factorisation is a single term).
  have hmap : Ideal.map (algebraMap R S) p = m ^ e := by
    have hp0' : p ≠ 0 := hp0
    rw [Ideal.map_algebraMap_eq_finsetProd_pow hp0']
    rw [Finset.prod_eq_single m]
    · intro b hb hne
      exact absurd ((Set.mem_singleton_iff).mp
        (by rw [← IsLocalRing.primesOver_eq S hp0, ← Set.mem_toFinset]; exact hb)) hne
    · intro h
      exact absurd (by rw [Set.mem_toFinset, IsLocalRing.primesOver_eq S hp0]; rfl) h
  -- `e · f = [Frac S : Frac R]` (the fundamental identity; *no* separability hypothesis).
  letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  haveI : IsScalarTower R (FractionRing R) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra R _
  haveI : IsScalarTower R S (FractionRing S) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hef : e * f = Module.finrank (FractionRing R) (FractionRing S) :=
    Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing S (FractionRing R) (FractionRing S) hp0
  -- `(relNorm 𝔪)^e = relNorm(𝔪^e) = relNorm(p · S) = p^{[Frac S:Frac R]} = p^{e·f}`.
  have h3 : (Ideal.relNorm R m) ^ e = p ^ (e * f) := by
    rw [← map_pow, ← hmap, Ideal.relNorm_algebraMap, hef]
  -- `relNorm 𝔪 = p^s`; substitute, cancel the prime power, conclude `s = f`.
  obtain ⟨s, hs⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime m p
  rw [hs, ← pow_mul] at h3
  have hpr : Prime p := (Ideal.prime_iff_isPrime hp0).mpr inferInstance
  have hse : s * e = e * f := pow_injective_of_not_isUnit hpr.not_unit hpr.ne_zero h3
  have hsf : s = f :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero he0) (by rw [hse]; ring)
  rw [hs, hsf]

/-- **`relNorm 𝔪 = 𝔪.under` over a local base extension at residue degree one, unconditionally**
(Silverman III.4.10(a), `f = 1`; no `PerfectField`).  Specialisation of
`Ideal.relNorm_maximalIdeal_eq_pow_inertiaDeg_of_isLocalRing` to `inertiaDeg = 1`: the prime power
collapses (`pow_one`) and `p = 𝔪.under R`, giving `relNorm R 𝔪 = 𝔪.under R` (`= comap (algebraMap R
S) 𝔪`) with **no** separability hypothesis. -/
theorem Ideal.relNorm_maximalIdeal_eq_under_of_inertiaDeg_one_of_isLocalRing
    {R S : Type*}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [IsDedekindDomain S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (hp0 : (IsLocalRing.maximalIdeal S).under R ≠ ⊥)
    (hf : Ideal.inertiaDeg ((IsLocalRing.maximalIdeal S).under R)
      (IsLocalRing.maximalIdeal S) = 1) :
    Ideal.relNorm R (IsLocalRing.maximalIdeal S) = (IsLocalRing.maximalIdeal S).under R := by
  haveI : ((IsLocalRing.maximalIdeal S).under R).IsMaximal :=
    Ideal.IsMaximal.under R (IsLocalRing.maximalIdeal S)
  haveI : (IsLocalRing.maximalIdeal S).LiesOver ((IsLocalRing.maximalIdeal S).under R) :=
    Ideal.over_under _
  rw [Ideal.relNorm_maximalIdeal_eq_pow_inertiaDeg_of_isLocalRing hp0, hf, pow_one]

/-! #### Norm-localisation bridges (the `relNorm` "top-localisation" compatibility)

These two lemmas are the genuinely missing ingredients for the `PerfectField`-free general-base
identity (see the residual note after `Ideal.relNorm_eq_under_of_inertiaDeg_one`).  They express
that the relative norm `relNorm` is unchanged when the **top** ring is replaced by a localisation of
itself sharing the same fraction field (e.g. localising the semilocal `Sₚ` at a single prime `Q` to
reach the DVR `Localization.AtPrime Q`).

The key observation is that `Algebra.intNorm A B x` is defined as the restriction of the field norm
`Algebra.norm (Frac A) (algebraMap B (Frac B) x)`, so it depends only on the **fraction field** of
`B`, not on the integral model `B`.  Hence two integral models `B`, `B'` of the same field extension
have the same `intNorm`, and therefore the same `relNorm` on corresponding ideals. -/

/-- **`intNorm` depends only on the common fraction field.** If `B` and `B'` are integrally closed
domains, both integral over `A` and both having `L` as a common fraction field over `K = Frac A`
(with `B → B'` compatible), then `intNorm A B x = intNorm A B' (algebraMap B B' x)`.

This is `Algebra.algebraMap_intNorm` (`algebraMap A K (intNorm A B x) = norm K (algebraMap B L x)`)
applied to both `B` and `B'` with the **same** ambient field `L`: the two field norms coincide
because `algebraMap B L = algebraMap B' L ∘ algebraMap B B'` (the scalar tower `B → B' → L`).
No module-finiteness of `B'` over `A` is required (only finiteness at the fraction-field level
`[FiniteDimensional K L]`), which is why this survives the passage to a non-finite localisation. -/
theorem intNorm_eq_intNorm_of_common_fractionField
    {A K L B B' : Type*}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
    [CommRing B'] [IsDomain B'] [IsIntegrallyClosed B'] [Algebra A B'] [Algebra.IsIntegral A B']
    [Module.IsTorsionFree A B'] [Algebra B' L] [IsScalarTower A B' L] [IsIntegralClosure B' A L]
    [Algebra B B'] [IsScalarTower A B B'] [IsScalarTower B B' L]
    (x : B) :
    Algebra.intNorm A B x = Algebra.intNorm A B' (algebraMap B B' x) := by
  apply IsFractionRing.injective A K
  rw [Algebra.algebraMap_intNorm (K := K) (L := L), Algebra.algebraMap_intNorm (K := K) (L := L)]
  congr 1
  rw [← IsScalarTower.algebraMap_apply B B' L]

/-- **`relNorm` is unchanged under top-localisation of a principal prime.** If `B` is a Dedekind
**PID** (e.g. the semilocal localisation `Sₚ`), `Q` a principal ideal of `B`, and `B'` an
integrally closed domain sharing the fraction field `L = Frac B`, then
`relNorm A Q = relNorm A (Q.map (B → B'))`.

The proof writes `Q = span{π}` (principal), so `relNorm A Q = span{intNorm A B π}` and
`relNorm A (Q.map) = span{intNorm A B' (algebraMap π)}` (`relNorm_singleton`, `Ideal.map_span`),
and the two generators agree by `intNorm_eq_intNorm_of_common_fractionField`.

**Caveat.**  `Ideal.relNorm A B'` is only well-typed under `[Module.Finite A B']` (mathlib's
`relNorm`/`spanNorm` carry this in their definition).  This is exactly why this bridge does **not**
discharge the general-base residual: the intended `B' = Localization.AtPrime Q` (a DVR isolating one
of several primes over `p`) is **not** module-finite over `A = Rₚ` when several primes lie over `p`,
so the right-hand side is ill-typed there.  It applies when finiteness is preserved — e.g. when `Q`
is the *unique* prime over `p` (`finite_of_primesOver_eq_singleton`), which is the already-handled
local case `Ideal.relNorm_maximalIdeal_eq_pow_inertiaDeg_of_isLocalRing`. -/
theorem relNorm_eq_relNorm_localization
    {A K L B B' : Type*}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
    [IsPrincipalIdealRing B]
    [CommRing B'] [IsDomain B'] [IsIntegrallyClosed B'] [IsDedekindDomain B']
    [Algebra A B'] [Algebra.IsIntegral A B'] [Module.Finite A B'] [Module.IsTorsionFree A B']
    [Algebra B' L] [IsScalarTower A B' L] [IsIntegralClosure B' A L]
    [Algebra B B'] [IsScalarTower A B B'] [IsScalarTower B B' L]
    (Q : Ideal B) [Q.IsPrincipal] :
    Ideal.relNorm A Q = Ideal.relNorm A (Q.map (algebraMap B B')) := by
  have hQ : Q = Ideal.span {Submodule.IsPrincipal.generator Q} :=
    (Ideal.span_singleton_generator Q).symm
  rw [hQ, Ideal.relNorm_singleton, Ideal.map_span, Set.image_singleton, Ideal.relNorm_singleton,
    intNorm_eq_intNorm_of_common_fractionField (A := A) (K := K) (L := L) (B := B) (B' := B')]

/-! #### `PerfectField`-free **general-base** reduction to the semilocal relative norm

This block discharges, **without `PerfectField`**, the global-to-semilocal half of the general-base
identity `relNorm R 𝔭 = 𝔭.under` at residue degree one.  The localisation bridge
`relNorm_map_localization` (an instance of mathlib's `Ideal.spanIntNorm_localization`, the same engine
behind `relNorm_eq_relNorm_localization`) transports `relNorm R 𝔭` to the **semilocal**
`Sₚ = Localization (algebraMapSubmonoid S p.primeCompl)` over the DVR `Rₚ = Localization.AtPrime p`,
and `relNorm_eq_under_of_localized` then assembles the whole identity by `eq_of_localization_maximal`:
at primes `q ≠ p` both sides localise to `⊤`, and at `q = p` the claim is exactly the **semilocal
per-prime formula** `relNorm Rₚ (𝔭·Sₚ) = maximalIdeal Rₚ`.

This reduces the `PerfectField` gate to the **single** residual stated in `relNorm_eq_under_of_localized`'s
hypothesis `hlocal` — the per-prime relative norm over a DVR base (see the residual note after
`Ideal.relNorm_eq_under_of_inertiaDeg_one`). -/

omit [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R] [IsDomain S]
  [IsIntegrallyClosed S] [IsDedekindDomain S] [Module.IsTorsionFree R S] in
/-- **The extension of `𝔭` to a localisation away from `𝔭.under` is `⊤`.**  If the maximal prime
`q` of `R` differs from `p = P.under R`, then `p ⊄ q`, so an element `a ∈ p ⊆ P` lands outside `q`,
hence becomes a unit in `Sₚ = Localization (algebraMapSubmonoid S q.primeCompl)`; since
`algebraMap R S a ∈ P`, this unit lies in `P.map`, forcing `P.map = ⊤`.  (Used for the `q ≠ p` case
of `relNorm_eq_under_of_localized`.) -/
theorem map_eq_top_of_under_ne (P : Ideal S) (q : Ideal R) [hq : q.IsMaximal] [P.IsMaximal]
    (hne : P.under R ≠ q) :
    P.map (algebraMap S (Localization (Algebra.algebraMapSubmonoid S q.primeCompl))) = ⊤ := by
  haveI : (P.under R).IsMaximal := Ideal.IsMaximal.under R P
  obtain ⟨a, hap, haq⟩ : ∃ a, a ∈ P.under R ∧ a ∉ q := by
    by_contra h; push Not at h
    exact hne (((Ideal.IsMaximal.under R P).eq_of_le hq.ne_top h))
  have haP : algebraMap R S a ∈ P := by rwa [← Ideal.mem_comap, ← Ideal.under_def]
  have hunit : IsUnit (algebraMap S (Localization (Algebra.algebraMapSubmonoid S q.primeCompl))
      (algebraMap R S a)) :=
    IsLocalization.map_units _ (⟨algebraMap R S a, ⟨a, haq, rfl⟩⟩ :
      Algebra.algebraMapSubmonoid S q.primeCompl)
  rw [Ideal.eq_top_iff_one]
  exact (P.map _).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem _ haP) hunit ▸ Submodule.mem_top

-- The semilocal `Sₚ` Dedekind/finite/torsion-free instance bundle over the DVR `Rₚ` pushes instance
-- synthesis (e.g. `IsDomain Sₚ`) past the default budget at statement elaboration.
set_option synthInstance.maxHeartbeats 400000 in
/-- **The relative norm localises (top + bottom) at a maximal prime `q` of `R`.**  Pushing
`relNorm R P` along `R → Rₚ := Localization.AtPrime q` equals the relative norm over `Rₚ` of the
extension of `P` to the semilocal `Sₚ = Localization (algebraMapSubmonoid S q.primeCompl)`.

This is a direct instance of mathlib's `Ideal.spanIntNorm_localization` (with `M = q.primeCompl`,
`Sₘ = Sₚ`), the same lemma powering `Ideal.relNorm_algebraMap` and `relNorm_eq_relNorm_localization`.
It is the genuine `relNorm`-vs-localisation compatibility needed to compute `relNorm R P` valuation
by valuation. -/
theorem relNorm_map_localization (P : Ideal S) (q : Ideal R) [q.IsMaximal] [NeZero q] :
    (Ideal.relNorm R P).map (algebraMap R (Localization.AtPrime q)) =
      Ideal.relNorm (Localization.AtPrime q)
        (P.map (algebraMap S (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))) := by
  rw [← Ideal.spanNorm_eq, ← Ideal.spanNorm_eq,
    ← Ideal.spanIntNorm_localization (R := R)
      (Sₘ := Localization (Algebra.algebraMapSubmonoid S q.primeCompl))
      P q.primeCompl q.primeCompl_le_nonZeroDivisors]

-- The semilocal `Sₚ` instance bundle (in `hlocal`'s type) needs synthesis room at elaboration.
set_option synthInstance.maxHeartbeats 400000 in
/-- **General-base `relNorm 𝔭 = 𝔭.under`, reduced to the semilocal per-prime formula** (no
`PerfectField`).  For a maximal prime `P` of `S` (with `p := P.under R`), the identity
`relNorm R P = p` holds **once** the per-prime relative norm over the DVR base is known:
`relNorm Rₚ (P·Sₚ) = maximalIdeal Rₚ`, where `Rₚ = Localization.AtPrime p` and
`Sₚ = Localization (algebraMapSubmonoid S p.primeCompl)` is the semilocal localisation of `S`.

Proof by `Ideal.eq_of_localization_maximal`: at every maximal `q` of `R`,
* `q ≠ p`: `p` maps to `⊤` (`IsLocalization.AtPrime.map_eq_top_of_not_le`) and `P·Sₚ = ⊤`
  (`map_eq_top_of_under_ne`), so both sides localise to `⊤` (`relNorm_top`);
* `q = p`: the localisation bridge `relNorm_map_localization` turns the goal into the hypothesis
  `hlocal`, and `p` maps to `maximalIdeal Rₚ` (`Localization.AtPrime.map_eq_maximalIdeal`).

The hypothesis `hlocal` is **exactly** the `PerfectField`-free residual (the per-prime relative norm
over a DVR base, the `f = 1` case `relNorm Rₚ 𝔮 = m^f = m`); everything else here is unconditional.
Combined with `Ideal.inertiaDeg_under_eq_one_of_algHom_of_residueField_finrank_one`, this is the
`relNorm`-vs-`comap` bridge the `Pic⁰` naturality (`hnat`) needs at a rational point. -/
theorem relNorm_eq_under_of_localized (P : Ideal S) [P.IsMaximal] (hP : P ≠ ⊥)
    (hlocal :
      letI := NeZero.mk (Ideal.under_ne_bot R hP)
      Ideal.relNorm (Localization.AtPrime (P.under R))
        (P.map (algebraMap S (Localization (Algebra.algebraMapSubmonoid S (P.under R).primeCompl))))
        = IsLocalRing.maximalIdeal (Localization.AtPrime (P.under R))) :
    Ideal.relNorm R P = P.under R := by
  haveI : (P.under R).IsMaximal := Ideal.IsMaximal.under R P
  haveI hpne : NeZero (P.under R) := ⟨Ideal.under_ne_bot R hP⟩
  have hnotfield : ¬ IsField R :=
    Ring.not_isField_of_ne_of_ne (Ideal.under_ne_bot R hP) (Ideal.IsMaximal.ne_top inferInstance)
  refine Ideal.eq_of_localization_maximal (fun q hq ↦ ?_)
  by_cases hqp : P.under R = q
  · subst hqp
    rw [relNorm_map_localization P (P.under R), hlocal,
      Localization.AtPrime.map_eq_maximalIdeal]
  · haveI : NeZero q := ⟨Ring.ne_bot_of_isMaximal_of_not_isField hq hnotfield⟩
    rw [relNorm_map_localization P q, map_eq_top_of_under_ne P q hqp, Ideal.relNorm_top,
      IsLocalization.AtPrime.map_eq_top_of_not_le _ (fun hle ↦ hqp
        ((Ideal.IsMaximal.under R P).eq_of_le hq.ne_top hle))]

/-! #### The per-prime relative norm over a DVR base — the `PerfectField`-free residual, **CLOSED**

The single remaining input of `relNorm_eq_under_of_localized` — the per-prime relative norm
`relNorm Rₚ 𝔮 = maximalIdeal Rₚ` over a **DVR** base `Rₚ` at residue degree one — is discharged here,
**without `PerfectField`**, via the **module-length** route (no residue *field* structure on the base,
so no `Field (Rₚ ⧸ m)` instance diamond).

The engine is the `Rₚ`-module-length identity over a **PID** base (`Rₚ` is a DVR, hence a PID):
for a nonzero principal `Q = (π)` of a free-finite `Rₚ`-algebra `Sₚ`,

  `length_{Rₚ}(Sₚ ⧸ Q) = length_{Rₚ}(Rₚ ⧸ relNorm Rₚ Q)`        (`relNorm_length_eq_span`),

proved by Smith normal form (`Ideal.quotientEquivPiSpan` is `Rₚ`-linear) + additivity of the order of
vanishing (`Ring.ord_mul`, `Ideal.relNorm_singleton`, `Algebra.intNorm_eq_norm`,
`associated_norm_prod_smith`).  When `f = inertiaDeg = 1`, `Sₚ ⧸ Q` is a **simple** `Rₚ`-module
(`isSimpleModule_quot_of_inertiaDeg_one`: the residue algebra map `Rₚ → Sₚ ⧸ Q` is onto, so
`Sₚ ⧸ Q ≃ₗ[Rₚ] Rₚ ⧸ m`), hence `length = 1`; the identity then forces `Rₚ ⧸ relNorm Rₚ Q` to be simple,
i.e. `relNorm Rₚ Q` maximal, i.e. `= m` (`IsLocalRing.eq_maximalIdeal`).  **No Galois, no
`PerfectField`.** -/

/-- **Additivity of the order of vanishing over a finite product** (`Ring.ord_mul`, iterated). For
nonzero `cᵢ` in a commutative domain, `ord (∏ cᵢ) = ∑ ord cᵢ`. -/
theorem Ring.ord_finset_prod {A : Type*} [CommRing A] [IsDomain A]
    {ι : Type*} (s : Finset ι) (c : ι → A) (hc : ∀ i ∈ s, c i ≠ 0) :
    Ring.ord A (∏ i ∈ s, c i) = ∑ i ∈ s, Ring.ord A (c i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Ring.ord_mul,
      ih (fun i hi ↦ hc i (Finset.mem_insert_of_mem hi))]
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi ↦ hc i (Finset.mem_insert_of_mem hi))

/-- **Norm–length identity over a PID base.** For a free-finite algebra `Sₚ` over a PID `Rₚ`
(integrally closed domains), and a nonzero element `π`, the `Rₚ`-module length of `Sₚ ⧸ (π)` equals
the `Rₚ`-module length of `Rₚ ⧸ relNorm Rₚ (π)`.

Proof: `relNorm Rₚ (π) = (Algebra.norm Rₚ π)` (`relNorm_singleton`, `intNorm_eq_norm`), whose order
of vanishing is `∑ᵢ length(Rₚ ⧸ (cᵢ))` for the Smith coefficients `cᵢ`
(`associated_norm_prod_smith`, `Ring.ord_finset_prod`, `Ring.ord = length(·⧸·)`); the same sum is
`length(Sₚ ⧸ (π))` by the `Rₚ`-linear `Ideal.quotientEquivPiSpan` + `length_pi_of_fintype`. -/
theorem relNorm_length_eq_span
    {Rp Sp : Type*}
    [CommRing Rp] [IsDomain Rp] [IsPrincipalIdealRing Rp] [IsIntegrallyClosed Rp]
    [CommRing Sp] [IsDomain Sp] [IsIntegrallyClosed Sp] [IsDedekindDomain Sp]
    [Algebra Rp Sp] [Module.Finite Rp Sp] [Module.IsTorsionFree Rp Sp]
    (π : Sp) (hπ0 : π ≠ 0) :
    Module.length Rp (Rp ⧸ Ideal.relNorm Rp (Ideal.span {π})) =
      Module.length Rp (Sp ⧸ (Ideal.span {π} : Ideal Sp)) := by
  classical
  have hQ : (Ideal.span {π} : Ideal Sp) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hπ0
  set b := Module.Free.chooseBasis Rp Sp with hb
  set c := fun i ↦ (Ideal.span {π} : Ideal Sp).smithCoeffs b hQ i with hc
  have hc0 : ∀ i, c i ≠ 0 := fun i ↦ (Ideal.span {π}).smithCoeffs_ne_zero b hQ i
  have hrelNorm : Ideal.relNorm Rp (Ideal.span {π}) = Ideal.span {Algebra.norm Rp π} := by
    rw [Ideal.relNorm_singleton, Algebra.intNorm_eq_norm]
  have hassoc : Associated (Algebra.norm Rp π) (∏ i, c i) := by
    have := associated_norm_prod_smith (R := Rp) (S := Sp) b hπ0
    convert this using 2
  have hord_relNorm : Ring.ord Rp (Algebra.norm Rp π) =
      Module.length Rp (Rp ⧸ Ideal.relNorm Rp (Ideal.span {π})) := by rw [Ring.ord, hrelNorm]
  have hord_eq : Ring.ord Rp (Algebra.norm Rp π) = Ring.ord Rp (∏ i, c i) := by
    rw [Ring.ord, Ring.ord, Ideal.span_singleton_eq_span_singleton.mpr hassoc]
  have hord_prod : Ring.ord Rp (∏ i, c i) = ∑ i, Module.length Rp (Rp ⧸ Ideal.span {c i}) := by
    rw [Ring.ord_finset_prod Finset.univ c (fun i _ ↦ hc0 i)]; rfl
  have hlen_smith : Module.length Rp (Sp ⧸ (Ideal.span {π} : Ideal Sp)) =
      ∑ i, Module.length Rp (Rp ⧸ Ideal.span {c i}) := by
    rw [(Ideal.quotientEquivPiSpan (Ideal.span {π}) b hQ).length_eq, Module.length_pi_of_fintype]
  rw [← hord_relNorm, hord_eq, hord_prod, hlen_smith]

set_option maxHeartbeats 800000 in
-- The explicit residue-field algebra structure (built on the `Ideal.Quotient.field`-derived semiring
-- via `algebraQuotientOfLEComap`) keeps the surjectivity/`finrank` bookkeeping in elaboration budget
-- *without* the `algebraOfLiesOver` instance-diamond (which carries free metavariables).
/-- **`Sₚ ⧸ Q` is a simple `Rₚ`-module at residue degree one** (the diamond-free `f = 1` input). For
a maximal ideal `Q` of `Sₚ` lying over a maximal `m` of `Rₚ` with `inertiaDeg m Q = 1`, the residue
algebra map `Rₚ → Sₚ ⧸ Q` is **surjective** with kernel `m` (the residue extension is trivial), so
`Sₚ ⧸ Q ≃ₗ[Rₚ] Rₚ ⧸ m`, a simple `Rₚ`-module.

Diamond-free: the residue `Field (Rₚ ⧸ m)` and the residue algebra `Algebra (Rₚ ⧸ m) (Sₚ ⧸ Q)` are
introduced together by `algebraQuotientOfLEComap` on the **same** field-derived semiring, so the
`FiniteDimensional`/`finrank` synthesis never disagrees with `inertiaDeg`'s
`Module (Rₚ ⧸ m) (Sₚ ⧸ Q)`. -/
theorem isSimpleModule_quot_of_inertiaDeg_one
    {Rp Sp : Type*} [CommRing Rp] [CommRing Sp] [Algebra Rp Sp]
    (Q : Ideal Sp) [hQ : Q.IsMaximal] (m : Ideal Rp) [hm : m.IsMaximal]
    [hlo : Q.LiesOver m] (hf : Ideal.inertiaDeg m Q = 1) :
    IsSimpleModule Rp (Sp ⧸ Q) := by
  letI : Field (Rp ⧸ m) := Ideal.Quotient.field m
  letI alg : Algebra (Rp ⧸ m) (Sp ⧸ Q) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq (Q.over_def m))
  haveI hst : IsScalarTower Rp (Rp ⧸ m) (Sp ⧸ Q) := IsScalarTower.of_algebraMap_eq' rfl
  have hfr : Module.finrank (Rp ⧸ m) (Sp ⧸ Q) = 1 := by
    rw [← Ideal.inertiaDeg_algebraMap m Q]; exact hf
  haveI : Nontrivial (Sp ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr hQ.ne_top
  haveI : FiniteDimensional (Rp ⧸ m) (Sp ⧸ Q) := Module.finite_of_finrank_eq_succ hfr
  have hsurj' : Function.Surjective (algebraMap (Rp ⧸ m) (Sp ⧸ Q)) := by
    have hinj : Function.Injective (Algebra.linearMap (Rp ⧸ m) (Sp ⧸ Q)) :=
      (algebraMap (Rp ⧸ m) (Sp ⧸ Q)).injective
    have hrank : Module.finrank (Rp ⧸ m) (Rp ⧸ m) = Module.finrank (Rp ⧸ m) (Sp ⧸ Q) := by
      rw [Module.finrank_self, hfr]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  have hsurjRp : Function.Surjective (Algebra.linearMap Rp (Sp ⧸ Q)) := by
    intro w
    obtain ⟨cc, hcc⟩ := hsurj' w
    obtain ⟨c0, rfl⟩ := Ideal.Quotient.mk_surjective cc
    refine ⟨c0, ?_⟩
    change algebraMap Rp (Sp ⧸ Q) c0 = w
    rw [IsScalarTower.algebraMap_apply Rp (Rp ⧸ m) (Sp ⧸ Q) c0, ← hcc]; rfl
  have hker : LinearMap.ker (Algebra.linearMap Rp (Sp ⧸ Q)) = m := by
    change RingHom.ker (algebraMap Rp (Sp ⧸ Q)) = m
    rw [IsScalarTower.algebraMap_eq Rp Sp (Sp ⧸ Q), ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact (Ideal.LiesOver.over (p := m) (P := Q)).symm
  rw [isSimpleModule_iff_quot_maximal]
  exact ⟨m, hm, ⟨(LinearMap.quotKerEquivOfSurjective _ hsurjRp).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)⟩⟩

set_option maxHeartbeats 800000 in
-- The module-length chain over the DVR base (Smith + `Ring.ord` additivity + simplicity) needs room.
/-- **The per-prime relative norm over a DVR base at residue degree one** (the `PerfectField`-free
residual, **CLOSED**).  For a DVR `Rₚ` (a local PID), a Dedekind PID `Sₚ` free-finite torsion-free
over `Rₚ`, and a nonzero maximal ideal `Q` of `Sₚ` lying over `m = maximalIdeal Rₚ` with
`inertiaDeg m Q = 1`, the relative norm `relNorm Rₚ Q = m`.

Proof (module-length, **no** residue-field instance, **no** Galois/`PerfectField`):
`Sₚ ⧸ Q` is `Rₚ`-simple (`isSimpleModule_quot_of_inertiaDeg_one`), so `length_{Rₚ}(Sₚ ⧸ Q) = 1`; the
norm–length identity `relNorm_length_eq_span` transports this to
`length_{Rₚ}(Rₚ ⧸ relNorm Rₚ Q) = 1`,
making `Rₚ ⧸ relNorm Rₚ Q` simple, i.e. `relNorm Rₚ Q` maximal, hence `= m`
(`IsLocalRing.eq_maximalIdeal`). -/
theorem relNorm_eq_maximalIdeal_of_inertiaDeg_one
    {Rp Sp : Type*}
    [CommRing Rp] [IsDomain Rp] [IsPrincipalIdealRing Rp] [IsIntegrallyClosed Rp] [IsLocalRing Rp]
    [CommRing Sp] [IsDomain Sp] [IsIntegrallyClosed Sp] [IsDedekindDomain Sp]
    [IsPrincipalIdealRing Sp]
    [Algebra Rp Sp] [Module.Finite Rp Sp] [Module.IsTorsionFree Rp Sp]
    (Q : Ideal Sp) [hQ : Q.IsMaximal] (hQ0 : Q ≠ ⊥)
    [hlo : Q.LiesOver (IsLocalRing.maximalIdeal Rp)]
    (hf : Ideal.inertiaDeg (IsLocalRing.maximalIdeal Rp) Q = 1) :
    Ideal.relNorm Rp Q = IsLocalRing.maximalIdeal Rp := by
  set m := IsLocalRing.maximalIdeal Rp with hm
  haveI : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal Rp
  haveI hsimp : IsSimpleModule Rp (Sp ⧸ Q) := isSimpleModule_quot_of_inertiaDeg_one Q m hf
  have hlen1 : Module.length Rp (Sp ⧸ Q) = 1 := Module.length_eq_one Rp (Sp ⧸ Q)
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal Q).principal
  have hπ0 : π ≠ 0 := by rintro rfl; apply hQ0; rw [hπ]; simp
  have hQspan : Q = Ideal.span {π} := by rw [hπ, Ideal.submodule_span_eq]
  have hlen_relNorm : Module.length Rp (Rp ⧸ Ideal.relNorm Rp Q) = 1 := by
    rw [hQspan, relNorm_length_eq_span (Rp := Rp) π hπ0, ← hQspan, hlen1]
  have hsimp2 : IsSimpleModule Rp (Rp ⧸ Ideal.relNorm Rp Q) :=
    Module.length_eq_one_iff.mp hlen_relNorm
  have hmax : (Ideal.relNorm Rp Q).IsMaximal := by
    rw [Ideal.isMaximal_def, ← isSimpleModule_iff_isCoatom]; exact hsimp2
  exact IsLocalRing.eq_maximalIdeal hmax

set_option synthInstance.maxHeartbeats 400000 in
-- The abstract `Rₚ`/`Sₚ` localisation instance bundle (in the binders) needs synthesis room.
omit [IsIntegrallyClosed R] [IsDedekindDomain R] [IsDomain S] [IsIntegrallyClosed S]
  [IsDedekindDomain S] [Module.Finite R S] [Module.IsTorsionFree R S] in
/-- **The per-prime relative norm at residue degree one, general semilocal `Rₚ`/`Sₚ`.**  The
hypothesis `hlocal` of `relNorm_eq_under_of_localized`, stated over abstract localisation data
`Rₚ`/`Sₚ` (so the expensive concrete-`Localization` instances are deferred): for a maximal `P` of
`S` over a maximal `p` of `R` with `inertiaDeg p P = 1`, `relNorm Rₚ (P·Sₚ) = maximalIdeal Rₚ`.

The prime/maximal/`LiesOver`/`inertiaDeg`-transport facts for `P·Sₚ` come from the
`IsLocalization.AtPrime` extension API (`isPrime_map_of_liesOver`, `liesOver_map_of_liesOver`,
`inertiaDeg_map_eq_inertiaDeg`); the per-prime norm itself is
`relNorm_eq_maximalIdeal_of_inertiaDeg_one`. -/
theorem relNorm_map_eq_maximalIdeal_general
    (p : Ideal R) [hp : p.IsMaximal] (hp0 : p ≠ ⊥)
    (Rp : Type*) [CommRing Rp] [IsDomain Rp] [IsIntegrallyClosed Rp] [IsDedekindDomain Rp]
      [IsPrincipalIdealRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
      [Module.IsTorsionFree R Rp]
    (Sp : Type*) [CommRing Sp] [IsDomain Sp] [IsIntegrallyClosed Sp] [IsDedekindDomain Sp]
      [IsPrincipalIdealRing Sp] [Algebra S Sp]
      [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sp]
      [Algebra Rp Sp] [Module.Finite Rp Sp] [Module.IsTorsionFree Rp Sp]
      [Algebra R Sp] [IsScalarTower R S Sp] [IsScalarTower R Rp Sp]
    (P : Ideal S) [hPmax : P.IsMaximal] [hPp : P.LiesOver p]
    (hf : Ideal.inertiaDeg p P = 1) :
    Ideal.relNorm Rp (P.map (algebraMap S Sp)) = IsLocalRing.maximalIdeal Rp := by
  haveI hQprime : (P.map (algebraMap S Sp)).IsPrime :=
    IsLocalization.AtPrime.isPrime_map_of_liesOver S p Sp P
  haveI hQlo : (P.map (algebraMap S Sp)).LiesOver (IsLocalRing.maximalIdeal Rp) :=
    IsLocalization.AtPrime.liesOver_map_of_liesOver p Rp Sp P
  have hm0 : IsLocalRing.maximalIdeal Rp ≠ ⊥ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp]
    exact Ideal.map_ne_bot_of_ne_bot hp0
  have hQ0 : (P.map (algebraMap S Sp)) ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hm0 _
  haveI hQmax : (P.map (algebraMap S Sp)).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hQ0 hQprime
  have hfQ : Ideal.inertiaDeg (IsLocalRing.maximalIdeal Rp) (P.map (algebraMap S Sp)) = 1 := by
    rw [IsLocalization.AtPrime.inertiaDeg_map_eq_inertiaDeg p Rp Sp P]; exact hf
  exact relNorm_eq_maximalIdeal_of_inertiaDeg_one (P.map (algebraMap S Sp)) hQ0 hfQ

set_option synthInstance.maxHeartbeats 1000000 in
-- The concrete semilocal `Sₚ` / DVR `Rₚ` localisation instance bundle is expensive to synthesise.
set_option maxHeartbeats 1600000 in
/-- **`relNorm 𝔭 = comap 𝔭` for a maximal prime of residue degree one** (Silverman III.4.10(a),
`f = 1`; ideal form). For a maximal ideal `P` of `S` with `inertiaDeg (P.under R) P = 1`, the
relative norm `Ideal.relNorm R P` equals the contraction `P.under R = comap (algebraMap R S) P`.

This is reduced (no `PerfectField`) to the per-prime DVR-base norm via the global→semilocal
`relNorm_eq_under_of_localized`; see the body and `relNorm_map_eq_maximalIdeal_general`.

**Unconditional — no `PerfectField`.**  Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal`
(`relNorm 𝔭 = 𝔭.under^f`) is gated on `[PerfectField (FractionRing R)]` (its proof reduces to the
**Galois** case), which fails for a function field over a finite base.  That hypothesis is *not*
mathematically necessary at `f = 1` (standard `e · f` theory, Silverman III.4.10), and is now
removed: the global→semilocal reduction `relNorm_eq_under_of_localized` reduces
`relNorm R P = P.under R` to the **single** semilocal per-prime input

  `relNorm Rₚ (P·Sₚ) = maximalIdeal Rₚ`  (`Rₚ = Localization.AtPrime p`, `Sₚ = semilocal loc. S`),

which `relNorm_map_eq_maximalIdeal_general` discharges via the **module-length** route over the DVR
base (`relNorm_eq_maximalIdeal_of_inertiaDeg_one` ← `relNorm_length_eq_span` +
`isSimpleModule_quot_of_inertiaDeg_one`) — no Galois, no `PerfectField`, and **no** `Field (Rₚ ⧸ m)`
instance diamond (the length is taken over the DVR `Rₚ`, never the residue field).  The inertia
degree transports across the localisation via `IsLocalization.AtPrime.inertiaDeg_map_eq_inertiaDeg`.

(The shipped local-base specialisation
`Ideal.relNorm_maximalIdeal_eq_under_of_inertiaDeg_one_of_isLocalRing` is now subsumed for the
general base; it is retained as a lighter-weight `IsLocalRing` form.) -/
theorem Ideal.relNorm_eq_under_of_inertiaDeg_one
    {P : Ideal S} [hPmax : P.IsMaximal] (hP : P ≠ ⊥)
    (hf : Ideal.inertiaDeg (P.under R) P = 1) :
    Ideal.relNorm R P = P.under R := by
  letI hnz := NeZero.mk (Ideal.under_ne_bot R hP)
  haveI hpmax : (P.under R).IsMaximal := Ideal.IsMaximal.under R P
  haveI : P.LiesOver (P.under R) := Ideal.over_under P
  -- Pre-establish the heavy semilocal `Sₚ` / DVR `Rₚ` instances so the discharge stays in budget.
  haveI iDed : IsDedekindDomain
      (Localization (Algebra.algebraMapSubmonoid S (P.under R).primeCompl)) := inferInstance
  haveI iPID : IsPrincipalIdealRing
      (Localization (Algebra.algebraMapSubmonoid S (P.under R).primeCompl)) := inferInstance
  haveI iFin : Module.Finite (Localization.AtPrime (P.under R))
      (Localization (Algebra.algebraMapSubmonoid S (P.under R).primeCompl)) := inferInstance
  haveI iTF : Module.IsTorsionFree (Localization.AtPrime (P.under R))
      (Localization (Algebra.algebraMapSubmonoid S (P.under R).primeCompl)) := inferInstance
  haveI iIC : IsIntegrallyClosed
      (Localization (Algebra.algebraMapSubmonoid S (P.under R).primeCompl)) := inferInstance
  haveI iST2 : IsScalarTower R (Localization.AtPrime (P.under R))
      (Localization (Algebra.algebraMapSubmonoid S (P.under R).primeCompl)) := inferInstance
  haveI iST3 : IsScalarTower R S
      (Localization (Algebra.algebraMapSubmonoid S (P.under R).primeCompl)) := inferInstance
  haveI iTFr : Module.IsTorsionFree R (Localization.AtPrime (P.under R)) := inferInstance
  refine relNorm_eq_under_of_localized P hP ?_
  exact relNorm_map_eq_maximalIdeal_general (P.under R) (Ideal.under_ne_bot R hP)
    (Localization.AtPrime (P.under R))
    (Localization (Algebra.algebraMapSubmonoid S (P.under R).primeCompl)) P hf

/-- **`relNorm 𝔭 = comap 𝔭` for a maximal prime of residue degree one** (Silverman III.4.10(a),
`f = 1`; nonZeroDivisors / `relNorm0` form). The `(Ideal R)⁰`-packaged value `relNorm0 P` equals the
contraction `comap (algebraMap R S) P` (which is nonzero by `Ideal.under_ne_bot`), as elements of
`(Ideal R)⁰`. -/
theorem relNorm0_eq_comap_of_inertiaDeg_one
    (P : (Ideal S)⁰) [hPmax : (P : Ideal S).IsMaximal]
    (hf : Ideal.inertiaDeg ((P : Ideal S).under R) (P : Ideal S) = 1) :
    (relNorm0 (R := R) (S := S) P : Ideal R) =
      Ideal.comap (algebraMap R S) (P : Ideal S) :=
  Ideal.relNorm_eq_under_of_inertiaDeg_one (R := R) (S := S)
    (mem_nonZeroDivisors_iff_ne_zero.mp P.2) hf

/-- **`class(relNorm 𝔭) = class(comap 𝔭)` for a maximal prime of residue degree one**
(Silverman III.4.10(a), `f = 1`; class-group form). The `ClassGroup.mk0` class of `relNorm0 P` is
the class of the contraction `comap (algebraMap R S) P`.

This is the residue-degree-`1` content that bridges the divisor pushforward `φ_* = relNorm`
(`classNorm`) with the set-theoretic point image `comap` (the shipped `toClass_toPointMap`), pinning
the `Pic⁰` naturality `hnat` at a rational point.  The `comap`-nonzero membership proof is supplied
via `Ideal.under_ne_bot`. -/
theorem ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one
    (P : (Ideal S)⁰) [hPmax : (P : Ideal S).IsMaximal]
    (hf : Ideal.inertiaDeg ((P : Ideal S).under R) (P : Ideal S) = 1)
    (hcomap : Ideal.comap (algebraMap R S) (P : Ideal S) ∈ (Ideal R)⁰) :
    ClassGroup.mk0 (relNorm0 (R := R) (S := S) P) =
      ClassGroup.mk0 (⟨Ideal.comap (algebraMap R S) (P : Ideal S), hcomap⟩ : (Ideal R)⁰) :=
  congrArg ClassGroup.mk0 (Subtype.ext (relNorm0_eq_comap_of_inertiaDeg_one (R := R) (S := S) P hf))

/-! ### `inertiaDeg = 1` at a residue-degree-one prime, for an `F`-algebra self-map `R →ₐ[F] R`

The residue/inertia degree `f = inertiaDeg (M.under R) M = finrank (R ⧸ M.under R) (R ⧸ M)` is `1`
whenever the residue field `R ⧸ M` is *one-dimensional over the ground field `F`* (an `F`-rational
point: `R ⧸ M ≅ F`).  This is Silverman III.4.10(a) `f = 1`: at a rational point the inseparability
of an `F`-algebra self-map `g : R →ₐ[F] R` (e.g. Frobenius) lives entirely in the **ramification**
`e`, never in `f`.

The proof is **diamond-free** (it does *not* invoke `finrank_mul_finrank`, which is what blocks the
`Module.Free` "Piece 9" route in `Curves/GenericFiber.lean`): it bounds
`finrank (R ⧸ M.under R) (R ⧸ M) ≤ 1` directly by surjectivity of the residue-field algebra map.
That surjectivity holds because `g` is an `F`-algebra hom — so it fixes the image of `F`, and
`algebraMap F (R ⧸ M)` is already surjective when `finrank F (R ⧸ M) = 1`; hence every residue class
is hit by a *constant* `algebraMap F (R ⧸ M.under R) c`.  Positivity (`finrank ≥ 1`) is
`Module.finrank_pos` (the residue extension is finite + nontrivial).

`g` need only be *module-finite over itself through `g`* (`hfin`) for `M.under R` to be maximal
(going-up / `Algebra.IsIntegral.of_finite`); this is exactly the `Module.Finite` witness an
`Isogeny.CoordHom` already carries. -/

-- The twisted self-algebra `R →[g] R` pushes instance synthesis past the default budget.
set_option synthInstance.maxHeartbeats 400000 in
-- The residue-field `finrank` bookkeeping (surjectivity bound + tower) needs more elaboration room.
set_option maxHeartbeats 1600000 in
/-- **`inertiaDeg = 1` at a rational point, for an `F`-algebra self-map** (Silverman III.4.10(a),
`f = 1`). For an `F`-algebra `R`, an `F`-algebra hom `g : R →ₐ[F] R` that is module-finite over
itself through `g`, and a maximal ideal `M` whose residue field is one-dimensional over `F`
(`finrank F (R ⧸ M) = 1`, the `F`-rational condition), the inertia degree of `M.under R` (the
contraction `comap g M`) under `M` is `1`.

Diamond-free (no `finrank_mul_finrank`): see the section note.  This is the missing `f = 1` input
that, via `Ideal.relNorm_eq_under_of_inertiaDeg_one`, collapses `relNorm 𝔪 = comap 𝔪` at rational
points — the residue-degree content of the `Pic⁰` naturality `hnat`. -/
theorem Ideal.inertiaDeg_under_eq_one_of_algHom_of_residueField_finrank_one
    {F : Type*} [Field F] {R : Type*} [CommRing R] [Algebra F R] (g : R →ₐ[F] R)
    (hfin : @Module.Finite R R _ _ g.toRingHom.toAlgebra.toModule)
    (M : Ideal R) [hM : M.IsMaximal]
    (hres : Module.finrank F (R ⧸ M) = 1) :
    letI : Algebra R R := g.toRingHom.toAlgebra
    Ideal.inertiaDeg (M.under R) M = 1 := by
  letI inst : Algebra R R := g.toRingHom.toAlgebra
  haveI instFin : @Module.Finite R R _ _ inst.toModule := hfin
  haveI : @Algebra.IsIntegral R R _ _ inst :=
    @Algebra.IsIntegral.of_finite R R _ _ inst instFin
  -- The twisted self-algebra is a scalar tower over `F`: `g` fixes the image of `F`.
  haveI hst : @IsScalarTower F R R _ inst.toSMul _ :=
    @IsScalarTower.of_algebraMap_eq F R R _ _ _ _ inst _ fun c ↦ by
    change algebraMap F R c = g.toRingHom (algebraMap F R c)
    rw [show g.toRingHom (algebraMap F R c) = g (algebraMap F R c) from rfl, AlgHom.commutes]
  haveI : M.LiesOver (M.under R) := Ideal.over_under M
  haveI hmax : (M.under R).IsMaximal := Ideal.IsMaximal.under R M
  haveI : Field (R ⧸ M.under R) := Ideal.Quotient.field _
  rw [Ideal.inertiaDeg_algebraMap]
  haveI : Nontrivial (R ⧸ M) := Ideal.Quotient.nontrivial_iff.mpr hM.ne_top
  haveI : FiniteDimensional F (R ⧸ M) := Module.finite_of_finrank_eq_succ hres
  -- `algebraMap F (R ⧸ M)` is surjective: injective `F`-linear map between equal (= 1) finrank.
  have hFsurj : Function.Surjective (algebraMap F (R ⧸ M)) := by
    have hinj : Function.Injective (Algebra.linearMap F (R ⧸ M)) :=
      (algebraMap F (R ⧸ M)).injective
    have hrank : Module.finrank F F = Module.finrank F (R ⧸ M) := by
      rw [Module.finrank_self, hres]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  -- Hence the residue-field algebra map `R ⧸ M.under R → R ⧸ M` is surjective: hit each class by a
  -- constant `algebraMap F (R ⧸ M.under R) c` (scalar tower `F → R ⧸ M.under R → R ⧸ M`).
  have hsurj : Function.Surjective (algebraMap (R ⧸ M.under R) (R ⧸ M)) := by
    intro w
    obtain ⟨c₀, hc₀⟩ := hFsurj w
    exact ⟨algebraMap F (R ⧸ M.under R) c₀, by
      rw [← IsScalarTower.algebraMap_apply F (R ⧸ M.under R) (R ⧸ M), hc₀]⟩
  haveI hfinMod : Module.Finite (R ⧸ M.under R) (R ⧸ M) :=
    Module.Finite.of_surjective (Algebra.linearMap (R ⧸ M.under R) (R ⧸ M))
      (by intro w; obtain ⟨c, hc⟩ := hsurj w; exact ⟨c, hc⟩)
  have h_le : Module.finrank (R ⧸ M.under R) (R ⧸ M) ≤ 1 :=
    finrank_le_one 1 fun w ↦ by
      obtain ⟨c, hc⟩ := hsurj w
      exact ⟨c, by rw [Algebra.smul_def, hc]; exact mul_one w⟩
  have h_ge : 1 ≤ Module.finrank (R ⧸ M.under R) (R ⧸ M) := Module.finrank_pos
  exact le_antisymm h_le h_ge

/-- `map_one` sanity check: the relative norm of the trivial class is trivial. -/
theorem ClassGroup.relNorm_one : ClassGroup.relNorm (R := R) (S := S) 1 = 1 :=
  map_one _

/-- `map_mul` sanity check: the relative norm is multiplicative. -/
theorem ClassGroup.relNorm_mul (a b : ClassGroup S) :
    ClassGroup.relNorm (R := R) (a * b) =
      ClassGroup.relNorm (R := R) a * ClassGroup.relNorm (R := R) b :=
  map_mul _ a b

/-!
## The class-group extension (pullback) map and the dual relation

We now build the *extension* direction `ClassGroup R →* ClassGroup S`, induced by
`Ideal.map (algebraMap R S)` (extend an ideal of `R` to `S`), by exactly the same descent
technique used for `relNorm`.  Composing the relative norm with the extension recovers raising to
the `n`-th power, where `n = [Frac S : Frac R] = Module.finrank R S`
(`ClassGroup.relNorm_comp_map`).  This is the class-group shadow of the dual-isogeny relation
`α̂ ∘ α = [deg α]`.

The whole arithmetic core
`Ideal.relNorm R (Ideal.map (algebraMap R S) I) = I ^ n`
is already available in mathlib as `Ideal.relNorm_algebraMap` (proved by localising at maximal
ideals and reducing to `Algebra.norm_algebraMap`); in particular it needs **no**
separability/Galois/`PerfectField` hypothesis, so the ramification–inertia route is not needed
here.
-/

/-- The extension of an integral ideal, packaged as a homomorphism of `nonZeroDivisors` monoids
`(Ideal R)⁰ →* (Ideal S)⁰`, using that `Ideal.map (algebraMap R S)` sends nonzero ideals to nonzero
ideals (`Ideal.map_eq_bot_iff_of_injective`, since `algebraMap R S` is injective by
`FaithfulSMul.algebraMap_injective`). -/
noncomputable def map0 : (Ideal R)⁰ →* (Ideal S)⁰ where
  toFun I := ⟨Ideal.map (algebraMap R S) (I : Ideal R), by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, ← bot_eq_zero,
      Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S), bot_eq_zero,
      ← ne_eq, ← mem_nonZeroDivisors_iff_ne_zero]
    exact I.2⟩
  map_one' := by
    ext
    simp [Ideal.one_eq_top, Ideal.map_top]
  map_mul' I J := by
    ext
    simp [Ideal.map_mul]

/-- The composite "extend then take the class", as a homomorphism `(Ideal R)⁰ →* ClassGroup S`. -/
noncomputable def mk0CompMap0 : (Ideal R)⁰ →* ClassGroup S :=
  (ClassGroup.mk0 (R := S)).comp map0

omit [IsIntegrallyClosed R] [IsDedekindDomain R] [IsIntegrallyClosed S] [Module.Finite R S] in
@[simp]
theorem mk0CompMap0_apply (I : (Ideal R)⁰) :
    mk0CompMap0 (S := S) I = ClassGroup.mk0 (map0 I) := rfl

omit [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Module.Finite R S] in
/-- Well-definedness of the descent: if two integral ideals of `R` have the same class in
`ClassGroup R`, their extensions have the same class in `ClassGroup S`.

The proof reduces, via `ClassGroup.mk0_eq_mk0_iff`, to the fact that the extension of a principal
ideal is principal (`Ideal.map_span` together with `Set.image_singleton`): from
`span{x} * I = span{y} * J` (`x, y ≠ 0`) we obtain, by multiplicativity of `Ideal.map`,
`span{algebraMap x} * (map I) = span{algebraMap y} * (map J)` with `algebraMap x, algebraMap y ≠ 0`
by injectivity of `algebraMap R S`. -/
theorem mk0CompMap0_eq_of_mk0_eq {I J : (Ideal R)⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    mk0CompMap0 (S := S) I = mk0CompMap0 (S := S) J := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  simp only [mk0CompMap0_apply, ClassGroup.mk0_eq_mk0_iff]
  refine ⟨algebraMap R S x, algebraMap R S y,
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hx,
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hy, ?_⟩
  change Ideal.span {algebraMap R S x} * Ideal.map (algebraMap R S) (I : Ideal R) =
    Ideal.span {algebraMap R S y} * Ideal.map (algebraMap R S) (J : Ideal R)
  have key : ∀ a : R,
      Ideal.span {algebraMap R S a} = Ideal.map (algebraMap R S) (Ideal.span {a}) := fun a ↦ by
    rw [Ideal.map_span, Set.image_singleton]
  rw [key x, key y, ← Ideal.map_mul, ← Ideal.map_mul, hxy]

/-- The **class-group extension map**: the monoid homomorphism `ClassGroup R →* ClassGroup S`
induced by `Ideal.map (algebraMap R S)`.

Since `ClassGroup.mk0 : (Ideal R)⁰ →* ClassGroup R` is surjective, every class has an integral
representative; we send the class of `I` to the class of `Ideal.map (algebraMap R S) I`.  This is
well defined by `mk0CompMap0_eq_of_mk0_eq`. -/
noncomputable def ClassGroup.map : ClassGroup R →* ClassGroup S where
  toFun c := mk0CompMap0 (Function.surjInv ClassGroup.mk0_surjective c)
  map_one' := by
    rw [← map_one (mk0CompMap0 (R := R) (S := S))]
    apply mk0CompMap0_eq_of_mk0_eq
    rw [Function.surjInv_eq ClassGroup.mk0_surjective, map_one]
  map_mul' a b := by
    rw [← map_mul]
    apply mk0CompMap0_eq_of_mk0_eq
    rw [map_mul, Function.surjInv_eq ClassGroup.mk0_surjective,
      Function.surjInv_eq ClassGroup.mk0_surjective,
      Function.surjInv_eq ClassGroup.mk0_surjective]

omit [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Module.Finite R S] in
/-- The defining computation of `ClassGroup.map` on an integral representative: the extension of the
class of `I` is the class of `Ideal.map (algebraMap R S) I` (which lies in `(Ideal S)⁰` by
`Ideal.map_eq_bot_iff_of_injective`, here packaged as `map0 I`). -/
@[simp]
theorem ClassGroup.map_mk0 (I : (Ideal R)⁰) :
    ClassGroup.map (S := S) (ClassGroup.mk0 I) = ClassGroup.mk0 (map0 (S := S) I) := by
  refine (mk0CompMap0_eq_of_mk0_eq ?_).trans (mk0CompMap0_apply I)
  rw [Function.surjInv_eq ClassGroup.mk0_surjective]

omit [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Module.Finite R S] in
/-- `map_one` sanity check: the extension of the trivial class is trivial. -/
theorem ClassGroup.map_one : ClassGroup.map (R := R) (S := S) 1 = 1 :=
  _root_.map_one _

omit [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Module.Finite R S] in
/-- `map_mul` sanity check: the extension map is multiplicative. -/
theorem ClassGroup.map_mul (a b : ClassGroup R) :
    ClassGroup.map (S := S) (a * b) =
      ClassGroup.map (S := S) a * ClassGroup.map (S := S) b :=
  _root_.map_mul _ a b

/-- The **ideal-level arithmetic core** of the dual relation: the relative norm of the extension of
an integral ideal `I` of `R` is `I ^ n`, where `n = Module.finrank R S`.

This is `Ideal.relNorm_algebraMap` (whose native exponent is
`Module.finrank (FractionRing R) (FractionRing S)`), converted to `Module.finrank R S` via
`Algebra.IsAlgebraic.finrank_of_isFractionRing`.  The non-instance `FractionRing.liftAlgebra`
algebra on the fraction fields is supplied locally (the usual gotcha). -/
theorem Ideal.relNorm_map_algebraMap (I : Ideal R) :
    Ideal.relNorm R (Ideal.map (algebraMap R S) I) = I ^ Module.finrank R S := by
  letI : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  haveI : IsScalarTower R (FractionRing R) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  haveI : IsScalarTower R S (FractionRing S) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hrank : Module.finrank (FractionRing R) (FractionRing S) = Module.finrank R S :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing R (FractionRing R) S (FractionRing S)
  rw [Ideal.relNorm_algebraMap S I, hrank]

/-- **The target: the dual relation at the class-group level.**

The composite of the class-group extension map with the relative norm is raising to the `n`-th
power, where `n = Module.finrank R S = [Frac S : Frac R]`:
`relNorm (map c) = c ^ n` for every `c : ClassGroup R`.  This is the arithmetic core, on ideal
classes, of `α̂ ∘ α = [deg α]`.

The proof picks an integral representative `c = mk0 I` (`ClassGroup.mk0_surjective`), computes both
descents with `ClassGroup.map_mk0` and `ClassGroup.relNorm_mk0`, and reduces to the ideal-level
identity `Ideal.relNorm_map_algebraMap`.  Compatibility of `mk0` with `(· ^ n)` is `map_pow`. -/
theorem ClassGroup.relNorm_comp_map (c : ClassGroup R) :
    ClassGroup.relNorm (ClassGroup.map (S := S) c) = c ^ Module.finrank R S := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [ClassGroup.map_mk0, ClassGroup.relNorm_mk0, ← map_pow]
  refine congrArg ClassGroup.mk0 (Subtype.ext ?_)
  change Ideal.relNorm R (Ideal.map (algebraMap R S) (I : Ideal R))
    = (I : Ideal R) ^ Module.finrank R S
  exact Ideal.relNorm_map_algebraMap (S := S) (I : Ideal R)

/-- `ClassGroup.relNorm_comp_map`, stated as an equality of the composite monoid homomorphism
`ClassGroup R →* ClassGroup R` with the `n`-th power homomorphism. -/
theorem ClassGroup.relNorm_comp_map_eq :
    (ClassGroup.relNorm (R := R)).comp (ClassGroup.map (S := S)) =
      powMonoidHom (Module.finrank R S) := by
  refine MonoidHom.ext fun c ↦ ?_
  rw [MonoidHom.comp_apply, powMonoidHom_apply, ClassGroup.relNorm_comp_map]

end HasseWeil
