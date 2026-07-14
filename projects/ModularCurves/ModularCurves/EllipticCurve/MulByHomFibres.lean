import ModularCurves.EllipticCurve.MulByHomDegree
import HasseWeil.NTorsion.TorsionPowStructure
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Finite fibres of `[N]` — the BB-QF geometric leaf (QF-FIBFIN)

This file discharges the geometric content of the BB-QF box: **every topological fibre of
`[N] : E ⟶ E` is finite** (`N ≠ 0`), over an arbitrary base and in every characteristic.
Combined with the already-banked mathlib-criterion reduction
(`mulByHom_locallyQuasiFinite := LocallyQuasiFinite.of_finite_preimage_singleton`), this
eliminates BB-QF mathematically; the upstream `Torsion.lean` sorry then closes by relocating
this file's content below `Torsion` (a mechanical move boarded for the coordinator — no
statement changes).

## The wall-break (why this is possible today)

The 2026-07-14 adversarial decomposition classified the nonconstancy witness as gated on
T-B6 ("group-compatible scheme-fibre ↔ Weierstrass comparison, rooted in the sorried
`abelEnrichment_exists`"). That root cause is STALE: over a locally noetherian base the
**uniqueness** half of the enrichment is PROVEN (`abelEnrichment_unique_of_isLocallyNoetherian`,
T-W7.7·C4glue), and uniqueness is all a *pointed* comparison needs — GIT Cor 6.4
(`isMonHom_of_one_comp_eq'`, proven) makes ANY pointed morphism of group objects a monoid
homomorphism, and monoid homomorphisms intertwine `mulBy` (power-naturality, proved below).
So the field-fibre ↔ model comparison carrying scheme-`[N]` to model-`[N]` needs NO
existence box:

* the fibre curve is a record (`E.baseChange`), the model is a record
  (`modelEllipticCurve W` base-changed along the base identification);
* `localModel` supplies a **pointed** iso between their total spaces over the field;
* rigidity (GIT 6.4) upgrades it to a group-object hom; power-naturality conjugates `[N]`.

The fibre count then happens on the model, where everything is field-level and sorry-free:
the `zChart` coordinate-ring presentation (dimension ≤ 1 via Krull's PIT), Jacobson
closed-point theory, and HasseWeil's torsion cardinalities (`card_torsion_ellPow_nat`,
`ℓ ≠ char`, cross-project import) which force the image of `[N]` to be topologically
infinite, hence dense, hence the fibres proper closed subsets of an integral curve.

## De-confliction (v10.219)

Zero use of `mulByHom_finrank` / `endDeg` / any degree fact (KM's carve-out). The only
nonconstancy input is HasseWeil's prime-to-char torsion cardinality.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

/-! ### Power-naturality: monoid-object homomorphisms intertwine `mulBy`

For any `φ : A ⟶ G` between group objects in `Over S`: precomposition by `φ` is a monoid
homomorphism of hom-groups unconditionally (`MonObj.comp_mul`), and postcomposition is one
when `φ` is a `IsMonHom` (`IsMonHom.monoidHom`). Both send `𝟙` to `φ`, so evaluating the
two monoid homs on `(𝟙)^n` identifies `mulBy n ≫ φ = φ ≫ mulBy n`. -/

variable {S : Scheme.{u}}

/-- `[n]` is proper: it is an `S`-endomorphism of the proper `S`-scheme `E`
(cancellation along the separated `π`). KM 2.3.1 proof, first reduction ("Because `E`
is proper over `S`, any `S`-endomorphism of `E` is proper"). Relocated here (below
`GroupLaw`, above `Torsion`) so the BB-QF closure chain can consume it without cycling
through `Torsion`. -/
instance mulByHom_isProper (E : EllipticCurve S) (n : ℤ) : IsProper (E.mulByHom n) := by
  haveI h : IsProper (E.mulByHom n ≫ E.π) := by
    rw [E.mulByHom_π]
    exact E.proper
  exact IsProper.of_comp (E.mulByHom n) E.π

/-- **A monoid-object homomorphism between elliptic-curve records intertwines `mulBy`**:
`[n]_E ≫ φ = φ ≫ [n]_F` for every `n : ℤ`. Power-naturality: both sides are the `n`-th
power of `φ` in the hom-group `E.asOver ⟶ F.asOver` — the left via the postcomposition
monoid hom (`IsMonHom.monoidHom`, needs `[IsMonHom φ]`), the right via precomposition
(`GrpObj.comp_zpow`, unconditional). -/
theorem mulBy_comp_of_isMonHom (E F : EllipticCurve S) (φ : E.asOver ⟶ F.asOver)
    [IsMonHom φ] (n : ℤ) :
    E.mulBy n ≫ φ = φ ≫ F.mulBy n := by
  letI : Group (E.asOver ⟶ E.asOver) := Hom.group
  letI : Group (F.asOver ⟶ F.asOver) := Hom.group
  letI : CommGroup (E.asOver ⟶ F.asOver) := Hom.commGroup
  have hpost : E.mulBy n ≫ φ = (𝟙 E.asOver ≫ φ) ^ n := by
    show ((𝟙 E.asOver) ^ n) ≫ φ = (𝟙 E.asOver ≫ φ) ^ n
    have h := map_zpow (IsMonHom.monoidHom φ E.asOver) (𝟙 E.asOver) n
    simpa only [IsMonHom.monoidHom_apply] using h
  have hpre : φ ≫ F.mulBy n = (φ ≫ 𝟙 F.asOver) ^ n := by
    show φ ≫ (𝟙 F.asOver) ^ n = (φ ≫ 𝟙 F.asOver) ^ n
    rw [GrpObj.comp_zpow]
  rw [hpost, hpre, Category.id_comp, Category.comp_id]

/-- **Scheme-level power-naturality** (the `.left` of `mulBy_comp_of_isMonHom`): a pointed
monoid-object hom `φ` conjugates the scheme-level `[n]`, `[n]_E ≫ φ.left = φ.left ≫ [n]_F`.
`mulByHom n` is by definition `(mulBy n).left`, and `.left` is functorial on `Over S`. -/
theorem mulByHom_comp_left_of_isMonHom (E F : EllipticCurve S) (φ : E.asOver ⟶ F.asOver)
    [IsMonHom φ] (n : ℤ) :
    E.mulByHom n ≫ φ.left = φ.left ≫ F.mulByHom n := by
  have h := congrArg Over.Hom.left (mulBy_comp_of_isMonHom E F φ n)
  simp only [Over.comp_left] at h
  exact h

/-- **(BETA transport core)** Local quasi-finiteness of `[n]` transports across a pointed
monoid-object iso of elliptic-curve records: if `φ : E.asOver ≅ F.asOver` is `IsMonHom` and `[n]_F`
is locally quasi-finite, so is `[n]_E`. `φ.hom.left` is an iso, power-naturality conjugates
`[n]_E = φ.hom.left ≫ [n]_F ≫ (φ.hom.left)⁻¹`, and `LocallyQuasiFinite` is closed under composition
with isos. This is the record-level engine of the fibre transport (applied at each geometric fibre
`E_s ≅ modelEllipticCurve W_s`, whose model side is `ModelFibreCount.lean`). -/
theorem locallyQuasiFinite_mulByHom_of_isMonHom_iso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] (n : ℤ)
    [LocallyQuasiFinite (F.mulByHom n)] : LocallyQuasiFinite (E.mulByHom n) := by
  let ψ : E.E ≅ F.E := (Over.forget S).mapIso φ
  have hconj : E.mulByHom n = ψ.hom ≫ F.mulByHom n ≫ ψ.inv := by
    have h : E.mulByHom n ≫ ψ.hom = ψ.hom ≫ F.mulByHom n :=
      mulByHom_comp_left_of_isMonHom E F φ.hom n
    rw [← Category.assoc, ← h, Category.assoc, ψ.hom_inv_id, Category.comp_id]
  rw [hconj]
  infer_instance

end EllipticCurve

/-! ### Spectra of dimension-≤-1 domains: the curve-topology toolkit

Generic facts about `PrimeSpectrum R` for a domain `R` with `ringKrullDim R ≤ 1`:
nonzero primes are maximal, irreducible closed subsets are points or everything, and —
for Jacobson `R` (every finitely generated algebra over a field) — the spectrum is
infinite unless `R` is a field. -/

section CoordinateRingDim

open WeierstrassCurve Polynomial in
/-- **The affine coordinate ring of a Weierstrass curve has Krull dimension `≤ 1`.**
`CoordinateRing = K[X][Y]/(W.polynomial)` with `W.polynomial ≠ 0` in the two-dimensional
`K[X][Y]`: a nonzero prime of the quotient pulls back to a prime strictly containing the
nonzero `(W.polynomial)`, so a strict pair above it would give a chain of length three.
Every nonzero prime of the quotient is therefore maximal (`Ring.KrullDimLE.mk₁`-form). -/
theorem coordinateRing_krullDimLE_one {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] :
    Ring.KrullDimLE 1 W.toAffine.CoordinateRing := by
  rw [Ring.krullDimLE_iff]
  -- ambient dimension: `dim K[X][Y] = 2`
  have hamb : ringKrullDim (Polynomial (Polynomial K)) = 2 := by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing,
      Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    norm_num
  -- the comap along the quotient projection is a strictly monotone map of spectra
  have hsurj : Function.Surjective (AdjoinRoot.mk W.toAffine.polynomial) :=
    AdjoinRoot.mk_surjective
  have hstrict : StrictMono
      (PrimeSpectrum.comap (AdjoinRoot.mk W.toAffine.polynomial)) := by
    intro a b hab
    exact lt_of_le_of_ne (fun x hx => Ideal.mem_comap.mpr (hab.le (Ideal.mem_comap.mp hx)))
      fun h => hab.ne (PrimeSpectrum.comap_injective_of_surjective _ hsurj h)
  -- chains in the quotient lift to chains above `(W.polynomial)`, prepended by `⊥`
  have hlt : ringKrullDim W.toAffine.CoordinateRing < ((2 : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim, Order.krullDim_lt_coe_iff]
    intro l
    -- the head of the lifted chain contains the nonzero prime `(W.polynomial)`
    have hker : RingHom.ker (AdjoinRoot.mk W.toAffine.polynomial) ≤
        ((l.map _ hstrict).head).asIdeal := fun x hx => by
      have hx0 : (AdjoinRoot.mk W.toAffine.polynomial) x = 0 := RingHom.mem_ker.mp hx
      show x ∈ (PrimeSpectrum.comap (AdjoinRoot.mk W.toAffine.polynomial) l.head).asIdeal
      rw [PrimeSpectrum.comap_asIdeal]
      exact Ideal.mem_comap.mpr (by rw [hx0]; exact l.head.asIdeal.zero_mem)
    have hbotlt : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Polynomial (Polynomial K)))
        < (l.map _ hstrict).head := by
      refine lt_of_le_of_ne bot_le fun h => ?_
      have hfk : W.toAffine.polynomial ∈ RingHom.ker
          (AdjoinRoot.mk W.toAffine.polynomial) := by
        simp [RingHom.mem_ker, AdjoinRoot.mk_self]
      have h0 : W.toAffine.polynomial = 0 := by
        have hle := hker hfk
        rw [← h] at hle
        simpa using hle
      exact W.toAffine.polynomial_ne_zero h0
    -- the prepended chain violates `dim = 2`
    have hchain := Order.LTSeries.length_le_krullDim ((l.map _ hstrict).cons _ hbotlt)
    rw [← ringKrullDim, hamb] at hchain
    simp only [RelSeries.cons_length, RelSeries.map_length] at hchain
    have hle2 : ((l.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast hchain
    have hfin : l.length + 1 ≤ 2 := by exact_mod_cast hle2
    omega
  have h21 : ((2 : ℕ) : WithBot ℕ∞) = (1 : WithBot ℕ∞) + 1 := by norm_num
  rw [h21] at hlt
  exact ENat.WithBot.lt_add_one_iff.mp hlt

end CoordinateRingDim

end ModularCurves
