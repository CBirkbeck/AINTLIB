module

public import CebotarevDensity.Frobenius
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# The cyclotomic Frobenius as a norm residue, and Frobenii generate

Two arithmetic inputs of the Frobenius-fibre equidistribution (Gap B / L2), placed *below*
`ZetaProduct.lean` in the import order (the lemma `cyclotomic_frobenius_acts_as_norm_power`
currently lives in `Cyclotomic.lean`, which imports `ZetaProduct.lean` — the relevant content
is (re)stated here so that `ZetaProduct.lean` can consume it without an import cycle).

* `autToPow_frobeniusClass_out`: for `L = K(μ_m)` and a prime `𝔭` of `K` unramified in `L`
  with `N𝔭` coprime to `m`, the image of the Frobenius under the (faithful) cyclotomic
  character `Gal(L/K) →* (ℤ/m)ˣ` (`IsPrimitiveRoot.autToPow`) is the norm residue
  `N𝔭 mod m`. This is the multiplicative-dictionary form of the element-level fact
  `Frob_𝔭(ζ) = ζ^{N𝔭}` (Sharifi Prop. 7.1.15-adjacent; the element-level statement is
  `cyclotomic_frobenius_acts_as_norm_power`).

* `subgroup_eq_top_of_forall_frobenius_mem`: **Frobenii generate the Galois group** — a
  subgroup of `Gal(L/K)` containing the Frobenius representative of every unramified prime
  is the whole group. CFT-free proof via the project's zeta asymptotics: the fixed field `F`
  of such a subgroup has every unramified prime of `K` split completely; comparing
  `Σ_𝔭 N𝔭^{-s} ~ log (1/(s-1))` for `K` and for `F` (`primeIdealZetaSum_univ_tendsto_log`,
  both fields) against the `[F:K]`-fold multiplicity of split primes forces `[F:K] = 1`.
  (Used to realize every residue in the image of the cyclotomic character as a product of
  prime norm residues — the input `hS` of the κ-uniformity transfer.)
-/

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField

/-- Sharifi 7.2.1 step (i) — cyclotomic Frobenius formula (p. 142).
Verbatim source quote: "we have φ_𝔭(ζ_m) = ζ_m^{N𝔭} for a primitive mth root of
unity ζ_m". The coprimality `hcop : (N𝔭).Coprime m` is Sharifi's implicit
hypothesis made explicit — it is genuinely necessary: if `μ_m ⊆ K` then `L = K`,
`φ_𝔭 = id`, and *every* prime is unramified, yet the formula would force
`N𝔭 ≡ 1 (mod m)`. For a nontrivial extension it is the statement that an
unramified prime does not divide `m`; mathlib currently provides that only over
`ℚ` (`IsCyclotomicExtension.Rat.*`), so over a general base `K` the caller
supplies the coprimality.

(Relocated here from `Cyclotomic.lean` so that `ZetaProduct.lean` — which `Cyclotomic.lean`
imports — can consume it without an import cycle.) -/
theorem cyclotomic_frobenius_acts_as_norm_power
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (𝔭 : Ideal (𝓞 K))
    [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) :
    haveI : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 hP
    ∀ ζ : L, ζ ∈ primitiveRoots m L →
      arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ζ = ζ ^ Ideal.absNorm 𝔭 := by
  haveI : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 hP
  intro ζ hζmem
  set φ := arithFrobAt (𝓞 K) Gal(L/K) 𝔓
  have hζ : IsPrimitiveRoot ζ m := (mem_primitiveRoots (NeZero.pos m)).mp hζmem
  set z : 𝓞 L := hζ.toInteger
  have hzc : (algebraMap (𝓞 L) L) z = ζ := rfl
  have hzpow : z ^ m = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  set q := Ideal.absNorm 𝔭
  have h𝔭ne : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L hunr
  have hcopP : (Ideal.absNorm 𝔓).Coprime m := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓 𝔭 ‹𝔭.IsPrime› h𝔭ne]
    exact Nat.Coprime.pow_left _ hcop
  have hN1 : Ideal.absNorm 𝔓 ≠ 1 := fun h ↦ ‹𝔓.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hmnotmem : (m : 𝓞 L) ∉ 𝔓 := by
    intro hmem
    have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    rw [Ideal.absNorm_span_singleton, show ((m : ℕ) : 𝓞 L) = algebraMap ℤ (𝓞 L) (m : ℤ) by
        push_cast; rfl, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
    exact hN1 ((hcopP.pow_right _).eq_one_of_dvd hd)
  have hqcard : q = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) := by
    change Ideal.absNorm 𝔭 = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))
    rw [show 𝔭 = 𝔓.under (𝓞 K) from Ideal.LiesOver.over (p := 𝔭) (P := 𝔓),
      Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have key := (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).apply_of_pow_eq_one hzpow hmnotmem
  rw [← hqcard] at key
  have hmap := congrArg (algebraMap (𝓞 L) L) key
  rwa [map_pow,
    show (algebraMap (𝓞 L) L) ((MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) φ) z) = φ ζ from rfl,
    hzc] at hmap

/-- Powers of a primitive `n`-th root of unity agree iff the exponents are congruent mod `n`
(the easy direction: equal powers force congruent exponents). -/
private theorem pow_natModEq_of_pow_eq {S : Type*} [CommRing S] [IsDomain S] {μ : S} {n : ℕ}
    [NeZero n] (hμ : IsPrimitiveRoot μ n) {a b : ℕ} (h : μ ^ a = μ ^ b) : a ≡ b [MOD n] :=
  hμ.eq_orderOf ▸ (hμ.isOfFinOrder (NeZero.ne n)).pow_eq_pow_iff_modEq.mp h

/-- **The cyclotomic Frobenius is the norm residue** (multiplicative form). For `L = K(μ_m)`,
a primitive `m`-th root `ζ` of unity in `L`, and a prime `𝔭` of `K` unramified in `L` with
`N𝔭` coprime to `m`, the cyclotomic character `IsPrimitiveRoot.autToPow` sends the Frobenius
representative `(frobeniusClass K L 𝔭).out` to the unit `N𝔭 mod m`. -/
theorem autToPow_frobeniusClass_out
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ m) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m) :
    hζ.autToPow K ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) =
      ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop := by
  obtain ⟨𝔓, h𝔓prime, h𝔓lo, _⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  haveI := h𝔓prime
  haveI := h𝔓lo
  haveI : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 h𝔓lo
  set φ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) Gal(L/K) 𝔓
  have hclass : frobeniusClass K L 𝔭 = ConjClasses.mk φ :=
    frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr φ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) h𝔓lo
  have hconj : IsConj ((frobeniusClass K L 𝔭).out) φ := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, ← hclass, ConjClasses.mk, Quotient.out_eq]
  rw [isConj_iff_eq.mp ((hζ.autToPow K).map_isConj hconj)]
  have hact : φ ζ = ζ ^ Ideal.absNorm 𝔭 :=
    cyclotomic_frobenius_acts_as_norm_power K L m 𝔭 hunr hcop 𝔓 h𝔓lo ζ
      ((mem_primitiveRoots (NeZero.pos m)).mpr hζ)
  have hspec := hζ.autToPow_spec K φ
  rw [hact] at hspec
  apply Units.ext
  rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val ((hζ.autToPow K φ : (ZMod m)ˣ) : ZMod m)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (pow_natModEq_of_pow_eq hζ hspec)

/-! ### Sub-lemmas for `finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime`

The deep splitting/comparison content of the fixed-field reduction, established CFT-free. Step (A)
(splitting) factors through a *downward Frobenius restriction* lemma
(`isArithFrobAt_restrictNormal`,
the mirror of the upward `arithFrobAt_restrictScalars_eq` in `Main.lean`, replicated here because
`Main.lean` is below this file in the import order); step (B) (comparison) regroups the `F`-prime
zeta sum along the fibration `𝔮 ↦ 𝔮 ∩ 𝓞 K`; step (C) (limit) divides by `log(1/(s-1))` and passes
to the limit. -/

open scoped Pointwise in
/-- **Action intertwining for the normal restriction.** For an intermediate field `F` Galois over
`K`, the embedding `𝓞 F → 𝓞 L` intertwines the action of `σ : Gal(L/K)` with that of its normal
restriction `σ ↾ F : Gal(F/K)`: `σ • algebraMap (𝓞 F) (𝓞 L) y = algebraMap (𝓞 F) (𝓞 L) (σ↾F • y)`.
Checked after the (injective) embedding `𝓞 L → L`, via `AlgEquiv.restrictNormal_commutes`. -/
private theorem smul_algebraMap_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (F : IntermediateField K L) [IsGalois K F]
    (σ : L ≃ₐ[K] L) (y : 𝓞 F) :
    haveI : IsScalarTower K F L := F.isScalarTower_mid'
    σ • (algebraMap (𝓞 F) (𝓞 L) y) = algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y) := by
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  have hbridgeL : ∀ (g : L ≃ₐ[K] L) (x : 𝓞 L), ((g • x : 𝓞 L) : L) = g • (x : L) := fun g x ↦
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := L ≃ₐ[K] L) (R := 𝓞 L) (S := L) g x 1).symm
  have hbridgeF : ∀ (g : F ≃ₐ[K] F) (z : 𝓞 F), ((g • z : 𝓞 F) : F) = g • ((z : F)) := fun g z ↦
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := F ≃ₐ[K] F) (R := 𝓞 F) (S := F) g z 1).symm
  have hcoe : ∀ z : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 L) z : 𝓞 L) : L) = algebraMap F L (z : F) :=
    fun z ↦ by
      rw [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 L) L,
        RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 F) F L]
  rw [RingOfIntegers.ext_iff]
  change ((σ • algebraMap (𝓞 F) (𝓞 L) y : 𝓞 L) : L)
      = ((algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y) : 𝓞 L) : L)
  rw [hbridgeL, hcoe y, hcoe ((σ.restrictNormal F) • y), hbridgeF, AlgEquiv.smul_def,
    AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes]

/-- **Downward Frobenius restriction** (mirror of `Main.lean`'s upward
`arithFrobAt_restrictScalars_eq`). If `σ : Gal(L/K)` is an arithmetic Frobenius at a prime `𝔓` of
`𝓞 L`, then its normal restriction `σ ↾ F : Gal(F/K)` is an arithmetic Frobenius at `𝔮 = 𝔓 ∩ 𝓞 F`.
The defining congruence `σ x ≡ x^{N𝔭} (mod 𝔓)` descends along `𝓞 F → 𝓞 L` to `𝓞 F`, using the
action intertwining (`smul_algebraMap_eq`) and `(𝔓 ∩ 𝓞 F) ∩ 𝓞 K = 𝔓 ∩ 𝓞 K` (`Ideal.under_under`). -/
private theorem isArithFrobAt_restrictNormal
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (F : IntermediateField K L) [IsGalois K F] (σ : L ≃ₐ[K] L)
    (𝔓 : Ideal (𝓞 L)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    haveI : IsScalarTower K F L := F.isScalarTower_mid'
    IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F)) := by
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  intro y
  rw [Ideal.under_under 𝔓, Ideal.under, Ideal.mem_comap, map_sub, map_pow,
    show (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 F) (σ.restrictNormal F)) y
        = (σ.restrictNormal F) • y from rfl, ← smul_algebraMap_eq K L F σ y]
  exact hσ (algebraMap (𝓞 F) (𝓞 L) y)

/-- A prime of `𝓞 K` unramified in `L` is unramified in any intermediate field `F` Galois over `K`:
for a prime `𝔮` of `𝓞 F` over `𝔭`, pick `𝔓` of `𝓞 L` over `𝔮`; unramifiedness of `𝔓` over `𝓞 K`
descends to `𝔮` via `Algebra.IsUnramifiedAt.of_liesOver`. -/
private theorem unramifiedIn_intermediateField
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (F : IntermediateField K L) [IsGalois K F]
    (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K L 𝔭) :
    UnramifiedIn K (↥F) 𝔭 := by
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  haveI : IsScalarTower (𝓞 K) (𝓞 F) (𝓞 L) := inferInstance
  refine ⟨hunr.1, fun 𝔮 h𝔮max h𝔮lo ↦ ?_⟩
  haveI := h𝔮lo
  haveI := h𝔮max.isPrime
  obtain ⟨𝔓, h𝔓prime, h𝔓lo, -⟩ := exists_prime_liesOver (↥F) L 𝔮
    (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔮)
  haveI := h𝔓prime
  haveI := h𝔓lo
  haveI : 𝔓.LiesOver 𝔭 := ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓, h𝔓lo.over.symm, h𝔮lo.over.symm]⟩
  haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    hunr.2 𝔓 (h𝔓prime.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)) inferInstance
  exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) 𝔮 𝔓

/-- **Step (A): a Frobenius-trivial prime splits completely.** For `F = fixedField H` with `H`
abelian (hence normal) and a nonzero prime `𝔭` of `𝓞 K` unramified in `L` whose Frobenius
representative lies in `H`, the `F`-Frobenius class of `𝔭` is trivial: `frobeniusClass K F 𝔭 = [1]`.

In the abelian group `Gal(L/K)`, conjugate elements are equal, so a genuine Frobenius
`σ = arithFrobAt 𝔓` (`𝔓 ∣ 𝔭`) equals `(frobeniusClass 𝔭).out ∈ H = fixingSubgroup F`; its normal
restriction to `F` is the identity (`IntermediateField.restrictNormalHom_ker`), and by the
downward restriction `isArithFrobAt_restrictNormal` it is the `F`-Frobenius at `𝔮 = 𝔓 ∩ 𝓞 F`. -/
private theorem frobeniusClass_fixedField_eq_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    haveI : IsGalois K (IntermediateField.fixedField H) :=
      IsGalois.of_fixedField_normal_subgroup H
    frobeniusClass K (↥(IntermediateField.fixedField H)) 𝔭 = ConjClasses.mk 1 := by
  set F := IntermediateField.fixedField H with hF
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  obtain ⟨𝔓, h𝔓p, h𝔓lo, -⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  haveI := h𝔓p
  haveI := h𝔓lo
  haveI : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 h𝔓lo
  set σ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) Gal(L/K) 𝔓
  have hclass : frobeniusClass K L 𝔭 = ConjClasses.mk σ :=
    frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr σ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) h𝔓lo
  have hconj : IsConj σ ((frobeniusClass K L 𝔭).out) := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, hclass.symm, ConjClasses.mk, Quotient.out_eq]
  have hσeq : σ = (frobeniusClass K L 𝔭).out := by
    obtain ⟨c, hc⟩ := hconj
    rw [SemiconjBy, mul_comm' (c : Gal(L/K)) σ] at hc
    exact mul_right_cancel hc
  have hσfix : σ ∈ F.fixingSubgroup := by
    rw [hF, IntermediateField.fixingSubgroup_fixedField]
    exact hσeq ▸ hmem
  have hrestr : σ.restrictNormal F = 1 :=
    MonoidHom.mem_ker.mp <| (IntermediateField.restrictNormalHom_ker F).ge hσfix
  have h𝔮lo : (𝔓.under (𝓞 F)).LiesOver 𝔭 :=
    ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓]; exact h𝔓lo.over⟩
  haveI := h𝔮lo
  have hfrobF : IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F)) :=
    isArithFrobAt_restrictNormal K L F σ 𝔓 (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
  rw [frobeniusClass_eq_mk_of_isArithFrobAt K (↥F) 𝔭 (unramifiedIn_intermediateField K L F 𝔭 hunr)
    (σ.restrictNormal F) (𝔓.under (𝓞 F)) hfrobF h𝔮lo, hrestr]

/-- **Step (A), residue degree.** For `F = fixedField H` with the hypotheses of
`frobeniusClass_fixedField_eq_one`, every prime `𝔮` of `𝓞 F` above `𝔭` has residue degree one:
`[κ(𝔮) : κ(𝔭)] = 1`. Indeed the `F`-Frobenius class of `𝔭` is trivial
(`frobeniusClass_fixedField_eq_one`), so the residue degree equals `ord (1 : Gal(F/K)) = 1` by
`finrank_residue_eq_orderOf`. Shared by the count and norm forms below. -/
private theorem finrank_residue_fixedField_eq_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    haveI : IsGalois K (IntermediateField.fixedField H) :=
      IsGalois.of_fixedField_normal_subgroup H
    haveI : NumberField (IntermediateField.fixedField H) :=
      NumberField.of_intermediateField _
    ∀ 𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 →
      Module.finrank (𝓞 K ⧸ 𝔮.under (𝓞 K)) (𝓞 ↥(IntermediateField.fixedField H) ⧸ 𝔮) = 1 := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  have hunrF : UnramifiedIn K (↥F) 𝔭 := unramifiedIn_intermediateField K L F 𝔭 hunr
  have hfc : frobeniusClass K (↥F) 𝔭 = ConjClasses.mk (1 : Gal(↥F/K)) :=
    frobeniusClass_fixedField_eq_one K L H 𝔭 hunr hmem
  intro 𝔮 h𝔮p h𝔮lo
  haveI := h𝔮p
  haveI := h𝔮lo
  rw [finrank_residue_eq_orderOf K (↥F) (1 : Gal(↥F/K)) (ConjClasses.mk 1) rfl 𝔭 hunrF hfc 𝔮
    h𝔮lo, orderOf_one]

/-- **Step (A), count form.** For `F = fixedField H` with the hypotheses of
`frobeniusClass_fixedField_eq_one`, there are exactly `[F : K]` primes of `𝓞 F` above `𝔭`. Follows
from `card_primesAbove_mul_finrank_eq` (`Frobenius.lean`) with residue degree
`1` (`finrank_residue_fixedField_eq_one`). -/
private theorem card_primesOver_fixedField_eq_finrank
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    Nat.card {𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)) //
        𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} =
      Module.finrank K ↥(IntermediateField.fixedField H) := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  have hunrF : UnramifiedIn K (↥F) 𝔭 := unramifiedIn_intermediateField K L F 𝔭 hunr
  have hresdeg := finrank_residue_fixedField_eq_one K L H 𝔭 hunr hmem
  obtain ⟨𝔮₀, h𝔮₀p, h𝔮₀lo, -⟩ := exists_prime_liesOver K (↥F) 𝔭 (UnramifiedIn.ne_bot K L hunr)
  haveI := h𝔮₀p
  haveI := h𝔮₀lo
  have hcard := card_primesAbove_mul_finrank_eq K (↥F) 𝔭 hunrF 𝔮₀ h𝔮₀lo
  rw [hresdeg 𝔮₀ h𝔮₀p h𝔮₀lo, mul_one] at hcard
  rw [hcard, IsGalois.card_aut_eq_finrank K (↥F)]

/-- **Step (A), norm form.** For `F = fixedField H` with the hypotheses of
`frobeniusClass_fixedField_eq_one`, every prime `𝔮` of `𝓞 F` above `𝔭` has `N𝔮 = N𝔭`. Follows from
the inertia degree `f(𝔮 ∣ 𝔭) = 1` (`finrank_residue_fixedField_eq_one`) via
`Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`. -/
private theorem absNorm_eq_of_liesOver_fixedField
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    haveI : IsGalois K (IntermediateField.fixedField H) :=
      IsGalois.of_fixedField_normal_subgroup H
    haveI : NumberField (IntermediateField.fixedField H) :=
      NumberField.of_intermediateField _
    ∀ 𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 →
      Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭 := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  have hresdeg := finrank_residue_fixedField_eq_one K L H 𝔭 hunr hmem
  intro 𝔮 h𝔮p h𝔮lo
  haveI := h𝔮p
  haveI := h𝔮lo
  have hinert : (𝔮.under (𝓞 K)).inertiaDeg 𝔮 = 1 := by
    rw [Ideal.inertiaDeg_algebraMap]
    exact hresdeg 𝔮 h𝔮p h𝔮lo
  have hunder : 𝔮.under (𝓞 K) = 𝔭 := h𝔮lo.over.symm
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔮 (𝔮.under (𝓞 K)) inferInstance
    (hunder ▸ UnramifiedIn.ne_bot K L hunr), hinert, pow_one, hunder]

/-! ### Coprime-restricted Frobenii generation

The κ-uniformity transfer in `ZetaProduct.lean` realizes only the residues that are *coprime-norm
ideal Frobenius* values, so it needs `subgroup_eq_top_of_forall_frobenius_mem` with the Frobenius
hypothesis restricted to primes of **coprime norm** (`(N𝔭).Coprime m`). The proof is the same
fixed-field zeta comparison, but the `K`-side prime sum runs only over coprime-norm unramified
primes; the excluded primes (unramified but with `¬(N𝔭).Coprime m`) form a **finite** set (they
all divide the fixed ideal `(m)`), so the comparison ratio still tends to `1`. The finiteness
chain (`finite_badPrimes` etc., hoisted to `Frobenius.lean`) and the restricted log-asymptotic
feed `finrank_mul_unramified_coprime_le_univ`. -/

section CoprimeRestrictedComparison

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (m : ℕ) [NeZero m]

/-- The coprime-norm-unramified prime sum is asymptotic to `log(1/(s-1))`: it differs from the
universal prime sum (`primeIdealZetaSum_univ_tendsto_log`) by the finitely many excluded
primes — ramified (`finite_ramifiedIn`) or with norm not coprime to `m` (`finite_badPrimes`) —
whose bounded contribution is negligible against `log → ∞`. -/
private theorem primeIdealZetaSum_unramified_coprime_div_log_tendsto_one :
    Filter.Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s
          / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  set Uc : Set (Ideal (𝓞 K)) :=
    {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m}
  set D : Set (Ideal (𝓞 K)) :=
    {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m)}
  have hdisj : Disjoint Uc D :=
    Set.disjoint_left.mpr fun 𝔭 hc hd ↦ hd.2.2 ⟨hc.2.1, hc.2.2⟩
  have hcover : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ Uc ∪ D := fun 𝔭 hp hne ↦ by
    by_cases h : UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m
    · exact Or.inl ⟨hp, h.1, h.2⟩
    · exact Or.inr ⟨hp, hne, h⟩
  have hDfin : D.Finite := by
    refine ((finite_ramifiedIn K L).union (finite_badPrimes K m)).subset ?_
    rintro 𝔭 ⟨hp, hne, hnot⟩
    by_cases hunr : UnramifiedIn K L 𝔭
    · exact Or.inr ⟨hp, hne, fun hcop ↦ hnot ⟨hunr, hcop⟩⟩
    · exact Or.inl ⟨hp, hne, hunr⟩
  obtain ⟨CD, hCD⟩ : ∃ CD : ℝ, ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), primeIdealZetaSum D s ≤ CD := by
    refine ⟨Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ D ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Ioi] at hs
    exact primeIdealZetaSum_le_card_of_finite K hDfin (by linarith)
  have hDzero : Filter.Tendsto (fun s : ℝ ↦ primeIdealZetaSum D s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have hL := tendsto_log_one_div_sub_one_atTop
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop tendsto_const_nhds hL (a := CD))
    filter_upwards [hCD, hL.eventually_gt_atTop 0] with s hub hLpos
    have hDnn : 0 ≤ primeIdealZetaSum D s := by
      rw [primeIdealZetaSum_def]
      exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (div_nonneg hDnn hLpos.le)]
    gcongr
  have hcomb : Filter.Tendsto (fun s : ℝ ↦
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s / Real.log (1 / (s - 1))
        - primeIdealZetaSum D s / Real.log (1 / (s - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    simpa using (primeIdealZetaSum_univ_tendsto_log K).sub hDzero
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hadd : primeIdealZetaSum Uc s + primeIdealZetaSum D s =
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s := by
    rw [← primeIdealZetaSum_union_of_disjoint hdisj hs,
      primeIdealZetaSum_eq_univ_of_forall_prime_mem hcover s]
  rw [← sub_div, ← hadd, add_sub_cancel_right]

omit [IsGalois K L] [NeZero m] in
/-- The nonzero primes of `𝓞 F` lying over a fixed maximal prime `𝔭` of `𝓞 K` form a finite type,
for `F` an intermediate field Galois over `K`: they inject into the finite `𝔭.primesOver (𝓞 F)`. -/
private theorem finite_primesLiesOver_ne_bot (F : IntermediateField K L) [IsGalois K F]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal] :
    haveI : NumberField F := NumberField.of_intermediateField F
    Finite {𝔮 : Ideal (𝓞 ↥F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} := by
  haveI : NumberField F := NumberField.of_intermediateField F
  haveI : Finite (𝔭.primesOver (𝓞 ↥F)) :=
    (IsDedekindDomain.primesOver_finite 𝔭 (𝓞 ↥F)).to_subtype
  refine Finite.of_injective (β := 𝔭.primesOver (𝓞 ↥F)) (fun y ↦ ⟨y.1, y.2.1, y.2.2.1⟩)
    fun a b hab ↦ Subtype.ext ?_
  exact congrArg (Subtype.val : 𝔭.primesOver (𝓞 ↥F) → _) hab

omit [NeZero m] in
/-- The `F`-prime zeta sum over primes whose contraction to `𝓞 K` is coprime-norm-unramified
regroups, along `𝔮 ↦ 𝔮 ∩ 𝓞 K`, into `[F:K] · Σ_{coprime unram 𝔭} N𝔭^{-s}`, given the per-prime
count (`= [F:K]`) and norm-equality data `hsplit` for the fibres. -/
private theorem primeIdealZetaSum_under_eq_finrank_mul [IsMulCommutative Gal(L/K)]
    (H : Subgroup Gal(L/K))
    (hsplit : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → UnramifiedIn K L 𝔭 → (Ideal.absNorm 𝔭).Coprime m →
      Nat.card {𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)) //
          𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} = Module.finrank K ↥(IntermediateField.fixedField H)
        ∧ ∀ 𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 →
            Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭)
    {s : ℝ} (hs : 1 < s) :
    haveI : IsGalois K (IntermediateField.fixedField H) :=
      IsGalois.of_fixedField_normal_subgroup H
    haveI : NumberField (IntermediateField.fixedField H) := NumberField.of_intermediateField _
    primeIdealZetaSum {𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)) | 𝔮.IsPrime ∧
        UnramifiedIn K L (𝔮.under (𝓞 K)) ∧ (Ideal.absNorm (𝔮.under (𝓞 K))).Coprime m} s
      = (Module.finrank K ↥(IntermediateField.fixedField H) : ℝ) * primeIdealZetaSum
          {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  set U : Set (Ideal (𝓞 K)) :=
    {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m}
  set V : Set (Ideal (𝓞 F)) :=
    {𝔮 | 𝔮.IsPrime ∧ UnramifiedIn K L (𝔮.under (𝓞 K)) ∧ (Ideal.absNorm (𝔮.under (𝓞 K))).Coprime m}
  set IU := {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ U ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}
  set IV := {𝔮 : Ideal (𝓞 F) // 𝔮 ∈ V ∧ 𝔮.IsPrime ∧ 𝔮 ≠ ⊥}
  have hφ_mem : ∀ 𝔮 : IV, (𝔮.1.under (𝓞 K)) ∈ U ∧ (𝔮.1.under (𝓞 K)).IsPrime
      ∧ (𝔮.1.under (𝓞 K)) ≠ ⊥ := fun 𝔮 ↦ by
    haveI := 𝔮.2.2.1
    exact ⟨⟨inferInstance, 𝔮.2.1.2.1, 𝔮.2.1.2.2⟩, inferInstance,
      Ideal.IsIntegral.comap_ne_bot (𝓞 K) 𝔮.2.2.2⟩
  set φ : IV → IU := fun 𝔮 ↦ ⟨𝔮.1.under (𝓞 K), hφ_mem 𝔮⟩
  set e := Equiv.sigmaFiberEquiv φ
  have hsummSig : Summable (fun p : Σ 𝔭 : IU, {𝔮 : IV // φ 𝔮 = 𝔭} ↦
      (Ideal.absNorm (e p).1 : ℝ) ^ (-s)) :=
    (e.summable_iff (f := fun 𝔮 : IV ↦ (Ideal.absNorm 𝔮.1 : ℝ) ^ (-s))).mpr
      (summable_prime_absNorm_rpow V hs)
  rw [primeIdealZetaSum_def, ← e.tsum_eq (fun 𝔮 : IV ↦ (Ideal.absNorm (𝔮.1) : ℝ) ^ (-s)),
    hsummSig.tsum_sigma, primeIdealZetaSum_def, ← tsum_mul_left]
  refine tsum_congr (fun 𝔭 ↦ ?_)
  haveI := 𝔭.2.2.1
  have hfibeq : {𝔮 : IV // φ 𝔮 = 𝔭} ≃
      {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭.1 ∧ 𝔮 ≠ ⊥} :=
    { toFun := fun x ↦ ⟨x.1.1, x.1.2.2.1, ⟨(Subtype.ext_iff.mp x.2).symm⟩, x.1.2.2.2⟩
      invFun := fun y ↦ ⟨⟨y.1, ⟨y.2.1, by
          haveI := y.2.1
          haveI := y.2.2.1
          exact (y.2.2.1.over ▸ 𝔭.2.1.2 : UnramifiedIn K L (y.1.under (𝓞 K)) ∧
            (Ideal.absNorm (y.1.under (𝓞 K))).Coprime m)⟩, y.2.1, y.2.2.2⟩,
        Subtype.ext (haveI := y.2.2.1; y.2.2.1.over.symm)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hconst : ∀ x : {𝔮 : IV // φ 𝔮 = 𝔭}, (Ideal.absNorm (e ⟨𝔭, x⟩).1 : ℝ) ^ (-s)
      = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun x ↦ by
    change (Ideal.absNorm x.1.1 : ℝ) ^ (-s) = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
    rw [(hsplit 𝔭.1 𝔭.2.2.1 𝔭.2.1.2.1 𝔭.2.1.2.2).2 x.1.1 x.1.2.2.1 ⟨(Subtype.ext_iff.mp x.2).symm⟩]
  haveI : 𝔭.1.IsMaximal := 𝔭.2.2.1.isMaximal 𝔭.2.2.2
  haveI : Finite {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭.1 ∧ 𝔮 ≠ ⊥} :=
    finite_primesLiesOver_ne_bot K L F 𝔭.1
  haveI : Finite {𝔮 : IV // φ 𝔮 = 𝔭} := Finite.of_equiv _ hfibeq.symm
  rw [tsum_congr hconst, tsum_const, Nat.card_congr hfibeq,
    (hsplit 𝔭.1 𝔭.2.2.1 𝔭.2.1.2.1 𝔭.2.1.2.2).1, nsmul_eq_mul, mul_comm]

omit [NeZero m] in
/-- **Coprime-restricted fibred zeta comparison.** The coprime-restricted analog of
`finrank_mul_unramified_le_univ`: with the Frobenius-membership hypothesis required only on
**coprime-norm** unramified primes, `[F:K] · Σ_{coprime unram 𝔭} N𝔭^{-s} ≤ Σ_{𝔮 of F} N𝔮^{-s}`.
The `F`-prime sum restricted to primes over a coprime-norm-unramified base regroups (along
`𝔮 ↦ 𝔮 ∩ 𝓞 K`) into `[F:K] · Σ_{coprime unram 𝔭} N𝔭^{-s}`
(`primeIdealZetaSum_under_eq_finrank_mul`) and is `≤` the full `F`-prime sum. -/
private theorem finrank_mul_unramified_coprime_le_univ
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      (Ideal.absNorm 𝔭).Coprime m → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H)
    {s : ℝ} (hs : 1 < s) :
    (Module.finrank K ↥(IntermediateField.fixedField H) : ℝ) *
        primeIdealZetaSum
          {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s
      ≤ primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField H)))) s := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  have hsplit : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → UnramifiedIn K L 𝔭 → (Ideal.absNorm 𝔭).Coprime m →
      Nat.card {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} = Module.finrank K ↥F
        ∧ ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 → Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭 :=
    fun 𝔭 h𝔭p h𝔭unr h𝔭cop ↦
      ⟨card_primesOver_fixedField_eq_finrank K L H 𝔭 h𝔭unr
          (hH 𝔭 h𝔭p (UnramifiedIn.ne_bot K L h𝔭unr) h𝔭unr h𝔭cop),
        absNorm_eq_of_liesOver_fixedField K L H 𝔭 h𝔭unr
          (hH 𝔭 h𝔭p (UnramifiedIn.ne_bot K L h𝔭unr) h𝔭unr h𝔭cop)⟩
  rw [← primeIdealZetaSum_under_eq_finrank_mul K L m H hsplit hs]
  exact primeIdealZetaSum_le_of_subset (Set.subset_univ _) hs

/-- **Coprime-restricted bound on the fixed-field degree.** The coprime-norm analog of
`finrank_fixedField_le_one_of_forall_frobenius_mem`: with the Frobenius hypothesis required only
on coprime-norm unramified primes, `[F:K] ≤ 1`. Same proof, dividing the coprime-restricted
comparison by `log(1/(s-1))` and passing to the limit; the coprime-restricted `K`-side ratio
tends to `1` by `primeIdealZetaSum_unramified_coprime_div_log_tendsto_one`. -/
private theorem finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      (Ideal.absNorm 𝔭).Coprime m → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    Module.finrank K (IntermediateField.fixedField H) ≤ 1 := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  set d : ℕ := Module.finrank K ↥F
  rw [← Nat.cast_le (α := ℝ), Nat.cast_one]
  set A : ℝ → ℝ := fun s ↦ primeIdealZetaSum
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s
  set B : ℝ → ℝ := fun s ↦
    primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 ↥F))) s
  have hAtend : Filter.Tendsto (fun s ↦ A s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    primeIdealZetaSum_unramified_coprime_div_log_tendsto_one K L m
  have hBtend : Filter.Tendsto (fun s ↦ B s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    primeIdealZetaSum_univ_tendsto_log (↥F)
  have hLpos : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), 0 < Real.log (1 / (s - 1)) :=
    tendsto_log_one_div_sub_one_atTop.eventually_gt_atTop 0
  have hev : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
      (d : ℝ) * (A s / Real.log (1 / (s - 1))) ≤ B s / Real.log (1 / (s - 1)) := by
    filter_upwards [hLpos, self_mem_nhdsWithin] with s hLs hs1
    simp only [Set.mem_Ioi] at hs1
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (finrank_mul_unramified_coprime_le_univ K L m H hH hs1) hLs.le
  have hlim := le_of_tendsto_of_tendsto (hAtend.const_mul (d : ℝ)) hBtend hev
  simpa using hlim

/-- **Frobenii of coprime-norm primes generate the Galois group** (abelian case). A subgroup of
`Gal(L/K)` containing the Frobenius representative of every nonzero prime of `K` that is
unramified in `L` **and has norm coprime to `m`** is all of `Gal(L/K)`.

This is the coprime-restricted analog of `subgroup_eq_top_of_forall_frobenius_mem`, used by the
κ-uniformity realization in `ZetaProduct.lean`: it realizes only the residues that arise from
coprime-norm ideal Frobenius values, so it can only assert the Frobenius hypothesis there. The
proof is identical modulo restricting the fixed-field zeta comparison to coprime-norm primes (the
excluded unramified primes with non-coprime norm form a finite set, leaving the comparison ratio
unchanged): reduce `H = ⊤` to `[F:K] ≤ 1` and apply
`finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime`. -/
theorem subgroup_eq_top_of_forall_frobenius_mem_of_coprime
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      (Ideal.absNorm 𝔭).Coprime m → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    H = ⊤ := by
  rw [← Subgroup.card_eq_iff_eq_top]
  have hfk : Module.finrank K (IntermediateField.fixedField H) = 1 :=
    le_antisymm (finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime K L m H hH)
      Module.finrank_pos
  have htower := Module.finrank_mul_finrank K (IntermediateField.fixedField H) L
  rw [hfk, one_mul] at htower
  rw [IsGalois.card_aut_eq_finrank K L, ← htower, IntermediateField.finrank_fixedField_eq_card H]

end CoprimeRestrictedComparison

/-- **Frobenii generate the Galois group** (CFT-free, via the zeta asymptotics; abelian case). A
subgroup of `Gal(L/K)` that contains the Frobenius representative of every nonzero prime of `K`
unramified in `L` is all of `Gal(L/K)`.

**Statement change (authorized by the orchestrator).** The hypothesis `[IsMulCommutative Gal(L/K)]`
has been added (after `[FiniteDimensional K L]`). It is genuinely needed: the hypothesis only
provides the chosen class *representative* `(frobeniusClass 𝔭).out ∈ H`, which suffices precisely
when conjugacy classes are singletons, i.e. when `Gal(L/K)` is abelian (the only case the project
consumes — `L = K(μ_m)`). For a general (non-abelian) `G` the out-only membership is too weak: a
non-normal `H` containing one Frobenius conjugate per prime need not contain the whole class, and
the split-completely transfer (hence the `[F:K]`-fold zeta multiplicity) fails. The general form
would have to quantify over the entire class, not just `.out`.

Proof: reduce `H = ⊤` to `[F:K] ≤ 1` for `F = fixedField H`
(`Subgroup.card_eq_iff_eq_top` + `finrank_fixedField_eq_card` + `card_aut_eq_finrank`), then apply
`finrank_fixedField_le_one_of_forall_frobenius_mem`. -/
theorem subgroup_eq_top_of_forall_frobenius_mem
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    H = ⊤ :=
  subgroup_eq_top_of_forall_frobenius_mem_of_coprime K L 1 H
    fun 𝔭 hp hne hunr _ ↦ hH 𝔭 hp hne hunr

end Chebotarev
