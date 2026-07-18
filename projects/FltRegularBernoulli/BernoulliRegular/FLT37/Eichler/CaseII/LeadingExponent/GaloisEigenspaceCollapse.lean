import BernoulliRegular.FLT37.Eichler.Saturation.RealCyclotomicUnitSaturation
import BernoulliRegular.CyclotomicUnits.NormalizedIndex
import BernoulliRegular.UnitQuotient.Washington814ForwardD

/-!
# The Galois `Δ`-action eigenvalue on the real cyclotomic units, and the
Corollary-8.15 eigenspace collapse for `p = 37`

This file builds the **operative core** of the Case-II Corollary-8.15 descent
for Fermat's Last Theorem at `p = 37`: the Galois `Δ`-action eigenvalue on the
real cyclotomic units, wired to the *proven* eigenspace machinery, and used to

* discharge the analytic input `SinnottIndexFormula 37` *for free* from the
  proven Kummer–Dirichlet determinant identity (`kummerDirichletDeterminant_of_deletedFourier`,
  valid for `5 ≤ 37`); and
* reduce the per-descent-unit eigenspace predicate `Cor815EigenCollapseAt` to a
  **sound, eigenvalue-indexed** hypothesis on the descent unit's mod-`37`
  free-part class (its membership in the single irregular `ω^{32}`-eigenspace),
  via the Galois `Δ`-action eigenvalue `σ_a(E_i) = E_i^{a^i} · (37th power)`.

It imports only — it does not modify any existing file.

## What is the Galois `Δ`-action eigenvalue?

For the real cyclotomic units `E_i` (Washington's `η_a/η_b` expansion basis), the
cyclotomic Galois automorphism `σ_a` acts on the mod-`37` free-part class
`[E_i] ∈ (E_K free)/37` by the scalar `a^i` (Washington Corollary 8.15 / Lemma
9.9 eigenvalue): `σ_a([E_i]) = a^i • [E_i]`.  In the repository this is the
*proven* `pollaczekUnit_image_eigenvalue_zmod_general_forall` (for the K-side
Pollaczek units `E_i`, even `i ∈ [2, 34]`) and
`pollaczekUnit_image_in_omegaChar_eigenspace_general` (its eigenspace form): the
class `[E_i]` lies in the `ω^i`-eigenspace of the `Δ`-action on `(E_K free)/37`.

**Soundness note.**  This eigenvalue is *per-index*: `[E_i]` lies in the
`ω^i`-eigenspace, which for distinct even `i` are *distinct* one-dimensional
subspaces.  It is therefore **false** that an arbitrary real cyclotomic unit is
an `E_{32}`-monomial modulo `37`-th powers (a regular `E_2` lies in the
`ω^2`-eigenspace, not the `ω^{32}` one).  Every collapse statement below is
**eigenvalue-indexed**: it applies to a unit whose class lies in the *specific*
irregular `ω^{32}`-eigenspace, never to all of `C⁺`.

## What is built here (real, axiom-clean Lean)

* `caseIIGaloisEigen_kummerDirichletDeterminant_37` /
  `caseIIGaloisEigen_sinnottRegulatorIdentity_37` /
  `caseIIGaloisEigen_sinnottIndexFormula_37` — **step (A)**: `SinnottIndexFormula 37`
  is discharged for free from the proven `kummerDirichletDeterminant_of_deletedFourier`.

* `caseIIGaloisEigen_assumptionII_of_realDescentData` /
  `caseIIGaloisEigen_assumptionII_of_eigenCollapseProvenance` — the Corollary-8.15
  discharge of **Assumption II** with `SinnottIndexFormula 37` now supplied by
  step (A): the *only* remaining inputs are `Cor815RealDescentData37`
  (descent-unit provenance + eigenspace collapse) and `Lemma98LocalPower37`.

* The Galois `Δ`-action eigenvalue surfaced at the K⁺ level on the real
  cyclotomic-unit family (`caseIIGaloisEigen_realUnit_omegaChar_eigenvalue`), and
  the **eigenspace collapse bridge**
  (`caseIIGaloisEigen_eigenCollapse_of_class_in_omega32_eigenspace`,
  `caseIIGaloisEigen_realDescentData_of_provenance`) reducing
  `Cor815EigenCollapseAt` for the descent unit to the *sound, eigenvalue-indexed*
  hypothesis that its class lies in the irregular `ω^{32}`-eigenspace.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer GTM 83:
  Corollary 8.15 (p. 153), Lemma 9.9 (pp. 180–181), §8.2 (Theorem 8.2, Sinnott).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

/-! ## (A) Wiring `SinnottIndexFormula 37` from the proven determinant identity

`SinnottIndexFormula 37` is the named analytic input carried by
`CaseIICor815Lemma98.lean` (`[E⁺ : C⁺] = h⁺`).  It is **derivable for free**: the
Kummer–Dirichlet determinant identity `KummerDirichletDeterminant 37` is *proven*
by `kummerDirichletDeterminant_of_deletedFourier` (`5 ≤ 37`), and equals
`SinnottRegulatorIdentity 37` (`sinnottRegulatorIdentity_iff_kummerDirichletDeterminant`,
literally the same equation), from which `sinnottIndexFormula_of_regulatorIdentity`
gives `SinnottIndexFormula 37`. -/

/-- **The Kummer–Dirichlet determinant identity for `p = 37`** (proven, free).
The cyclotomic-unit regulator-of-family determinant identity
`regOfFamily(family) = 2^{17} · h⁺ · regulator(K⁺)`, banked from the proven
`kummerDirichletDeterminant_of_deletedFourier` (the deleted-Fourier / Kummer
1850 determinant computation), valid for `5 ≤ 37`. -/
theorem caseIIGaloisEigen_kummerDirichletDeterminant_37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    FLT37.Sinnott.KummerDirichletDeterminant 37 (CyclotomicField 37 ℚ)
      (by decide) (by decide) :=
  BernoulliRegular.kummerDirichletDeterminant_of_deletedFourier
    (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide) (by decide) (by decide)

/-- **Sinnott's regulator identity for `p = 37`** (proven, free).  Equal to the
Kummer–Dirichlet determinant identity by
`sinnottRegulatorIdentity_iff_kummerDirichletDeterminant` (`Iff.rfl`). -/
theorem caseIIGaloisEigen_sinnottRegulatorIdentity_37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    FLT37.Sinnott.SinnottRegulatorIdentity 37 (CyclotomicField 37 ℚ)
      (by decide) (by decide) :=
  (FLT37.Sinnott.sinnottRegulatorIdentity_iff_kummerDirichletDeterminant
    (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide)).1
    caseIIGaloisEigen_kummerDirichletDeterminant_37

/-- **Sinnott's index formula for `p = 37`** (proven, free): `[E⁺ : C⁺] = h⁺`.

This *discharges* the named analytic input `SinnottIndexFormula 37` that
`CaseIICor815Lemma98.lean` carries as a hypothesis throughout the Corollary-8.15
saturation core.  It is derived from the proven `SinnottRegulatorIdentity 37`
(itself the proven Kummer–Dirichlet determinant identity) via
`sinnottIndexFormula_of_regulatorIdentity`. -/
theorem caseIIGaloisEigen_sinnottIndexFormula_37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    FLT37.Sinnott.SinnottIndexFormula 37 (CyclotomicField 37 ℚ)
      (by decide) (by decide) :=
  FLT37.Sinnott.sinnottIndexFormula_of_regulatorIdentity
    (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide)
    caseIIGaloisEigen_sinnottRegulatorIdentity_37

/-! ### Assumption II with `SinnottIndexFormula 37` discharged

With `SinnottIndexFormula 37` now supplied by step (A), the Corollary-8.15
discharge `caseIICor815_singleIndexExpansion_of_realDescentData` and the
Assumption-II composer `caseIICor815_assumptionII_of_reduced_inputs` no longer
need it as an external hypothesis.  The *only* remaining inputs are the
descent-unit data `Cor815RealDescentData37` (realness/membership + the
eigenspace collapse for the descent unit) and `Lemma98LocalPower37` (the mod-`𝔩`
Kummer congruence). -/

/-- **Corollary 8.15 single-index expansion for the descent unit, `SinnottIndexFormula 37`
discharged** (proven, axiom-clean *given* `Cor815RealDescentData37`).

`caseIICor815_singleIndexExpansion_of_realDescentData` with the analytic input
`SinnottIndexFormula 37` now supplied for free by step (A).  Hence
`Cor815SingleIndexExpansion37` follows from the single named descent-unit input
`Cor815RealDescentData37`. -/
theorem caseIIGaloisEigen_singleIndexExpansion_of_realDescentData
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_prov : Cor815RealDescentData37) :
    Cor815SingleIndexExpansion37 :=
  caseIICor815_singleIndexExpansion_of_realDescentData
    caseIIGaloisEigen_sinnottIndexFormula_37 h_prov

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II from `Cor815RealDescentData37` + `Lemma98LocalPower37`**, with
`SinnottIndexFormula 37` discharged for free (proven, axiom-clean).

This is `caseIICor815_assumptionII_of_reduced_inputs` with the analytic input
`SinnottIndexFormula 37` supplied by step (A).  It reduces **Assumption II**
(`WashingtonCaseIIExactQuotientUnitPower37Source`) — and hence the entire
Theorem-9.5 Case-II descent, modulo the proven σ-stable adjacent-generator
producer — to the *two* precisely-named inputs:

* `Cor815RealDescentData37` — for the descent unit `ε₁/ε₂`: it is the K-image of a
  real cyclotomic unit `w ∈ C⁺` whose `37`-residue is an `E₃₂`-monomial; and
* `Lemma98LocalPower37` — Washington Lemma 9.8's mod-`𝔩` Kummer congruence.

The analytic `SinnottIndexFormula 37` is **no longer a free parameter** — it is
proven here from the Kummer–Dirichlet determinant identity. -/
theorem caseIIGaloisEigen_assumptionII_of_reduced_inputs
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_prov : Cor815RealDescentData37)
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIICor815_assumptionII_of_reduced_inputs
    caseIIGaloisEigen_sinnottIndexFormula_37 h_prov h_localPow

/-! ## (B) The Galois `Δ`-action eigenvalue and the all-nonzero certificate

The Galois `Δ`-action eigenvalue `σ_a([E_i]) = a^i • [E_i]` on the mod-`37`
free-part class of the real cyclotomic units `E_i` is the *proven*
`pollaczekUnit_image_eigenvalue_zmod_general_forall`; its eigenspace form is
`pollaczekUnit_image_in_omegaChar_eigenspace_general` (`[E_i]` lies in the
`ω^i`-eigenspace).  Both are proven for general even `i ∈ [2, 34]`.

The **all-nonzero certificate** — every even Pollaczek class `[E_i]` (`2 ≤ i ≤ 34`)
is nonzero in `(E_K free)/37` — is itself *proven unconditionally* for `37` from
the `i = 32` local certificate (`flt37_pollaczekUnit_class_in_modp_freepart_ne_zero`)
and Washington Theorem 8.16 (class form) contraposed against the Bernoulli table
`flt37_bernoulli_table` (`37 ∤ B_i` for even `i ≠ 32`).  This is exactly the data
that proves Vandiver for `37`; we re-bank it here to drive the eigenspace
linear independence and the kernel-vanishing collapse. -/

/-- **The all-nonzero certificate for `p = 37`** (proven, unconditional): every
even Pollaczek class `[E_i]` (`2 ≤ i ≤ 34`) is nonzero in `(E_K free)/37`.

For `i = 32` this is the proven local mod-`𝔩` certificate
(`flt37_pollaczekUnit_class_in_modp_freepart_ne_zero`); for `i ≠ 32` it is
Washington Theorem 8.16 in class form
(`flt37_dvd_bernoulli_of_pollaczek_class_eq_zero`) contraposed against the
finite Bernoulli table (`flt37_bernoulli_table`).  This is the precise hypothesis
of `CPlusGenerator_image_linearIndependent` / the eigenspace collapse. -/
theorem caseIIGaloisEigen_pollaczekClasses_ne_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 →
      cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
          (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) i))) ≠ 0 := by
  intro i hi_even hi2 hi34
  rw [← cyclotomicUnitToFreePartModPAdd_apply]
  by_cases hi32 : i = 32
  · subst hi32
    exact FLT37.flt37_pollaczekUnit_class_in_modp_freepart_ne_zero
  · intro hzero
    exact FLT37.Sinnott.flt37_bernoulli_table i hi_even hi2 hi34 hi32
      (FLT37.flt37_dvd_bernoulli_of_pollaczek_class_eq_zero i hi_even hi2 hi34 hzero)

/-- **The Galois `Δ`-action eigenvalue, surfaced for the descent index `i = 32`**
(proven re-export).  For every cyclotomic Galois automorphism `σ_a` (`a ∈ Δ`),

  `σ_a([E₃₂]) = a^{32} • [E₃₂]`   in `(E_K free)/37`,

i.e. the mod-`37` free-part class of the irregular real cyclotomic unit
`E₃₂ = pollaczekUnit 37 K 32` is an `ω^{32}`-eigenvector of the `Δ`-action.  This
is the Washington Corollary 8.15 / Lemma 9.9 eigenvalue for `37`'s single
irregular eigenspace; it is the proven
`pollaczekUnit_image_eigenvalue_zmod_general_forall` at `i = 32`. -/
theorem caseIIGaloisEigen_omega32_eigenvalue
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [Fact (Nat.Prime 37)] [NumberField.IsCMField K]
    (a : (ZMod 37)ˣ) :
    cyclotomicUnitFreePartModPDeltaActionZMod (p := 37) K a
        (cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (FLT37.pollaczekUnit 37 K 32)))) =
      (((a ^ 32 : (ZMod 37)ˣ) : ZMod 37)) •
        cyclotomicUnitFreePartModPClass (p := 37) K
          (Additive.ofMul (cyclotomicUnitFreeClass K (FLT37.pollaczekUnit 37 K 32))) :=
  pollaczekUnit_image_eigenvalue_zmod_general_forall (K := K) 32 (by decide) (by decide)
    (by decide) a

/-- **The descent unit's eigenvector lies in the `ω^{32}`-eigenspace** (proven
re-export): `[E₃₂] ∈ ω^{32}`-eigenspace of the `Δ`-action on `(E_K free)/37`.

This is the eigenspace form of the Galois `Δ`-action eigenvalue
`caseIIGaloisEigen_omega32_eigenvalue` — `pollaczekUnit_image_in_omegaChar_eigenspace_general`
at `i = 32`.  It is the **sound, eigenvalue-indexed** statement underlying the
collapse: only the `ω^{32}`-eigenspace (not all of `C⁺`) is collapsed to `E₃₂`. -/
theorem caseIIGaloisEigen_E32_in_omega32_eigenspace
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [Fact (Nat.Prime 37)] [NumberField.IsCMField K] :
    cyclotomicUnitFreePartModPClass (p := 37) K
        (Additive.ofMul (cyclotomicUnitFreeClass K (FLT37.pollaczekUnit 37 K 32))) ∈
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37) K
        (cyclotomicOmegaChar (p := 37) 32) :=
  pollaczekUnit_image_in_omegaChar_eigenspace_general (K := K) 32 (by decide) (by decide)
    (by decide)

/-! ## (C) The kernel-vanishing collapse: `realUnitToFreePartModP v = 0 ⟹ v = β^{37}`

The composite `φ = realUnitToFreePartModP : (𝓞 K⁺)ˣ → (E_K free)/37` restricted to
`C⁺` is *injective on `C⁺/(C⁺)^{37}`* under the all-nonzero certificate (the
`φ(CPlusGenerator_a)` are linearly independent by
`CPlusGenerator_image_linearIndependent`).  Hence a `C⁺` unit in the kernel of
`φ` is a `37`-th power.  This is the faithful-detection half of Washington
Corollary 8.15: the regular indices drop out *and* the only way the class
vanishes is for the unit to be a genuine `37`-th power.

This is the irreducible bridge from "mod-`37` free-part class is `0`" to
"`37`-th power in `(𝓞 K⁺)ˣ`", proved here head-on via the exponent expansion
`CPlusExponentProduct` and the linear independence of the generator images. -/

/-- `caseIICPlus37 = CPlus 37` (the two spellings of the real cyclotomic-unit
subgroup coincide definitionally: both are
`closure(range cyclotomicUnitFamilyKplusFinRank) ⊔ torsion`, which equals
`CPlus = closure({-1} ∪ range CPlusGenerator)` by
`cyclotomicUnitIndexSubgroup_eq_CPlus`). -/
theorem caseIIGaloisEigen_caseIICPlus37_eq_CPlus
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    caseIICPlus37 =
      BernoulliRegular.CPlus (p := 37) (K := CyclotomicField 37 ℚ) (by decide) :=
  BernoulliRegular.cyclotomicUnitIndexSubgroup_eq_CPlus
    (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide)

/-- **Kernel-vanishing collapse on `CPlus`** (proven, unconditional via the proven
all-nonzero certificate): a real cyclotomic unit `v ∈ CPlus` whose mod-`37`
free-part class `realUnitToFreePartModP v` vanishes is a `37`-th power in
`(𝓞 K⁺)ˣ` — indeed `∃ β, β ^ 37 = v`.

This is the faithful-detection content of Corollary 8.15: expanding `v` as a
`CPlusExponentProduct` and using the *proven* linear independence of the
generator images `φ(CPlusGenerator_a)` (from `caseIIGaloisEigen_pollaczekClasses_ne_zero`),
every generator exponent vanishes mod `37`, so `v` is `(-1)^s` times a genuine
`37`-th product — and `-1 = (-1)^{37}`.  No external hypothesis: the all-nonzero
certificate is proven. -/
theorem caseIIGaloisEigen_isPow37_of_realUnitToFreePartModP_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hv : v ∈ BernoulliRegular.CPlus (p := 37) (K := CyclotomicField 37 ℚ) (by decide))
    (hφ : FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul v) = 0) :
    ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ, β ^ 37 = v := by
  -- Expand v as a CPlusExponentProduct.
  obtain ⟨s, e, hse⟩ :=
    BernoulliRegular.exists_CPlusExponentProduct_of_mem_CPlus
      (p := 37) (K := CyclotomicField 37 ℚ) (by decide) hv
  -- The φ-image of v is ∑ e a • φ(CPlusGenerator a) = 0.
  have hsum : ∑ a : Fin ((37 - 3) / 2),
      e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
        (Additive.ofMul (BernoulliRegular.CPlusGenerator
          (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a)) = 0 := by
    rw [← FLT37.realUnitToFreePartModP_CPlusExponentProduct, hse]
    exact hφ
  -- Linear independence (from the proven all-nonzero certificate) forces e a ≡ 0 (mod 37).
  have hli := FLT37.CPlusGenerator_image_linearIndependent
    (K := CyclotomicField 37 ℚ) caseIIGaloisEigen_pollaczekClasses_ne_zero
  have hzero : ∀ a, ((e a : ℤ) : ZMod 37) = 0 := by
    -- Rewrite ∑ e a • φ_a as ∑ (e a : ZMod 37) • φ_a, then apply linear independence.
    have hsum' : ∑ a : Fin ((37 - 3) / 2),
        ((e a : ℤ) : ZMod 37) • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
          (Additive.ofMul (BernoulliRegular.CPlusGenerator
            (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a)) = 0 := by
      rw [← hsum]
      exact Finset.sum_congr rfl fun a _ => Int.cast_smul_eq_zsmul (ZMod 37) (e a) _
    exact fun a => Fintype.linearIndependent_iff.mp hli (fun a => ((e a : ℤ) : ZMod 37)) hsum' a
  -- e a ≡ 0 (mod 37) ⟹ 37 ∣ e a ⟹ e a = 37 * k a.
  have hdvd : ∀ a, (37 : ℤ) ∣ e a := fun a =>
    (CharP.intCast_eq_zero_iff (ZMod 37) 37 (e a)).mp (hzero a)
  choose k hk using hdvd
  -- v = (CPlusExponentProduct s k)^37.
  refine ⟨BernoulliRegular.CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ)
    (by decide) s k, ?_⟩
  rw [BernoulliRegular.CPlusExponentProduct_pow_of_exponents_eq_mul
    (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide) s e k hk, hse]

/-! ## (D) The eigenspace collapse: discharging `Cor815EigenCollapseAt`

We now feed the Galois `Δ`-action eigenvalue structure (§B) and the
kernel-vanishing collapse (§C) into `Cor815EigenCollapseAt`.

The **sound, eigenvalue-indexed** hypothesis on the descent unit `w ∈ C⁺` is that
its mod-`37` free-part class is an `E₃₂`-monomial — a `ZMod 37`-scalar multiple
of the single irregular eigenvector `[E₃₂]`:

  `realUnitToFreePartModP w = c • [pollaczekUnit 32]`   for some `c : ZMod 37`.

This is **not** asserted for arbitrary `w ∈ C⁺`: a regular generator's class lies
in a *different* `ω^i`-eigenspace (`i ≠ 32`), so it is not a multiple of `[E₃₂]`.
It holds for the descent unit precisely because the regular indices drop out —
the Galois `Δ`-action eigenvalue (§B) plus the half-range Vandermonde collapse
`caseIIThm95_coeff_collapse_even`.  Equivalently (and this is the form we derive
below), `realUnitToFreePartModP w` lies in the irregular `ω^{32}`-eigenspace.

From this hypothesis: since `realUnitToFreePartModP W₃₂ = 2 • [E₃₂]` and `2` is a
unit mod `37`, choosing `d := (c · 2⁻¹).val` makes
`realUnitToFreePartModP (w · (W₃₂^d)⁻¹) = 0`, whence the kernel-vanishing
collapse (§C) gives `w · (W₃₂^d)⁻¹ = β^{37}` — i.e. `Cor815EigenCollapseAt w`. -/

/-- **`realUnitToFreePartModP W₃₂ = 2 • [E₃₂]`** (proven re-export): the
`Δ`-symmetrised K⁺-side preimage `W₃₂ = pollaczekUnitPlusKplus 32` has mod-`37`
free-part class twice the bare irregular eigenvector `[E₃₂] = [pollaczekUnit 32]`
(the factor `2` from the σ-symmetrisation `pollaczekUnitPlus = pollaczekUnit ·
σ(pollaczekUnit)`). -/
theorem caseIIGaloisEigen_realUnitToFreePartModP_W32
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
        (Additive.ofMul caseIICor815_W32) =
      (2 : ℕ) • cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)) :=
  FLT37.realUnitToFreePartModP_pollaczekUnitPlusKplus (K := CyclotomicField 37 ℚ) 32

/-- **The `E₃₂`-monomial residue collapse ⟹ `Cor815EigenCollapseAt`** (proven,
axiom-clean, **sound**).

For a real cyclotomic unit `w ∈ C⁺` whose mod-`37` free-part class is an
`E₃₂`-monomial — `realUnitToFreePartModP w = c • [E₃₂]` for some `c : ZMod 37`
(the *eigenvalue-indexed* hypothesis: only the single irregular `ω^{32}`-component
survives) — the eigenspace predicate `Cor815EigenCollapseAt w` holds: there is `d`
with `w · (W₃₂^d)⁻¹` a `37`-th power in `(𝓞 K⁺)ˣ`.

The exponent is `d := (c · 2⁻¹).val` (so that `2d ≡ c` mod `37`, matching
`realUnitToFreePartModP W₃₂ = 2 • [E₃₂]`); then
`realUnitToFreePartModP (w · (W₃₂^d)⁻¹) = 0`, and the kernel-vanishing collapse §C
(`caseIIGaloisEigen_isPow37_of_realUnitToFreePartModP_eq_zero`, banking the proven
all-nonzero certificate) upgrades it to a genuine `37`-th power. -/
theorem caseIIGaloisEigen_eigenCollapse_of_E32_monomial_residue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hw : w ∈ caseIICPlus37)
    {c : ZMod 37}
    (hres : FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul w) =
      c • cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))) :
    Cor815EigenCollapseAt w := by
  -- Set the bare irregular eigenvector class E := [pollaczekUnit 32].
  set E := cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
    (Additive.ofMul (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)) with hE
  -- Choose the exponent d so that 2 d ≡ c mod 37.
  refine ⟨(c * (2 : ZMod 37)⁻¹).val, ?_⟩
  set d : ℕ := (c * (2 : ZMod 37)⁻¹).val with hd
  -- The corrected unit lies in CPlus.
  have hmem : w * (caseIICor815_W32 ^ d)⁻¹ ∈
      BernoulliRegular.CPlus (p := 37) (K := CyclotomicField 37 ℚ) (by decide) := by
    rw [← caseIIGaloisEigen_caseIICPlus37_eq_CPlus]
    exact caseIICPlus37.mul_mem hw
      (caseIICPlus37.inv_mem (caseIICPlus37.pow_mem caseIICor815_W32_mem d))
  -- Its φ-image vanishes.
  have hφ0 : FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
      (Additive.ofMul (w * (caseIICor815_W32 ^ d)⁻¹)) = 0 := by
    rw [ofMul_mul, map_add, ofMul_inv, ofMul_pow, map_neg, map_nsmul, hres,
      caseIIGaloisEigen_realUnitToFreePartModP_W32, ← hE]
    -- Goal: c • E + -(d • (2 • E)) = 0, i.e. (c - 2 d) • E = 0 with 2 d ≡ c.
    have h2d : ((d : ℕ) : ZMod 37) * 2 = c := by
      rw [hd, ZMod.natCast_val, ZMod.cast_id, mul_assoc,
        inv_mul_cancel₀ (by decide : (2 : ZMod 37) ≠ 0), mul_one]
    -- Convert ℕ-smuls to ZMod 37-smuls and simplify.
    have hcast :
        (d • ((2 : ℕ) • E) : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)) =
        c • E := by
      rw [smul_smul, ← Nat.cast_smul_eq_nsmul (ZMod 37) (d * 2) E]
      rw [show ((d * 2 : ℕ) : ZMod 37) = ((d : ℕ) : ZMod 37) * 2 from by push_cast; ring, h2d]
    rw [hcast, add_neg_cancel]
  -- Apply the kernel-vanishing collapse and flip the equation to the predicate's shape.
  obtain ⟨β, hβ⟩ := caseIIGaloisEigen_isPow37_of_realUnitToFreePartModP_eq_zero
    (w * (caseIICor815_W32 ^ d)⁻¹) hmem hφ0
  exact ⟨β, hβ.symm⟩

/-- **An element of the irregular `ω^{32}`-eigenspace is an `E₃₂`-monomial**
(proven): a class `x ∈ (E_K free)/37` lying in the `ω^{32}`-eigenspace of the
`Δ`-action is a `ZMod 37`-scalar multiple of `[E₃₂] = [pollaczekUnit 32]`.

The `ω^{32}`-eigenspace is one-dimensional
(`cyclotomicUnitFreePartModPDeltaCharacterEigenspace_finrank_of_even_ne_one`,
`ω^{32}` even and non-trivial) and `[E₃₂]` is a nonzero element of it (§B +
the proven all-nonzero certificate), so `[E₃₂]` spans it.  This is the soundness
guard made explicit: membership in the *single irregular* eigenspace — not in all
of `(E_K free)/37` — is what forces the `E₃₂`-monomial form. -/
theorem caseIIGaloisEigen_E32_monomial_of_mem_omega32_eigenspace
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {x : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)}
    (hx : x ∈ cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
      (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32)) :
    ∃ c : ZMod 37, x =
      c • cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)) := by
  letI : Fintype {w : NumberField.InfinitePlace (CyclotomicField 37 ℚ) //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := Fintype.ofFinite _
  letI : DiscreteTopology (NumberField.Units.unitLattice (CyclotomicField 37 ℚ)) :=
    NumberField.Units.instDiscrete_unitLattice (CyclotomicField 37 ℚ)
  letI : IsZLattice ℝ (NumberField.Units.unitLattice (CyclotomicField 37 ℚ)) := by
    refine ⟨?_⟩
    convert NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top (CyclotomicField 37 ℚ)
  -- The eigenspace is 1-dimensional.
  set Eig := cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
    (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32)
  -- [E₃₂] as a member of the eigenspace, nonzero.
  have hE32_mem : cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
      (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
        (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))) ∈ Eig :=
    caseIIGaloisEigen_E32_in_omega32_eigenspace
  set vE : Eig := ⟨_, hE32_mem⟩ with hvE
  have hvE_ne : vE ≠ 0 := by
    rw [hvE, Ne, Submodule.mk_eq_zero]
    exact caseIIGaloisEigen_pollaczekClasses_ne_zero 32 (by decide) (by decide) (by decide)
  -- The eigenspace span of [E₃₂] is ⊤ (1-dim, nonzero spanning vector).
  have hspan : Submodule.span (ZMod 37) ({vE} : Set Eig) = ⊤ := by
    have h_finrank : Module.finrank (ZMod 37) Eig = 1 :=
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace_finrank_of_even_ne_one
        (p := 37) (K := CyclotomicField 37 ℚ) (by decide)
        (cyclotomicOmegaChar_even_of_even (p := 37) 32 (by decide))
        (cyclotomicOmegaChar_ne_one_of_range 32 (by decide) (by decide))
    exact (finrank_eq_one_iff_of_nonzero vE hvE_ne).mp h_finrank
  -- x as a member of the eigenspace lies in span{vE}, hence is a scalar multiple.
  have hx_mem_span : (⟨x, hx⟩ : Eig) ∈ Submodule.span (ZMod 37) ({vE} : Set Eig) := by
    rw [hspan]; exact Submodule.mem_top
  rw [Submodule.mem_span_singleton] at hx_mem_span
  obtain ⟨c, hc⟩ := hx_mem_span
  refine ⟨c, ?_⟩
  -- hc : c • vE = ⟨x, hx⟩, descend to the ambient.
  have := congrArg (Subtype.val) hc
  simpa [hvE, Submodule.coe_smul] using this.symm

/-- **The `ω^{32}`-eigenspace collapse ⟹ `Cor815EigenCollapseAt`** (proven,
axiom-clean, **sound**).

For a real cyclotomic unit `w ∈ C⁺` whose mod-`37` free-part class lies in the
single irregular `ω^{32}`-eigenspace of the Galois `Δ`-action, the eigenspace
predicate `Cor815EigenCollapseAt w` holds.  Composes
`caseIIGaloisEigen_E32_monomial_of_mem_omega32_eigenspace` (eigenspace membership
⟹ `E₃₂`-monomial residue, via the 1-dimensionality of the eigenspace) with
`caseIIGaloisEigen_eigenCollapse_of_E32_monomial_residue` (the kernel-vanishing
collapse).

This is the faithful Washington Corollary 8.15 / Lemma 9.9 statement: the
`37`-residue of a real unit whose class is in the irregular eigenspace is an
`E₃₂`-monomial.  It is **sound** — it applies only to units whose class is in the
single `ω^{32}`-eigenspace, never to all of `C⁺`. -/
theorem caseIIGaloisEigen_eigenCollapse_of_mem_omega32_eigenspace
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (w : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ)
    (hw : w ∈ caseIICPlus37)
    (hmem : FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul w) ∈
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32)) :
    Cor815EigenCollapseAt w := by
  obtain ⟨c, hc⟩ := caseIIGaloisEigen_E32_monomial_of_mem_omega32_eigenspace hmem
  exact caseIIGaloisEigen_eigenCollapse_of_E32_monomial_residue w hw hc

/-! ## (D′) Reducing `Cor815RealDescentData37` to the descent-unit provenance

`Cor815RealDescentData37` bundles, for the descent unit `ε₁/ε₂`, **two** facts:

1. **provenance**: `ε₁/ε₂` is the K-image (`Units.map (algebraMap (𝓞 K⁺) (𝓞 K))`)
   of a *real cyclotomic* unit `w ∈ C⁺` (realness + cyclotomic membership of
   `η_a/η_b`, from the σ-stable `caseII_descent_equation`); and
2. **eigenspace collapse**: `Cor815EigenCollapseAt w` (`w`'s `37`-residue is an
   `E₃₂`-monomial).

The eigenspace-collapse fact (2) is now *proven* from (1) plus the
eigenvalue-indexed hypothesis that `w`'s mod-`37` free-part class is in the
irregular `ω^{32}`-eigenspace — the Galois `Δ`-action eigenvalue collapse §B–§D.
We therefore reduce `Cor815RealDescentData37` to a **reduced provenance Prop**
`Cor815RealDescentProvenance37` carrying only the genuinely-remaining content
(realness/membership of `η_a/η_b` and the `ω^{32}`-eigenspace membership of its
class — the latter being where Lemma 9.8's all-conjugate residue equations enter),
discharging the eigenspace-collapse conjunct via §D. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Reduced descent-unit provenance for Corollary 8.15** (a `def … : Prop`,
**not** an axiom).

For every Case-II descent instance, the quotient unit `ε₁/ε₂` is the K-image of a
real cyclotomic unit `w ∈ C⁺` whose mod-`37` free-part class lies in the single
irregular `ω^{32}`-eigenspace of the Galois `Δ`-action.

Compared with `Cor815RealDescentData37`, the eigenspace-collapse conjunct
`Cor815EigenCollapseAt w` is **dropped** — it is *derived* from the `ω^{32}`-eigenspace
membership via the proven Galois `Δ`-action eigenvalue collapse
(`caseIIGaloisEigen_eigenCollapse_of_mem_omega32_eigenspace`).  What remains here
is exactly:

* the realness + cyclotomic membership of `η_a/η_b` (`w ∈ C⁺`, `Units.map w = ε₁/ε₂`),
  from the σ-stable descent-equation construction; and
* the membership of `w`'s class in the irregular `ω^{32}`-eigenspace, which is the
  content of Washington Lemma 9.8 (the mod-`𝔩` residue equations `η_a/η_b ≡
  (ρ_b/ρ_a)^{37}` over all conjugates `a`) feeding the half-range Vandermonde
  collapse `caseIIThm95_coeff_collapse_even`.

This Prop is **sound** — it asserts eigenspace membership for the *specific*
descent unit, never an `E₃₂`-monomial property of arbitrary `w ∈ C⁺`. -/
def Cor815RealDescentProvenance37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ}
    (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
    ¬ (D.hζ.toInteger - 1) ∣ x' →
    ¬ (D.hζ.toInteger - 1) ∣ y' →
    ¬ (D.hζ.toInteger - 1) ∣ z' →
    ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
    ∃ w ∈ caseIICPlus37,
      (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul w) ∈
        cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32)) ∧
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom w = ε₁ / ε₂

open FLT37.LehmerVandiver.CaseII in
/-- **`Cor815RealDescentData37` from the reduced provenance** (proven, axiom-clean).

The reduced provenance `Cor815RealDescentProvenance37` provides, for each instance,
a real cyclotomic unit `w ∈ C⁺` with `Units.map w = ε₁/ε₂` whose class lies in the
irregular `ω^{32}`-eigenspace.  The eigenspace-collapse conjunct
`Cor815EigenCollapseAt w` of `Cor815RealDescentData37` is then *discharged* by the
proven Galois `Δ`-action eigenvalue collapse
`caseIIGaloisEigen_eigenCollapse_of_mem_omega32_eigenspace`.

Thus the eigenspace-collapse half of Washington Corollary 8.15 / Lemma 9.9 is no
longer an input: the only remaining descent-unit content is the *provenance*
(realness/membership of `η_a/η_b` and the `ω^{32}`-eigenspace membership of its
class — Lemma 9.8's all-conjugate residue equations). -/
theorem caseIIGaloisEigen_realDescentData_of_provenance
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_prov : Cor815RealDescentProvenance37) :
    Cor815RealDescentData37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  obtain ⟨w, hw_mem, hw_eig, hw_eq⟩ := h_prov hV hSO D hx hy hz heq
  exact ⟨w, hw_mem,
    caseIIGaloisEigen_eigenCollapse_of_mem_omega32_eigenspace w hw_mem hw_eig, hw_eq⟩

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II from the reduced provenance + Lemma 9.8**, with both
`SinnottIndexFormula 37` (step A) and the eigenspace-collapse (§B–§D) discharged
(proven, axiom-clean).

This is the cleanest statement of the remaining Case-II content for `p = 37`:
**Assumption II** (`WashingtonCaseIIExactQuotientUnitPower37Source`) — and hence the
entire Theorem-9.5 Case-II descent, modulo the proven σ-stable adjacent-generator
producer — follows from the *two* precisely-named inputs

* `Cor815RealDescentProvenance37` — the descent-unit *provenance* (realness +
  cyclotomic membership of `η_a/η_b`, and the `ω^{32}`-eigenspace membership of
  its class); and
* `Lemma98LocalPower37` — Washington Lemma 9.8's mod-`𝔩` Kummer congruence.

Everything else is *proven* here: the analytic `SinnottIndexFormula 37` (step A),
the Galois `Δ`-action eigenvalue eigenspace collapse (§B–§D), the
saturation/torsion core, and the index/Vandermonde collapse. -/
theorem caseIIGaloisEigen_assumptionII_of_provenance
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_prov : Cor815RealDescentProvenance37)
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIGaloisEigen_assumptionII_of_reduced_inputs
    (caseIIGaloisEigen_realDescentData_of_provenance h_prov) h_localPow

end BernoulliRegular.FLT37.Eichler

end
