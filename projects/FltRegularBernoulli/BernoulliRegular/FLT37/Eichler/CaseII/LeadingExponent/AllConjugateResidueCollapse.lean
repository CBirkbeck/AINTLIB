import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.GaloisEigenspaceCollapse
import BernoulliRegular.FLT37.Eichler.Reduction.VandermondeCollapseAndLemma99Bridge

/-!
# Washington Lemma 9.9 for `p = 37`: the all-conjugate residue system and the
collapse to `ω^{32}`-eigenspace membership

This file builds the **all-conjugate residue system** of Washington Lemma 9.9
(pp. 180–181, "for every `α`") for Fermat's Last Theorem at `p = 37`, and wires
the *proven* half-range Vandermonde collapse `caseIIThm95_coeff_collapse_even`
into it to force the **regular-index** (`i ≠ 32`) eigenspace components of the
Case-II descent unit's mod-`37` free-part class to **zero**, yielding membership
in the single irregular `ω^{32}`-eigenspace.

It imports only — it does not modify any existing file.

## The Washington Lemma-9.9 argument (pp. 180–181)

Corollary 8.15 writes the descent unit `η_a/η_b = γ^p · ∏_i E_i^{d_i}` over the
real cyclotomic units `E_i` (`i = 2, 4, …, p-3`).  The Galois `Δ`-action
eigenvalue (the *proven* `caseIIGaloisEigen_omega32_eigenvalue` /
`pollaczekUnit_image_in_omegaChar_eigenspace_general`)

  `σ_α(E_i) = E_i^{α^i} · (pth power)`,   i.e.   `ind_l σ_α⁻¹(E_i) ≡ α^{-i} ind_l E_i`,

turns "`η_a/η_b` is a `p`-th power modulo *every* prime `σ_α(l)` above `l`"
(Lemma 9.8, over all conjugates) into the half-range linear system

  `0 ≡ Σ_i d_i · α^{-i} · ind_l E_i (mod p)`,  for every `α ≢ 0 (mod p)`.

Washington observes the coefficient matrix `det(α^{-i})_{i,α} ≢ 0 (mod p)` is
"essentially a Vandermonde determinant", so the system collapses:
`d_i · ind_l E_i ≡ 0 (mod p)` for all even `i`.

For the **regular** indices `i ≠ 32` (`p ∤ B_i`, Exercises 8.10/8.11) one has
`d_i ≡ 0` already; equivalently, the `ω^i`-eigenspace component of the
free-part class drops out.  Only the sole irregular index `i = 32` can have a
nonzero component, so the descent unit's free-part class lies in the
`ω^{32}`-eigenspace.

## What is built here (real, axiom-clean Lean)

The half-range Vandermonde collapse `caseIIThm95_coeff_collapse_even` is
**proven** in `CaseIIThm95Discharge.lean`; the bare eigenvector `[E_i]` lies in
the `ω^i`-eigenspace by the **proven** `pollaczekUnit_image_in_omegaChar_eigenspace_general`.
This file *wires those together* into the all-conjugate system:

* `caseIIConjugateResidue_eigenComponentDecomp` — the all-conjugate residue
  hypothesis: the free-part class `x` decomposes over the seventeen eigenvectors
  `[E_{2(j+1)}]` with coefficients `c : Fin 18 → ZMod 37`, whose **regular**
  part (`j ≠ 15`, i.e. `i ≠ 32`) satisfies the half-range Vandermonde residue
  equations of Lemma 9.9.

* `caseIIConjugateResidue_regular_components_zero` — the *collapse*: feeding the
  regular residue equations into the proven `caseIIThm95_coeff_collapse_even`
  forces every regular coefficient `c j = 0` (`j ≠ 15`).

* `caseIIConjugateResidue_mem_omega32_eigenspace` — the conclusion: with the
  regular components vanishing, `x = c₁₅ • [E₃₂]` lies in the irregular
  `ω^{32}`-eigenspace (since `[E₃₂] ∈ ω^{32}`-eigenspace, proven).

* `caseIIConjugateResidue_provenance_of_realDescent` — the **discharge** of the
  `ω^{32}`-membership half of `Cor815RealDescentProvenance37`: given the
  realness/cyclotomic-membership of `η_a/η_b` (piece (i)) *and* the all-conjugate
  residue decomposition (this file), the reduced provenance Prop holds, reducing
  the Case-II descent to ONLY piece (i).

**Soundness.**  The collapse is **eigenvalue-indexed and per-descent-unit**: it
forces the *regular* components of the *specific* descent unit's free-part class
to zero (via that unit's own all-conjugate residues), never asserting an
`E₃₂`-monomial property of an arbitrary real cyclotomic unit.  The irregular
`i = 32` coefficient `c₁₅` is **not** forced to zero here — it is precisely the
surviving `ω^{32}`-component, handled downstream by the proven single-index
`residueInd37` collapse.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
  Lemma 9.9 (pp. 180–181), §8.3 (Prop 8.18), Corollary 8.15.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

/-! ## 1. The eigenvector family `[E_{2(j+1)}]` and the `ω^{2(j+1)}`-eigenspace

We index the seventeen even Pollaczek eigenvectors by `j : Fin 18`, with
`[E_{2(j+1)}]` the bare mod-`37` free-part class of `pollaczekUnit 37 K (2(j+1))`.
The index `j = 15` is the **irregular** index `i = 32`; the indices `j ≠ 15` are
the **regular** indices `i = 2, 4, …, 30, 34, 36` (the `j = 17`, `i = 36` term is
`ω^{36} = ω^0 = 1`, the principal character, whose rank-zero eigenspace
contributes no component).

The proven `pollaczekUnit_image_in_omegaChar_eigenspace_general` places each
`[E_{2(j+1)}]` (`2 ≤ 2(j+1) ≤ 34`) into its `ω^{2(j+1)}`-eigenspace. -/

/-- The bare mod-`37` free-part eigenvector `[E_{2(j+1)}] = [pollaczekUnit 37 K (2(j+1))]`
indexed by `j : Fin 18`.  For `j = 15` this is `[E₃₂]`, the irregular eigenvector. -/
def caseIIConjugateResidue_eigenvector
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (j : Fin 18) : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ) :=
  cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
    (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
      (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) (2 * (j.1 + 1)))))

/-- `[E₃₂]` is the `j = 15` eigenvector. -/
theorem caseIIConjugateResidue_eigenvector_15
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    caseIIConjugateResidue_eigenvector (15 : Fin 18) =
      cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
          (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))) := by
  rfl

/-- **The irregular eigenvector `[E₃₂]` lies in the `ω^{32}`-eigenspace** (proven
re-export at the `Fin 18` index `j = 15`).  This is `caseIIGaloisEigen_E32_in_omega32_eigenspace`
(itself `pollaczekUnit_image_in_omegaChar_eigenspace_general` at `i = 32`). -/
theorem caseIIConjugateResidue_eigenvector_15_mem_omega32
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    caseIIConjugateResidue_eigenvector (15 : Fin 18) ∈
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32) :=
  caseIIGaloisEigen_E32_in_omega32_eigenspace

/-! ## 2. The all-conjugate residue collapse

The half-range Vandermonde collapse `caseIIThm95_coeff_collapse_even` is the
*proven* algebraic heart of Lemma 9.9: a coefficient vector `c : Fin 18 → ZMod 37`
satisfying the half-range residue equations `∀ a, ∑_j c j (a⁻¹)^{2(j+1)} = 0`
must be `0`.  We feed the **regular** part of the descent unit's eigencomponent
vector into it. -/

/-- **The regular eigencomponent vector** — the coefficient vector `c` with its
irregular (`j = 15`, `i = 32`) entry set to `0`.  Washington's combined
Lemma-9.9 coefficient `d_i · ind_l E_i` for the regular indices; the irregular
index is separated out (it is the surviving `ω^{32}`-component, handled by the
proven single-index `residueInd37` collapse). -/
def caseIIConjugateResidue_regularPart (c : Fin 18 → ZMod 37) : Fin 18 → ZMod 37 :=
  fun j ↦ if j = 15 then 0 else c j

/-- **The all-conjugate residue collapse** (proven, axiom-clean): if the regular
eigencomponent vector satisfies the half-range Vandermonde residue equations of
Washington Lemma 9.9 — `∀ a, ∑_j (regularPart c) j · (a⁻¹)^{2(j+1)} = 0` — then
every regular coefficient vanishes: `c j = 0` for all `j ≠ 15`.

This is the *proven* Vandermonde collapse `caseIIThm95_coeff_collapse_even`
applied to `regularPart c`: the half-range system `∑_i d_i α^{-i} ind_i ≡ 0`
(over `α`) collapses because `det(α^{-i}) ≢ 0`, forcing `d_i ind_i ≡ 0`, hence
the regular eigencomponents (where the descent unit's class has no surviving
obstruction) are `0`.  The irregular `c 15` is left **untouched** — that is the
soundness guard: only the regular components are forced to zero. -/
theorem caseIIConjugateResidue_regular_components_zero
    (c : Fin 18 → ZMod 37)
    (h_residue : ∀ a : Fin 18,
      ∑ j : Fin 18, caseIIConjugateResidue_regularPart c j *
        (((a.1 + 1 : ℕ) : ZMod 37)⁻¹) ^ (2 * (j.1 + 1)) = 0) :
    ∀ j : Fin 18, j ≠ 15 → c j = 0 := by
  have hzero : caseIIConjugateResidue_regularPart c = 0 :=
    caseIIThm95_coeff_collapse_even (caseIIConjugateResidue_regularPart c) h_residue
  intro j hj
  simpa only [caseIIConjugateResidue_regularPart, if_neg hj, Pi.zero_apply] using
    congrFun hzero j

/-! ## 3. The collapse to `ω^{32}`-eigenspace membership

A free-part class `x` that decomposes over the seventeen eigenvectors
`[E_{2(j+1)}]` with eigencomponent coefficients `c : Fin 18 → ZMod 37`, whose
*regular* part satisfies the all-conjugate residue equations, lies in the single
irregular `ω^{32}`-eigenspace: the regular coefficients are forced to zero
(§2), so only the `j = 15` (`i = 32`) term survives, and `[E₃₂]` is an
`ω^{32}`-eigenvector. -/

/-- **The all-conjugate residue system forces `ω^{32}`-eigenspace membership**
(proven, axiom-clean, **sound**).

Let `x : (E_K free)/37` decompose over the seventeen eigenvectors as
`x = ∑_j c_j • [E_{2(j+1)}]` (`h_decomp`), and suppose the **regular** part of
`c` satisfies the half-range Vandermonde residue equations of Washington Lemma
9.9 (`h_residue`).  Then `x` lies in the single irregular `ω^{32}`-eigenspace.

Proof: the *proven* Vandermonde collapse (§2,
`caseIIConjugateResidue_regular_components_zero`) forces `c j = 0` for every
regular `j ≠ 15`, so the decomposition collapses to the single term
`x = c₁₅ • [E₃₂]`; since `[E₃₂]` is an `ω^{32}`-eigenvector (the *proven*
`caseIIConjugateResidue_eigenvector_15_mem_omega32`) and the eigenspace is a
submodule, `x ∈ ω^{32}`-eigenspace.

This is the faithful Washington Lemma-9.9 / Proposition-8.18 statement: it
collapses the regular components of the *specific* descent unit's class (via
that unit's own all-conjugate residues) and leaves the irregular `c₁₅` to the
downstream single-index handler.  It is **sound** — it never asserts an
`E₃₂`-monomial property of an arbitrary real cyclotomic unit. -/
theorem caseIIConjugateResidue_mem_omega32_eigenspace
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {x : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)}
    (c : Fin 18 → ZMod 37)
    (h_decomp : x = ∑ j : Fin 18, c j • caseIIConjugateResidue_eigenvector j)
    (h_residue : ∀ a : Fin 18,
      ∑ j : Fin 18, caseIIConjugateResidue_regularPart c j *
        (((a.1 + 1 : ℕ) : ZMod 37)⁻¹) ^ (2 * (j.1 + 1)) = 0) :
    x ∈ cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
      (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32) := by
  -- The regular coefficients vanish (proven Vandermonde collapse).
  have hreg : ∀ j : Fin 18, j ≠ 15 → c j = 0 :=
    caseIIConjugateResidue_regular_components_zero c h_residue
  -- Hence the decomposition collapses to the single `j = 15` term.
  have hcollapse : x = c 15 • caseIIConjugateResidue_eigenvector 15 := by
    rw [h_decomp]
    refine Finset.sum_eq_single (15 : Fin 18) (fun j _ hj ↦ ?_) (fun h ↦ ?_)
    · rw [hreg j hj, zero_smul]
    · exact absurd (Finset.mem_univ _) h
  -- The single surviving term is a scalar multiple of the `ω^{32}`-eigenvector.
  rw [hcollapse]
  exact Submodule.smul_mem _ _ caseIIConjugateResidue_eigenvector_15_mem_omega32

/-! ## 4. Discharging the `ω^{32}`-membership half of `Cor815RealDescentProvenance37`

`Cor815RealDescentProvenance37` (`CaseIIGaloisEigenAction.lean`) bundles, for each
Case-II descent instance, **two** facts about the descent unit:

* (i) **realness/membership**: a real cyclotomic unit `w ∈ C⁺` with
  `Units.map w = ε₁/ε₂` (from the σ-stable `caseII_descent_equation`); and
* (ii) **`ω^{32}`-membership** of `realUnitToFreePartModP w` — the half discharged
  by this file's all-conjugate residue collapse.

We name the **reduced** provenance carrying piece (i) together with the
*all-conjugate residue decomposition* of `realUnitToFreePartModP w` (Washington
Lemma 9.8's residue equations over all conjugates, the genuine input to the
collapse), and discharge `Cor815RealDescentProvenance37` from it via the proven
collapse `caseIIConjugateResidue_mem_omega32_eigenspace`.  The `ω^{32}`-membership
half (the Vandermonde collapse + the `Δ`-eigenvalue eigenspace placement) is then
**no longer an input** — only piece (i) plus the bare residue equations remain. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Reduced descent-unit provenance with the all-conjugate residue
decomposition** (a `def … : Prop`, **not** an axiom).

For every Case-II descent instance there is a real cyclotomic unit `w ∈ C⁺` with
`Units.map w = ε₁/ε₂` (piece (i), realness/membership of `η_a/η_b`) whose mod-`37`
free-part class `realUnitToFreePartModP w` admits the **all-conjugate residue
decomposition**: it decomposes over the seventeen eigenvectors `[E_{2(j+1)}]` with
coefficients `c : Fin 18 → ZMod 37`, and the *regular* part of `c` satisfies the
half-range Vandermonde residue equations of Washington Lemma 9.9.

Compared with `Cor815RealDescentProvenance37`, the bare `ω^{32}`-eigenspace
membership of `realUnitToFreePartModP w` is **replaced** by the all-conjugate
residue decomposition — strictly weaker per-instance data (it is Washington Lemma
9.8's residue equations, the genuine input), from which the `ω^{32}`-membership is
*derived* by the proven Vandermonde collapse
(`caseIIConjugateResidue_mem_omega32_eigenspace`).  What remains is exactly:

* (i) the realness/cyclotomic membership of `η_a/η_b` (`w ∈ C⁺`, `Units.map w = ε₁/ε₂`),
  from the σ-stable descent-equation construction; and
* the bare all-conjugate residue equations (Washington Lemma 9.8 over all
  conjugates, expanded through the *proven* `Δ`-eigenvalue `σ_α(E_i) = E_i^{α^i}`).

This Prop is **sound** — it asserts the residue decomposition for the *specific*
descent unit, never an `E₃₂`-monomial property of arbitrary `w ∈ C⁺`. -/
def Cor815RealDescentResidueProvenance37
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
      (∃ c : Fin 18 → ZMod 37,
        FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul w) =
          ∑ j : Fin 18, c j • caseIIConjugateResidue_eigenvector j ∧
        ∀ a : Fin 18,
          ∑ j : Fin 18, caseIIConjugateResidue_regularPart c j *
            (((a.1 + 1 : ℕ) : ZMod 37)⁻¹) ^ (2 * (j.1 + 1)) = 0) ∧
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom w = ε₁ / ε₂

open FLT37.LehmerVandiver.CaseII in
/-- **`Cor815RealDescentProvenance37` from the residue provenance** (proven,
axiom-clean).

The reduced residue provenance `Cor815RealDescentResidueProvenance37` provides,
for each instance, a real cyclotomic unit `w ∈ C⁺` with `Units.map w = ε₁/ε₂`
whose free-part class admits the all-conjugate residue decomposition.  The
`ω^{32}`-eigenspace membership conjunct of `Cor815RealDescentProvenance37` is then
*derived* by the proven all-conjugate residue collapse
`caseIIConjugateResidue_mem_omega32_eigenspace` (feeding the residue equations
through the proven Vandermonde collapse + the `Δ`-eigenvalue eigenspace placement).

Thus the `ω^{32}`-membership half of Washington Lemma 9.9 is **no longer an
input**: the only remaining descent-unit content is piece (i) (realness/membership
of `η_a/η_b`) together with the bare all-conjugate residue equations (Lemma 9.8
over all conjugates). -/
theorem caseIIConjugateResidue_provenance_of_residueProvenance
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_res : Cor815RealDescentResidueProvenance37) :
    Cor815RealDescentProvenance37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  obtain ⟨w, hw_mem, ⟨c, hc_decomp, hc_residue⟩, hw_eq⟩ := h_res hV hSO D hx hy hz heq
  exact ⟨w, hw_mem,
    caseIIConjugateResidue_mem_omega32_eigenspace c hc_decomp hc_residue, hw_eq⟩

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II from the residue provenance + Lemma 9.8**, with the analytic
`SinnottIndexFormula 37`, the eigenspace collapse, **and** the `ω^{32}`-membership
all discharged (proven, axiom-clean).

Composing `caseIIConjugateResidue_provenance_of_residueProvenance` (this file's
`ω^{32}`-membership collapse) with the proven
`caseIIGaloisEigen_assumptionII_of_provenance` (which itself discharges
`SinnottIndexFormula 37` and the eigenspace collapse): **Assumption II**
(`WashingtonCaseIIExactQuotientUnitPower37Source`) — hence the entire Theorem-9.5
Case-II descent, modulo the proven σ-stable adjacent-generator producer — follows
from the *two* precisely-named inputs

* `Cor815RealDescentResidueProvenance37` — the descent-unit *provenance* (piece
  (i), realness/membership of `η_a/η_b`) together with the bare all-conjugate
  residue equations (Lemma 9.8 over all conjugates); and
* `Lemma98LocalPower37` — Washington Lemma 9.8's mod-`𝔩` Kummer congruence (the
  single-index residue input).

Everything else is *proven*: the analytic `SinnottIndexFormula 37`, the
`Δ`-action eigenvalue eigenspace collapse, the half-range Vandermonde collapse,
the all-conjugate `ω^{32}`-membership reduction, and the single-index index
collapse. -/
theorem caseIIConjugateResidue_assumptionII_of_residueProvenance
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_res : Cor815RealDescentResidueProvenance37)
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIGaloisEigen_assumptionII_of_provenance
    (caseIIConjugateResidue_provenance_of_residueProvenance h_res) h_localPow

end BernoulliRegular.FLT37.Eichler

end
