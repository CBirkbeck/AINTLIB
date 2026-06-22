import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.AllConjugateResidueCollapse

/-!
# Washington Lemma 9.9 for `p = 37`: the eigencomponent decomposition is automatic, and the
descent-unit residue provenance reduced to its two genuine inputs

This file makes the final residue-data reduction for Fermat's Last Theorem at `p = 37`.  It
imports only — it does not modify any existing file.

## What `Cor815RealDescentResidueProvenance37` requires

`Cor815RealDescentResidueProvenance37` (`CaseIIConjugateResidue.lean`) is the most-reduced named
hypothesis at the bottom of the *fully proven* Case-II `ω^{32}`-collapse engine.  For every
Case-II descent instance it asks for a real cyclotomic unit `w ∈ C⁺` with

* **(i) realness/membership** — `Units.map (algebraMap 𝓞K⁺ 𝓞K) w = ε₁/ε₂` (Washington §9.1: the
  descent unit `η_a/η_b` is real, with `ρ_a ρ̄_a` σ-fixed); and
* **(ii) the all-conjugate residue data** — `∃ c : Fin 18 → ZMod 37` with
  `realUnitToFreePartModP w = ∑_j c_j • [E_{2(j+1)}]` **and** the half-range Vandermonde residue
  equations `∀ a, ∑_j (regularPart c)_j · (a⁻¹)^{2(j+1)} = 0` (Washington Lemma 9.8 over all
  conjugates, routed through the proven `Δ`-eigenvalue).

Everything downstream of these two facts — the half-range Vandermonde collapse
(`caseIIThm95_coeff_collapse_even`), the `Δ`-action eigenspace placement
(`caseIIGaloisEigen_omega32_eigenvalue`), the `ω^{32}`-membership reduction
(`caseIIConjugateResidue_mem_omega32_eigenspace`), the single-index `residueInd37` collapse, the
analytic `SinnottIndexFormula 37`, and the proven `37 ∤ h⁺` — is **proven**.

## What this file proves (real, axiom-clean Lean)

The genuine forward progress is that **the eigencomponent decomposition of (ii) is automatic** —
it is *not* open content.  The seventeen bare even Pollaczek classes `[E_{2(k+1)}]` (`k : Fin 17`,
`i = 2, 4, …, 34`) **span** the whole mod-`37` free part `(E_K free)/37` — this is the *proven*
`pollaczekUnit_image_span_eq_top` together with the *proven* all-nonzero certificate
`caseIIGaloisEigen_pollaczekClasses_ne_zero` (the same data that proves Vandiver for `37`).  Hence:

* `caseIIResidueProvenance_exists_decomp` — **every** free-part class `x` decomposes over the
  `Fin 18`-indexed eigenvectors `[E_{2(j+1)}]` as `x = ∑_j c_j • [E_{2(j+1)}]` (with `c_{17} = 0`,
  the `j = 17`, `i = 36 = ω^0` principal-character term carrying no component).

This discharges the *existence of the decomposition* conjunct of
`Cor815RealDescentResidueProvenance37` outright, leaving as the only descent-unit inputs:

* **(i)** the realness/membership of `η_a/η_b` (Washington §9.1), and
* **(ii′)** the bare half-range residue equations of Lemma 9.8 (over all conjugates), now stated on
  the canonically-existing decomposition.

We name this strictly-smaller hypothesis `Cor815RealDescentResidueDataProvenance37` and prove

* `caseIIResidueProvenance_provenance_of_residueData` —
  `Cor815RealDescentResidueDataProvenance37 ⟹ Cor815RealDescentResidueProvenance37`
  (the decomposition existence is supplied by `caseIIResidueProvenance_exists_decomp`); and
* `caseIIResidueProvenance_assumptionII_of_residueData` — composing with the proven engine,
  `Cor815RealDescentResidueDataProvenance37 + Lemma98LocalPower37 ⟹` **Assumption II**
  (`WashingtonCaseIIExactQuotientUnitPower37Source`).

## The two genuinely remaining inputs (precisely, with Washington source)

After this file the *entire* Case-II II2 content for `p = 37` is the pair

* `Cor815RealDescentResidueDataProvenance37` — Washington §9.1 realness of `η_a/η_b`
  (`Introduction to Cyclotomic Fields`, 2nd ed., GTM 83, §9.1, the construction
  `η_a = (ω_j + ζ^a ω_j)/(1 - ζ^a)` and its complex-conjugate pairing) **plus** the bare
  all-conjugate residue equations of **Lemma 9.8** (p. 180, `η_a/η_b ≡ (ρ_b/ρ_a)^p (mod 𝔩)`, taken
  over every conjugate `σ_α(𝔩)`); and
* `Lemma98LocalPower37` — the single-index mod-`𝔩` Kummer congruence of Lemma 9.8.

The σ-stable pair-product producer `caseII_sigmaPairAnchoredSource_proven` supplies a *norm*
`K → K⁺` whose valuations **double** (it is the conjugate-pair product `𝔞(η)𝔞(η⁻¹)`), so it
realises the σ-stable adjacent-generator source `WashingtonCaseIIAdjacentFixedGenerators37Source`
but does **not**, by itself, present `ε₁/ε₂` as a *single* real cyclotomic unit at measure `< m` —
that identification is the Washington §9.1 reformulation in (i), which is carried as the named
input above.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (descent unit `η_a`),
  Lemma 9.8 (p. 180), Lemma 9.9 (pp. 180–181), Corollary 8.15, §8.3.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

/-! ## 1. The eigencomponent decomposition is automatic

The seventeen bare even Pollaczek classes `[E_{2(k+1)}]` (`k : Fin 17`) span the whole mod-`37`
free part `(E_K free)/37` (*proven* `pollaczekUnit_image_span_eq_top` under the *proven*
all-nonzero certificate `caseIIGaloisEigen_pollaczekClasses_ne_zero`).  Indexing them by
`j : Fin 18` (with `j = 17`, `i = 36 = ω^0`, the principal-character term carrying no component),
every free-part class decomposes over the eigenvectors `caseIIConjugateResidue_eigenvector`. -/

/-- **The `Fin 18` eigenvector at an index `< 17` is the corresponding span-family member.**
`caseIIConjugateResidue_eigenvector j` (for `j : Fin 18`) is by definition the mod-`37` free-part
class of `pollaczekUnit 37 K (2(j.1+1))`; for `j.1 = k.1` with `k : Fin 17` this is the `k`-th
member of the spanning family `fun k : Fin 17 ↦ [pollaczekUnit 37 K (2k+2)]` of
`pollaczekUnit_image_span_eq_top`, since `2(j.1+1) = 2·k.1 + 2`. -/
theorem caseIIResidueProvenance_eigenvector_castSucc
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (k : Fin 17) :
    caseIIConjugateResidue_eigenvector (Fin.castLE (by norm_num) k) =
      cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
          (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) (2 * (k : ℕ) + 2)))) := by
  unfold caseIIConjugateResidue_eigenvector
  congr 2

/-- **Every free-part class decomposes over the `Fin 18` eigenvectors** (proven, axiom-clean).

For any `x : (E_K free)/37` there is `c : Fin 18 → ZMod 37` with
`x = ∑_j c_j • [E_{2(j+1)}]` and the principal-character coefficient `c 17 = 0`.

Proof: the seventeen bare even Pollaczek classes span `⊤` (the *proven*
`pollaczekUnit_image_span_eq_top`, applied with the *proven* all-nonzero certificate
`caseIIGaloisEigen_pollaczekClasses_ne_zero`), so `Submodule.mem_span_range_iff_exists_fun`
gives a `Fin 17` coefficient family; extend it to `Fin 18` by `0` at `j = 17`.  This shows the
*existence-of-decomposition* conjunct of `Cor815RealDescentResidueProvenance37` is **not** open
content. -/
theorem caseIIResidueProvenance_exists_decomp
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (x : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)) :
    ∃ c : Fin 18 → ZMod 37,
      x = ∑ j : Fin 18, c j • caseIIConjugateResidue_eigenvector j ∧ c 17 = 0 := by
  have : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- The seventeen bare classes span `⊤`, so `x` is a `Fin 17`-combination of them.
  have hspan := pollaczekUnit_image_span_eq_top (K := CyclotomicField 37 ℚ)
    caseIIGaloisEigen_pollaczekClasses_ne_zero
  have hx : x ∈ Submodule.span (ZMod 37) (Set.range (fun k : Fin 17 ↦
      cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
          (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) (2 * (k : ℕ) + 2)))))) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c17, hc17⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hx
  -- Extend the `Fin 17` family by `0` at `j = 17`.
  refine ⟨fun j ↦ if h : (j : ℕ) < 17 then c17 ⟨j, h⟩ else 0, ?_, ?_⟩
  · -- The `Fin 18` RHS sum collapses to the `Fin 17` sum, which is `x` by `hc17`.
    symm
    rw [Fin.sum_univ_castSucc]
    -- The last (`j = 17`) term vanishes: `(Fin.last 17).1 = 17`, so the dite picks the `0` branch.
    have hlast : (if h : ((Fin.last 17 : Fin 18) : ℕ) < 17 then c17 ⟨Fin.last 17, h⟩
          else (0 : ZMod 37)) • caseIIConjugateResidue_eigenvector (Fin.last 17) = 0 := by
      rw [dif_neg (by rw [Fin.val_last]; exact lt_irrefl 17), zero_smul]
    rw [hlast, add_zero, ← hc17]
    -- The first seventeen block terms match the span-family combination, term by term.
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    beta_reduce
    have hcoeff : (if h : ((Fin.castSucc k : Fin 18) : ℕ) < 17 then
          c17 ⟨Fin.castSucc k, h⟩ else (0 : ZMod 37)) = c17 k := by
      rw [dif_pos (by rw [Fin.val_castSucc]; exact k.2)]
      congr 1
    have heig : caseIIConjugateResidue_eigenvector (Fin.castSucc k) =
        cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
          (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
            (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) (2 * (k : ℕ) + 2)))) := by
      unfold caseIIConjugateResidue_eigenvector
      congr 2
    rw [hcoeff, heig]
  · -- `c 17 = 0`: `(17 : Fin 18).1 = 17`, and `17 < 17` is false.
    have h17 : ((17 : Fin 18) : ℕ) = 17 := by decide
    simp only [h17, lt_irrefl, dif_neg, not_false_iff]

/-! ## 2. The canonical eigencomponent decomposition

Decompositions of a free-part class over the **seventeen** eigenvectors `[E_{2(j+1)}]`
(`j = 0, …, 16`, i.e. with the principal-character coefficient `c 17 = 0`) are **unique** — those
seventeen vectors are linearly independent (`pollaczekUnit_image_linearIndependent` under the
proven all-nonzero certificate) and span `⊤`, hence form a basis of `(E_K free)/37`.  So the
`c_17 = 0` decomposition produced by `caseIIResidueProvenance_exists_decomp` is canonical; we
extract it by choice and name it `caseIIResidueProvenance_decomp`.  This is the decomposition over
which Washington Lemma 9.8 supplies the residue equations (its `d_i · ind_l E_i` are exactly the
seventeen-basis eigencomponents). -/

/-- **The canonical eigencomponent decomposition coefficients of a free-part class.**  The unique
`c : Fin 18 → ZMod 37` with `c 17 = 0` and `x = ∑_j c_j • [E_{2(j+1)}]`, extracted from the proven
`caseIIResidueProvenance_exists_decomp` by choice.  (Uniqueness among `c 17 = 0` decompositions is
the seventeen-vector basis property; only existence is needed below.) -/
def caseIIResidueProvenance_decomp
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (x : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)) : Fin 18 → ZMod 37 :=
  Classical.choose (caseIIResidueProvenance_exists_decomp x)

/-- **The canonical decomposition reproduces `x`** (choice spec). -/
theorem caseIIResidueProvenance_decomp_spec
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (x : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)) :
    x = ∑ j : Fin 18, caseIIResidueProvenance_decomp x j • caseIIConjugateResidue_eigenvector j :=
  (Classical.choose_spec (caseIIResidueProvenance_exists_decomp x)).1

/-- **The canonical decomposition has vanishing principal-character coefficient** (choice spec). -/
theorem caseIIResidueProvenance_decomp_principal_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (x : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)) :
    caseIIResidueProvenance_decomp x 17 = 0 :=
  (Classical.choose_spec (caseIIResidueProvenance_exists_decomp x)).2

/-! ## 3. The descent-unit residue provenance reduced to realness + the bare Lemma-9.8 equations

`Cor815RealDescentResidueProvenance37` asks, for each Case-II descent instance, for a real
cyclotomic unit `w ∈ C⁺` with `Units.map w = ε₁/ε₂` **and** an eigencomponent decomposition `c`
of `realUnitToFreePartModP w` satisfying the half-range Vandermonde residue equations.

Since the decomposition is now *automatic* (§1–§2), we name the strictly-smaller hypothesis that
carries only

* **(i)** the realness/cyclotomic membership of `η_a/η_b` (`w ∈ C⁺`, `Units.map w = ε₁/ε₂`,
  Washington §9.1); and
* **(ii′)** the bare half-range residue equations of Washington Lemma 9.8 (over all conjugates),
  stated on the *canonical* decomposition
  `caseIIResidueProvenance_decomp (realUnitToFreePartModP w)`.

The decomposition itself is no longer an input — it is supplied by the proven
`caseIIResidueProvenance_decomp_spec`. -/

open FLT37.LehmerVandiver.CaseII in
/-- **Reduced descent-unit residue provenance** (a `def … : Prop`, **not** an axiom).

For every Case-II descent instance there is a real cyclotomic unit `w ∈ C⁺` with
`Units.map w = ε₁/ε₂` (piece (i), Washington §9.1) whose canonical mod-`37` free-part eigencomponent
vector `c = caseIIResidueProvenance_decomp (realUnitToFreePartModP w)` satisfies the half-range
Vandermonde residue equations of Washington Lemma 9.8 over all conjugates
(`∀ a, ∑_j (regularPart c)_j · (a⁻¹)^{2(j+1)} = 0`).

Compared with `Cor815RealDescentResidueProvenance37`, the existence of the eigencomponent
decomposition is **dropped** — it is *proven* automatic (`caseIIResidueProvenance_decomp_spec`,
from the seventeen-eigenvector spanning `pollaczekUnit_image_span_eq_top` under the proven
all-nonzero certificate).  What remains is exactly the two genuine descent-unit inputs: piece (i)
realness, and the bare Lemma-9.8 residue equations.

This Prop is **sound** — it asserts the residue equations for the *specific* descent unit's
canonical eigencomponents, never an `E₃₂`-monomial property of an arbitrary real cyclotomic unit. -/
def Cor815RealDescentResidueDataProvenance37
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
      (∀ a : Fin 18,
        ∑ j : Fin 18, caseIIConjugateResidue_regularPart
            (caseIIResidueProvenance_decomp
              (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul w))) j *
          (((a.1 + 1 : ℕ) : ZMod 37)⁻¹) ^ (2 * (j.1 + 1)) = 0) ∧
      Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom w = ε₁ / ε₂

/-- **`Cor815RealDescentResidueProvenance37` from the reduced residue-data provenance** (proven,
axiom-clean).

The reduced provenance `Cor815RealDescentResidueDataProvenance37` supplies, for each instance, a
real cyclotomic unit `w ∈ C⁺` with `Units.map w = ε₁/ε₂` whose canonical eigencomponent vector
satisfies the half-range residue equations.  The eigencomponent *decomposition* conjunct of
`Cor815RealDescentResidueProvenance37` is then supplied by the proven automatic decomposition
`caseIIResidueProvenance_decomp_spec` (the seventeen-eigenvector spanning).

Thus the existence of the eigencomponent decomposition is **no longer an input**: the only
remaining descent-unit content is piece (i) (realness/membership of `η_a/η_b`, Washington §9.1)
together with the bare all-conjugate residue equations (Washington Lemma 9.8). -/
theorem caseIIResidueProvenance_provenance_of_residueData
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_data : Cor815RealDescentResidueDataProvenance37) :
    Cor815RealDescentResidueProvenance37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx hy hz heq
  obtain ⟨w, hw_mem, hc_residue, hw_eq⟩ := h_data hV hSO D hx hy hz heq
  exact ⟨w, hw_mem,
    ⟨caseIIResidueProvenance_decomp
        (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul w)),
      caseIIResidueProvenance_decomp_spec _, hc_residue⟩,
    hw_eq⟩

/-- **Assumption II from the reduced residue-data provenance + Lemma 9.8** (proven, axiom-clean).

Composing `caseIIResidueProvenance_provenance_of_residueData` (this file's automatic-decomposition
reduction) with the proven `caseIIConjugateResidue_assumptionII_of_residueProvenance`: **Assumption
II** (`WashingtonCaseIIExactQuotientUnitPower37Source`) — hence the entire Theorem-9.5 Case-II
descent, modulo the proven σ-stable adjacent-generator producer
(`caseII_sigmaPairAnchoredSource_proven`) — follows from the *two* precisely-named inputs

* `Cor815RealDescentResidueDataProvenance37` — the descent-unit *provenance*: piece (i)
  realness/membership of `η_a/η_b` (Washington §9.1) together with the bare all-conjugate residue
  equations (Washington Lemma 9.8); and
* `Lemma98LocalPower37` — Washington Lemma 9.8's mod-`𝔩` Kummer congruence (the single-index
  residue input).

Everything else is *proven*: the analytic `SinnottIndexFormula 37`, the `Δ`-action eigenvalue
eigenspace collapse, the half-range Vandermonde collapse, the **automatic eigencomponent
decomposition** (§1–§2 of this file), the all-conjugate `ω^{32}`-membership reduction, and the
single-index index collapse. -/
theorem caseIIResidueProvenance_assumptionII_of_residueData
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_data : Cor815RealDescentResidueDataProvenance37)
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIConjugateResidue_assumptionII_of_residueProvenance
    (caseIIResidueProvenance_provenance_of_residueData h_data) h_localPow

end BernoulliRegular.FLT37.Eichler

end
