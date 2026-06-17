/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.IwasawaProof.FundamentalSequence
import PadicLFunctions.IwasawaProof.Generators
import PadicLFunctions.Coleman.ColContinuity

/-!
# Iwasawa's theorem (RJW §12.5, TeX 3582–3608) — E12.5, MILESTONE

`thm:iwasawa 2`: the Coleman map induces (i) a short exact sequence of `Λ(𝒢)`-modules
`0 → 𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p → ℤ_p(1) → 0` and (ii) the isomorphism
`𝒰_{∞,1}^+/𝒞_{∞,1}^+ ≅ Λ(𝒢^+)/I(𝒢^+)ζ_p` (the §11-stated, then-unwired, `thm:iwasawa`).
The image computation uses `Col_cyclo`/`coleman_to_kl` at the generators
(`LemmaGeneratorCinfty1`); (ii) follows from (i) since `p` is odd, `⟨c⟩`-invariants are
exact, and `ℤ_p(1)^{⟨c⟩} = 0`.

## Status of the image computation `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p`

The `⊇` inclusion — the §13/IMC **density-crossing** (from the dense `ℤ_p`-span of the
group-element scalars `{[σ_a]}` to all of `Λ(𝒢)`) — is **proved** (`zetaIdeal_le_col_image`),
on top of the analytic/topology layer `Coleman/ColContinuity.lean`: a weak-* topology on
`Λ(ℤ_p^×)`, the joint continuity of the (inverse-avoiding paired) Coleman pipeline
`colemanPipe2`, the compactness of `Col '' 𝒞_{∞,1}` (continuous image of the compact
`colemanPairSet`), and the weak-* density of the Dirac span. The injectivity corollary
`mem_cycloTower1_of_col_mem_zetaIdeal` (the `→` of the iff) is therefore axiom-clean.

The `⊆` inclusion (well-definedness of the descent) reduces to the deferred **cyclic-module
density** `𝒞_{∞,1} = closure(Λ(𝒢)·wγ(a₀))` (RJW LemmaGeneratorCinfty1, TeX 3573–3578), a
tower-level *algebraic* density not supplied by the continuity layer; it is the single
remaining input for `col_image_cycloTower1_eq_zetaIdeal` and hence for the milestones
`iwasawa_theorem`/`iwasawa_exact_sequence`.
-/

open PadicLFunctions PadicLFunctions.Coleman

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## Infrastructure for the descent of the Coleman map (RJW §12.5)

The two milestones are the descents of the Coleman map `Col : 𝒰_∞ → Λ(ℤ_p^×)` to the
cyclotomic quotient `𝒰_{∞,1}/𝒞_{∞,1}` (resp. its plus part). `Col` is a homomorphism from
the *multiplicative* group `NormCompatUnits` to the *additive* group of measures
(`Col_add`, `Col_one`); the descent is `[u] ↦ [Col u]` into the ideal quotient
`Λ(𝒢)/I(𝒢)ζ_p`, packaged as a `MonoidHom` into `Multiplicative (Λ(𝒢)/I(𝒢)ζ_p)` and
converted to the additive shape demanded by the statements with `MonoidHom.toAdditive`. -/

/-- `Col 1 = 0`: the trivial unit system is `(p−1)`-torsion (each level is `1`), so
`Col_eq_zero_of_torsion` kills it. -/
theorem Col_one : Col p (1 : NormCompatUnits p) = 0 :=
  Col_eq_zero_of_torsion p 1 (fun _ => one_pow _)

/-- **The Coleman map as a homomorphism into the additive group `Λ(𝒢)/I(𝒢)ζ_p`**, packaged
multiplicatively: `u ↦ [Col u] ∈ Multiplicative (Λ(𝒢)/I(𝒢)ζ_p)`. The hom property is
`Col_add` (`Col` turns products into sums) followed by the additive quotient map; `map_one`
is `Col_one`. This is the source of the descent `[u] ↦ [Col u]`. -/
def ColMul (hp2 : p ≠ 2) :
    NormCompatUnits p →* Multiplicative (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2) where
  toFun u := Multiplicative.ofAdd (Ideal.Quotient.mk (PadicMeasure.zetaIdeal p hp2) (Col p u))
  map_one' := by
    rw [show Col p (1 : NormCompatUnits p) = 0 from Col_one p, map_zero]; rfl
  map_mul' u v := by
    show Multiplicative.ofAdd (Ideal.Quotient.mk _ (Col p (u * v))) = _
    rw [Col_add, map_add, ofAdd_add]

@[simp] theorem ColMul_apply (hp2 : p ≠ 2) (u : NormCompatUnits p) :
    ColMul p hp2 u
      = Multiplicative.ofAdd (Ideal.Quotient.mk (PadicMeasure.zetaIdeal p hp2) (Col p u)) :=
  rfl

/-- The canonical cyclotomic generator `c(a₀)` maps into the ζ-ideal: `Col(c(a₀)) =
−zetaNum a₀ ∈ I(𝒢)ζ_p`. Here `a₀` is the integer topological generator chosen by
`padicZeta` (`exists_nat_topological_generator`), and `zetaNum a₀ ∈ I(𝒢)ζ_p` because
`([a₀]−1)·ζ_p = zetaNum a₀` (`IsLocalization.mk'_spec'`) with `[a₀]−1` in the augmentation
ideal. This is the **bounded facet** of the image computation (the single generator); the
full tower-level inclusion is `col_mem_zetaIdeal_iff_mem_cycloTower1`. -/
theorem Col_cyclo_mem_zetaIdeal (hp2 : p ≠ 2) :
    Col p (cyclo p
        (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose_spec.1 hp2)
      ∈ PadicMeasure.zetaIdeal p hp2 := by
  -- `Col(c(a₀)) = −zetaNum a₀` and `zetaNum a₀ ∈ I(𝒢)ζ_p`
  rw [Col_cyclo]
  refine neg_mem ?_
  rw [PadicMeasure.mem_zetaIdeal_iff]
  refine ⟨PadicMeasure.dirac p
      (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose - 1, ?_, ?_⟩
  · rw [PadicMeasure.augmentationIdeal, RingHom.mem_ker, map_sub, map_one,
      show PadicMeasure.deg p (PadicMeasure.dirac p _) = 1 from rfl, sub_self]
  · exact (IsLocalization.mk'_spec' (PadicMeasure.QuotientField p) _ _).symm

/-- **`ℤ_p(1) ⊆ 𝒞_{∞,1}`** (RJW §12.5, the injectivity sub-lemma): the Tate-twist tower
`(ξ_n^a)_n` lies in the cyclotomic tower. Levelwise, `ξ_n^a = zpPow ξ_n a` is a `ℤ_p`-limit
of the integral powers `ξ_n^k` (cyclotomic units in `𝒰_{n,1}`), so it lands in the p-adic
closure `𝒞_{n,1}` (`zpPow_zetaSys_mem_cycloClosureOne`). This is the inclusion making the
kernel `ℤ_p(1)` of `Col` (`mem_ker_Col_iff_mem_ZpOne`) sit inside `𝒞_{∞,1}`, which transfers
`Col`-equality on a cyclotomic representative back to tower membership. -/
theorem ZpOne_le_cycloTower1 : ZpOne p ≤ cycloTower1 p := by
  intro u hu n hn
  obtain ⟨a, ha⟩ := hu
  exact zpPow_zetaSys_mem_cycloClosureOne p hn a (ha n hn)

/-! ## The `Λ(𝒢)`-scalar action on `𝒞_{∞,1}` at the group-element level (RJW TeX 3582–3608)

The dense facet of the image computation `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p`: as `a` ranges over
`ℤ_p^×`, the group-element scalars `[σ_a]` act on the generator `wγ(a₀)⁻¹` (with
`Col(wγ(a₀)⁻¹) = ζ_p`-numerator) by `σ_a`, landing inside `𝒞_{∞,1}`
(`galNCU_wGamma_mem_cycloTower1`), and `Col(σ_a · wγ(a₀)⁻¹) = [a]·zetaNum a₀`
(`Col_galNCU_eq_dirac_mul`). So the `ℤ_p`-span of `{[σ_a]·zetaNum a₀}` — dense in `I(𝒢)ζ_p`
— lies in the additive subgroup `Col '' 𝒞_{∞,1}`. This is the §12.4-realised content; the
remaining density-crossing to all of `Λ(𝒢)` is the §13/IMC core isolated below. -/

/-- `σ_a(wγ(a₀)⁻¹) ∈ 𝒞_{∞,1}`: the `𝒢`-translate of the (inverse) cyclotomic generator stays in
the cyclotomic tower (`galNCU` is a group hom, `cycloTower1` a subgroup,
`galNCU_wGamma_mem_cycloTower1`). -/
theorem galNCU_wGamma_inv_mem_cycloTower1 (a : ℤ_[p]ˣ) (hp2 : p ≠ 2) :
    galNCU p a (wGamma p hp2)⁻¹ ∈ cycloTower1 p := by
  rw [galNCU_inv p a (wGamma p hp2)]
  exact (cycloTower1 p).inv_mem (galNCU_wGamma_mem_cycloTower1 p a hp2)

/-- **The group-element image identity** `Col(σ_a · wγ(a₀)⁻¹) = [a]·zetaNum a₀`: combines
`Col_galNCU_eq_dirac_mul` (`Col(σ_a u) = [a]·Col u`) with `Col(wγ(a₀)⁻¹) = −Col(wγ(a₀)) =
zetaNum a₀` (`Col_wGamma`, `Col`-homomorphism). As `a` ranges over `ℤ_p^×`, the RHS ranges over
the group-element multiples of `zetaNum a₀`. -/
theorem Col_galNCU_wGamma_inv (a : ℤ_[p]ˣ) (hp2 : p ≠ 2) :
    Col p (galNCU p a (wGamma p hp2)⁻¹)
      = (PadicMeasure.dirac p a) * PadicMeasure.zetaNum p
          (PadicMeasure.exists_nat_topological_generator p hp2).choose := by
  -- `Col(wγ⁻¹) = −Col(wγ) = zetaNum a₀`
  have h := Col_add p (wGamma p hp2) (wGamma p hp2)⁻¹
  rw [mul_inv_cancel, Col_one] at h
  have hinv : Col p (wGamma p hp2)⁻¹
      = PadicMeasure.zetaNum p
          (PadicMeasure.exists_nat_topological_generator p hp2).choose := by
    rw [eq_neg_of_add_eq_zero_right h.symm, Col_wGamma_choose, neg_neg]
  rw [Col_galNCU_eq_dirac_mul, hinv]

/-- **The group-element scalar multiples lie in `Col '' 𝒞_{∞,1}`** (the dense facet of the image
identity): for every `a ∈ ℤ_p^×`, `[a]·zetaNum a₀ ∈ Col '' 𝒞_{∞,1}`, witnessed by the tower
element `σ_a(wγ(a₀)⁻¹) ∈ 𝒞_{∞,1}` (`galNCU_wGamma_inv_mem_cycloTower1`, `Col_galNCU_wGamma_inv`).
The `ℤ_p`-span of these is dense in `I(𝒢)ζ_p = (zetaNum a₀)`. -/
theorem dirac_mul_zetaNum_mem_col_image (a : ℤ_[p]ˣ) (hp2 : p ≠ 2) :
    (PadicMeasure.dirac p a) * PadicMeasure.zetaNum p
        (PadicMeasure.exists_nat_topological_generator p hp2).choose
      ∈ Col p '' (cycloTower1 p : Set (NormCompatUnits p)) :=
  ⟨galNCU p a (wGamma p hp2)⁻¹, galNCU_wGamma_inv_mem_cycloTower1 p a hp2,
    Col_galNCU_wGamma_inv p a hp2⟩

/- **The §12.5 image computation (RJW thm:iwasawa 2, TeX 3582–3608).** Historical note: the
image characterisation `image(Col|_{𝒞_{∞,1}}) = I(𝒢)ζ_p` drives both milestones — for a
principal-unit tower `u ∈ 𝒰_{∞,1}`, `Col u ∈ I(𝒢)ζ_p` *iff* `u ∈ 𝒞_{∞,1}`.

This is the inverse-limit cyclic-`Λ(𝒢)`-module computation of RJW's proof: `𝒞_{∞,1}` is the
cyclic `Λ(𝒢)`-module generated by `c(a)` (LemmaGeneratorCinfty1, TeX 3553–3578), and
`Col(λ·c(a)) = λ·Col(c(a)) = λ·(−zetaNum a)`, so as `λ` ranges over `Λ(𝒢)` the images fill
`I(𝒢)ζ_p` (the `[σ_a]−1` generate the augmentation ideal). The `(⊇)`/well-definedness
direction is grounded at the single generator by `Col_cyclo_mem_zetaIdeal`; the `(⊆)`/
injectivity direction is the kernel-of-the-descent statement.

**State of the proof (T12xx).** Both directions are reduced here to the *single* set-level
image identity `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p` (`col_image_cycloTower1_eq_zetaIdeal`, the
remaining blocker), using the now-available `Λ(𝒢)`-action homomorphism laws
`galNCU_mul`/`galNCU_one` and the kernel inclusion `ZpOne_le_cycloTower1`:
* `←` (`u ∈ 𝒞_{∞,1} ⟹ Col u ∈ I(𝒢)ζ_p`) is the `⊆` half of the image identity applied to
  the witness `Col u = Col u`;
* `→` (`Col u ∈ I(𝒢)ζ_p ⟹ u ∈ 𝒞_{∞,1}`) is the injectivity corollary: the `⊇` half gives
  `c ∈ 𝒞_{∞,1}` with `Col c = Col u`, so `Col (u·c⁻¹) = 0` (`Col_add`,
  `Col`-homomorphism), whence `u·c⁻¹ ∈ ℤ_p(1)` (`mem_ker_Col_iff_mem_ZpOne`)
  `⊆ 𝒞_{∞,1}` (`ZpOne_le_cycloTower1`), so `u = (u·c⁻¹)·c ∈ 𝒞_{∞,1}`.

The remaining `col_image_cycloTower1_eq_zetaIdeal` is the genuine §13/IMC-deferred core: it
requires the inverse-limit `Λ(𝒢)`-module structure of `𝒞_{∞,1}` — defined as the inverse
limit of the *topological closures* `𝒞_{n,1} = clos(𝒟_{n,1}) ⊓ 𝒰_{n,1}` (`cycloClosureOne`).
Passing the level-`n` single-generator cyclicity `cor:cyc units gen 2`
(`cycloUnit_mem_cycloTranslateSubgroup`, now banked — the single `c_n(a₀)`
`ℤ[𝒢_n]`-generates every `c_n(b')`) up to the tower needs either continuity of
`Col` (`Col` is built from the Coleman-series limit construction — no continuity is
available) or the inverse-limit cyclic-`Λ(𝒢)`-module structure on the unit tower
(the full LemmaGeneratorCinfty1, TeX 3573–3578, the deferred §13 input). All other
ingredients of both
milestones (the `Col` hom property, the descent through `QuotientGroup.lift`, the plus-part
transport `plusEquiv`/`projPlus`/`isCompl_plusPart_minusPart`, the `ℤ_p(1)^{⟨c⟩}=0` collapse,
surjectivity onto `ker(χ-moment)` via `range_Col_eq_ker_chiMoment`) are proved without
further `sorry`.

**§12.4 infrastructure now in place (`Generators.lean`, all sorry-free, axiom-clean).**
The cyclic-`Λ(𝒢)`-module scaffolding for RJW `LemmaGeneratorCinfty1` is built:
* `galNCU_mul`/`galNCU_one` — `σ_a` is a group endomorphism of `𝒰_∞`;
* `galNCU_mem_unitsTower1` — `σ_a` preserves the principal-unit tower `𝒰_{∞,1}` (isometry
  `norm_galAut` fixing `1`), the levelwise half of the `𝒢`-stability of the tower;
* `Col_galNCU_eq_dirac_mul` — the generator-image identity `Col(σ_a u) = [a]·Col u` in
  convolution form (`Col_galNCU` + `dirac_mul_eq_pushforward`), i.e. the scalar `[σ_a]`-action
  matching `Col(λ·c) = λ·Col(c)` for the group-element scalars `λ = [σ_a]`.
With these, input **(I)** is now CLOSED and only the closure-crossing **(II)** remains:
* **(I) the generator `wγ(a₀) ∈ 𝒞_{∞,1}` with `Col(wγ(a₀)) = −zetaNum a₀` — DONE.** The
  generator `wGamma p hp2` is assembled in `Generators.lean` (`𝒪_n`-residue Teichmüller split
  `normCompat_eq_teichmuller_mul_principal`), `Col_wGamma : Col(wγ a₀) = −zetaNum a₀`, and
  `wGamma_mem_cycloTower1 : wγ(a₀) ∈ 𝒞_{∞,1}` (via the §13 `(p−1)`-divisible closure layer
  `mem_cycloClosureOne_of_pow_mem`, CyclotomicUnits, all sorry-free, axiom-clean).
* **(II) the closure-crossing / density — the SOLE remaining blocker.** With the generator in
  hand, both inclusions of `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p` reduce to the `Λ(𝒢)`-linearity of `Col`
  on the cyclic module `𝒞_{∞,1} = closure(Λ(𝒢)·wγ(a₀))`, i.e. `Col(r • c) = r · Col c` for
  *arbitrary* `r ∈ Λ(𝒢)`, not merely the group-element scalars `r = [σ_a]` (where
  `Col_galNCU_eq_dirac_mul` gives it and `galNCU_*` realise the action). The crossing from the
  `ℤ_p`-span of `{[σ_a]}` (dense in `Λ(𝒢)`) to all of `Λ(𝒢)` is the genuine §13/IMC core and
  requires infrastructure ABSENT from the project (verified by exhaustive search):
  - **continuity route** — a topology on `NormCompatUnits` (the inverse-limit profinite unit
    group) AND on `PadicMeasure` (a bare `C(X,ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` abbrev with NO topology),
    plus `Continuous (Col p)` through the whole Coleman construction
    `unitsCmul ∘ mahler⁻¹ ∘ dlog ∘ colemanSeries` (the Coleman-series inverse-limit factor is
    READ-ONLY and has no continuity lemma), plus `IsClosed (↑(zetaIdeal p hp2))`; OR
  - **cyclic-module route** — a convolution `Λ(𝒢)`-module action `μ • u` on the inverse-limit
    unit tower (no `Module (PadicMeasure …) (NormCompatUnits …)` instance exists) and a proof
    that `Col` intertwines it (no `Col`-`smul` lemma exists), i.e. the tower lift of the
    now-banked level-`n` cyclicity `cycloUnit_mem_cycloTranslateSubgroup` to the full
    inverse-limit cyclic-module description (LemmaGeneratorCinfty1, TeX 3573–3578).
  Neither is reachable within the file confinement without first building a multi-file §13
  topology/module layer; left as a single documented blocker below. -/
/-- `Col '' 𝒞_{∞,1}` packaged as an *additive subgroup* of `Λ(ℤ_p^×)` (the image of the
multiplicative subgroup `𝒞_{∞,1}` under the homomorphism `Col`, `Col_add`/`Col_one`). It is
*closed* in the weak-* topology (`isClosed_col_image`: the continuous `colemanPipe2`-image of
the compact `colemanPairSet`). -/
def colImageSubgroup : AddSubgroup (PadicMeasure p ℤ_[p]ˣ) where
  carrier := Col p '' (cycloTower1 p : Set (NormCompatUnits p))
  add_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u * v, mul_mem hu hv, Col_add p u v⟩
  zero_mem' := ⟨1, one_mem _, Col_one p⟩
  neg_mem' := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h := Col_add p u u⁻¹
    rw [mul_inv_cancel, Col_one] at h
    exact eq_neg_of_add_eq_zero_right h.symm

/-- **The ζ-ideal lands in the Coleman image** `I(𝒢)ζ_p ⊆ Col '' 𝒞_{∞,1}` — the genuine
density-crossing (RJW §13/IMC, the formerly-blocked core). Now proved: `Col '' 𝒞_{∞,1}` is a
*closed* additive subgroup (`isClosed_col_image`, the compact `colemanPipe2`-image), it contains
`[a]·ζ_num a₀` for every group element `a` (`dirac_mul_zetaNum_mem_col_image`), and the Dirac
span is weak-* dense, so the whole principal ideal `I(𝒢)ζ_p = (ζ_num a₀)` lands inside it
(`PadicMeasure.mul_mem_of_dirac_mul_mem`, crossing the `ℤ_p`-span of `{[σ_a]}` to all of
`Λ(𝒢)` by continuity of `s ↦ s · ζ_num a₀`). -/
theorem zetaIdeal_le_col_image (hp2 : p ≠ 2) :
    (PadicMeasure.zetaIdeal p hp2 : Set (PadicMeasure p ℤ_[p]ˣ))
      ⊆ Col p '' (cycloTower1 p : Set (NormCompatUnits p)) := by
  -- `H := colImageSubgroup` is closed and contains every `[a]·ζ_num a₀`
  have hHclosed : IsClosed ((colImageSubgroup p : Set (PadicMeasure p ℤ_[p]ˣ))) :=
    isClosed_col_image p
  have hHdirac : ∀ a : ℤ_[p]ˣ, PadicMeasure.dirac p a * PadicMeasure.zetaNum p
      (PadicMeasure.exists_nat_topological_generator p hp2).choose ∈ colImageSubgroup p :=
    fun a => dirac_mul_zetaNum_mem_col_image p a hp2
  have hb_gen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n
        (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose) = ⊤ :=
    (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose_spec.2.2
  have hνeq : algebraMap (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure.QuotientField p)
        (PadicMeasure.dirac p
          (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose - 1)
        * PadicMeasure.padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure.QuotientField p)
          (PadicMeasure.zetaNum p
            (PadicMeasure.exists_nat_topological_generator p hp2).choose) := by
    rw [PadicMeasure.padicZeta]
    exact IsLocalization.mk'_spec' (PadicMeasure.QuotientField p) _ _
  rw [PadicMeasure.zetaIdeal_eq_span p hp2 hb_gen hνeq]
  -- reduce to `span{ν} ⊆ H` for the closed subgroup `H = colImageSubgroup`
  intro x hx
  rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hx
  obtain ⟨r, rfl⟩ := hx
  -- `r · ζ_num a₀ ∈ H` by the density-crossing
  rw [mul_comm]
  exact PadicMeasure.mul_mem_of_dirac_mul_mem p hHclosed hHdirac r

/-! ## The `⊆`-direction reduction to the cyclic-module density (RJW LemmaGeneratorCinfty1)

The well-definedness inclusion `Col '' 𝒞_{∞,1} ⊆ I(𝒢)ζ_p` is reduced *axiom-clean* to the
single deferred density `𝒞_{∞,1} ⊆ closure(⟨σ_a · wγ(a₀)⟩)` (RJW LemmaGeneratorCinfty1,
TeX 3573–3578) using the now-banked continuity layer:

* the source-side inverse-limit topology and `Continuous (Col)` (`Coleman/ColContinuity.lean`,
  ST1/ST2): the cyclic generators `σ_a · wγ(a₀)` have `Col(σ_a · wγ) = [σ_a]·(−ζ_num a₀) ∈
  I(𝒢)ζ_p`, so the subgroup `M = ⟨σ_a · wγ(a₀)⟩` lands in the **closed** preimage
  `Col⁻¹(I(𝒢)ζ_p)` (`isClosed_zetaIdeal` + `continuous_Col`), hence so does `closure(M)`;
* therefore *if* `𝒞_{∞,1} ⊆ closure(M)` then `Col '' 𝒞_{∞,1} ⊆ I(𝒢)ζ_p`.

This replaces the old "no continuity available" route: with `continuous_Col` banked, the
`Λ(𝒢)`-linearity of `Col` on the cyclic module `𝒞_{∞,1} = closure(Λ(𝒢)·wγ)` *is* the
continuity extension, and the sole residual is the algebraic tower density `hdense` (the
inverse-limit lift of the level-`n` cyclicity `cycloUnit_mem_cycloTranslateSubgroup`). -/

/-- **The cyclic-module generating subgroup** `M = ⟨σ_a · wγ(a₀) : a ∈ ℤ_p^×⟩` of `𝒰_∞`: the
multiplicative subgroup generated by the `𝒢`-translates of the Teichmüller-corrected cyclotomic
generator `wγ(a₀)`. Its closure is RJW's cyclic `Λ(𝒢)`-module `𝒞_{∞,1}` (LemmaGeneratorCinfty1);
its `Col`-image is the `ℤ_p[𝒢]`-span of `−ζ_num a₀`, dense in `I(𝒢)ζ_p`. -/
def cycloGenSubgroup (hp2 : p ≠ 2) : Subgroup (NormCompatUnits p) :=
  Subgroup.closure {u : NormCompatUnits p | ∃ a : ℤ_[p]ˣ, u = galNCU p a (wGamma p hp2)}

/-- **`Col⁻¹(I(𝒢)ζ_p)` as a subgroup of `𝒰_∞`**: the units whose Coleman image lands in the
ζ-ideal. A subgroup because `Col` is a group hom into the additive `Λ(𝒢)` (`Col_add`/`Col_one`)
and `I(𝒢)ζ_p` is an additive subgroup; *closed* because `Col` is continuous (`continuous_Col`)
and `I(𝒢)ζ_p` is weak-* closed (`isClosed_zetaIdeal`). -/
def colPreimageZeta (hp2 : p ≠ 2) : Subgroup (NormCompatUnits p) where
  carrier := {u | Col p u ∈ PadicMeasure.zetaIdeal p hp2}
  mul_mem' {u v} hu hv := by
    simp only [Set.mem_setOf_eq, Col_add] at *
    exact (PadicMeasure.zetaIdeal p hp2).add_mem hu hv
  one_mem' := by
    simp only [Set.mem_setOf_eq, Col_one]; exact (PadicMeasure.zetaIdeal p hp2).zero_mem
  inv_mem' {u} hu := by
    simp only [Set.mem_setOf_eq] at *
    have h := Col_add p u u⁻¹
    rw [mul_inv_cancel, Col_one] at h
    rw [eq_neg_of_add_eq_zero_right h.symm]
    exact (PadicMeasure.zetaIdeal p hp2).neg_mem hu

/-- `Col⁻¹(I(𝒢)ζ_p)` is closed in the inverse-limit topology (`continuous_Col` pulls back the
weak-* closed `isClosed_zetaIdeal`). -/
theorem isClosed_colPreimageZeta (hp2 : p ≠ 2) :
    IsClosed (colPreimageZeta p hp2 : Set (NormCompatUnits p)) :=
  (PadicMeasure.isClosed_zetaIdeal p hp2).preimage (continuous_Col p)

/-- `ζ_num a₀ ∈ I(𝒢)ζ_p` (the principal generator): `ζ_num a₀ = ([a₀]−1)·ζ_p` with `[a₀]−1` in
the augmentation ideal (`mem_zetaIdeal_iff`). -/
theorem zetaNum_choose_mem_zetaIdeal (hp2 : p ≠ 2) :
    PadicMeasure.zetaNum p (PadicMeasure.exists_nat_topological_generator p hp2).choose
      ∈ PadicMeasure.zetaIdeal p hp2 := by
  rw [PadicMeasure.mem_zetaIdeal_iff]
  refine ⟨PadicMeasure.dirac p
    (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose - 1, ?_, ?_⟩
  · rw [PadicMeasure.augmentationIdeal, RingHom.mem_ker, map_sub, map_one,
      show PadicMeasure.deg p (PadicMeasure.dirac p
        (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose) = 1 from rfl,
      sub_self]
  · rw [PadicMeasure.padicZeta]
    exact (IsLocalization.mk'_spec' (PadicMeasure.QuotientField p) _ _).symm

/-- Each cyclic generator lands in `Col⁻¹(I(𝒢)ζ_p)`: `Col(σ_a · wγ(a₀)) = [a]·(−ζ_num a₀) ∈
I(𝒢)ζ_p` (`Col_galNCU_eq_dirac_mul`, `Col_wGamma_choose`, and `I(𝒢)ζ_p` an ideal containing
`ζ_num a₀`). -/
theorem galNCU_wGamma_mem_colPreimageZeta (a : ℤ_[p]ˣ) (hp2 : p ≠ 2) :
    galNCU p a (wGamma p hp2) ∈ colPreimageZeta p hp2 := by
  change Col p (galNCU p a (wGamma p hp2)) ∈ PadicMeasure.zetaIdeal p hp2
  rw [Col_galNCU_eq_dirac_mul, Col_wGamma_choose]
  exact (PadicMeasure.zetaIdeal p hp2).mul_mem_left _
    ((PadicMeasure.zetaIdeal p hp2).neg_mem (zetaNum_choose_mem_zetaIdeal p hp2))

/-- **Well-definedness `Col '' M ⊆ I(𝒢)ζ_p`**: the whole generating subgroup `M` lands in the
ζ-ideal preimage (each generator does, `galNCU_wGamma_mem_colPreimageZeta`, and the latter is a
subgroup). -/
theorem cycloGenSubgroup_le_colPreimageZeta (hp2 : p ≠ 2) :
    cycloGenSubgroup p hp2 ≤ colPreimageZeta p hp2 := by
  rw [cycloGenSubgroup, Subgroup.closure_le]
  rintro u ⟨a, rfl⟩
  exact galNCU_wGamma_mem_colPreimageZeta p a hp2

/-- `closure(M) ⊆ 𝒞_{∞,1}` (the *easy* half of `closure(M) = 𝒞_{∞,1}`): `𝒞_{∞,1}` is closed
(`isClosed_cycloTower1`) and contains every generator `σ_a · wγ(a₀)`
(`galNCU_wGamma_mem_cycloTower1`), hence the subgroup `M` and its closure. -/
theorem closure_cycloGenSubgroup_le_cycloTower1 (hp2 : p ≠ 2) :
    closure (cycloGenSubgroup p hp2 : Set (NormCompatUnits p))
      ⊆ (cycloTower1 p : Set (NormCompatUnits p)) := by
  refine (isClosed_cycloTower1 p).closure_subset_iff.mpr ?_
  rw [cycloGenSubgroup]
  refine (Subgroup.closure_le (cycloTower1 p)).mpr ?_
  rintro u ⟨a, rfl⟩
  exact galNCU_wGamma_mem_cycloTower1 p a hp2

/-- **The `⊆`-direction, modulo the cyclic-module density** (RJW thm:iwasawa 2): *given* the
tower density `𝒞_{∞,1} ⊆ closure(M)` (LemmaGeneratorCinfty1, the sole §13 residual), the
Coleman image of the cyclotomic tower lands in the ζ-ideal. Proof: `closure(M)` lies in the
closed subgroup `Col⁻¹(I(𝒢)ζ_p)` (it contains `M` by `cycloGenSubgroup_le_colPreimageZeta` and
is closed by `isClosed_colPreimageZeta`), so `𝒞_{∞,1} ⊆ closure(M) ⊆ Col⁻¹(I(𝒢)ζ_p)`. -/
theorem col_image_cycloTower1_le_zetaIdeal_of_density (hp2 : p ≠ 2)
    (hdense : (cycloTower1 p : Set (NormCompatUnits p)) ⊆
      closure (cycloGenSubgroup p hp2 : Set (NormCompatUnits p))) :
    Col p '' (cycloTower1 p : Set (NormCompatUnits p))
      ⊆ (PadicMeasure.zetaIdeal p hp2 : Set (PadicMeasure p ℤ_[p]ˣ)) := by
  rintro _ ⟨u, hu, rfl⟩
  have hclosure : closure (cycloGenSubgroup p hp2 : Set (NormCompatUnits p))
      ⊆ (colPreimageZeta p hp2 : Set (NormCompatUnits p)) :=
    (isClosed_colPreimageZeta p hp2).closure_subset_iff.mpr
      (by exact_mod_cast cycloGenSubgroup_le_colPreimageZeta p hp2)
  exact hclosure (hdense hu)

/- (`col_image_cycloTower1_eq_zetaIdeal` is now stated+proved BELOW `col_mem`, via `col_mem`.)
**The §12.5 image computation** `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p` (RJW thm:iwasawa 2, the image
identity). The `⊇` inclusion is the genuine density-crossing `zetaIdeal_le_col_image` (proved
via the §13 continuity layer `Coleman/ColContinuity.lean`: `Col '' 𝒞_{∞,1}` is closed and the
Dirac span is dense).

The `⊆` inclusion (well-definedness) is the single remaining input. Its *closedness* half is
now banked: `I(𝒢)ζ_p` is weak-* closed (`PadicMeasure.isClosed_zetaIdeal`, from the p-adic
Banach–Alaoglu compactness `PadicMeasure.instCompactSpace` of `Λ(ℤ_p^×)` — non-circular, it
does not use the image identity). So `⊆` reduces *exactly* to the algebraic cyclic-module
density `Col '' 𝒞_{∞,1} ⊆ closure(ℤ_p·{[σ_a]·ζ_num a₀})` (equivalently `𝒞_{∞,1} ⊆
closure(Λ(𝒢)·wγ(a₀))`, RJW LemmaGeneratorCinfty1, TeX 3573–3578): every cyclotomic-tower
unit is a `Λ(𝒢)`-limit of `σ_a`-translates of `wγ(a₀)`.

The level-`n` single-generator cyclicity `cor:cyc units gen 2` (RJW TeX 3484–3486) is now
**banked** (`cycloUnit_mem_cycloTranslateSubgroup`, `Generators.lean`): the single
`c_n(a₀)` `ℤ[𝒢_n]`-generates every cyclotomic unit `c_n(b')` via the explicit closed-form
`σ_a`-action `σ_a(c_n(b)) = (ξ^{tb}−1)/(ξ^t−1)` (`galAutVal_cycloUnit`) and the telescoping
product `c_n(b') = ∏_{i<r} σ_{a₀^i}(c_n(a₀))` (`prod_galAutValU_cycloUnit_telescope`).

What remains is *only* the **tower lift** of this level-`n` cyclicity to the inverse limit:
`𝒞_{∞,1} = closure(Λ(𝒢)·wγ(a₀))`, the genuine deferred §13 Iwasawa-module input not supplied
by any available layer. It needs the inverse-limit cyclic-`Λ(𝒢)`-module structure on the unit
tower (no `Module (PadicMeasure …) (NormCompatUnits …)` and no `Col`-`smul` intertwining for
arbitrary scalars exist; the latter is equivalent to the absent `Continuous (Col)`) or, on the
power-series side `Col '' 𝒞_{∞,1} = colemanPipe2 '' colemanPairSet`, the density of the
cyclotomic pairs in `colemanPairSet` (whose level-`n` constraints `f(π_n) ∈ val '' 𝒞_{n,1}` are
the closures `clos(𝒟_{n,1})`, tied across levels only by that module structure). -/
-- `col_image_cycloTower1_eq_zetaIdeal` is stated+proved below `col_mem_zetaIdeal_of_mem_cycloTower1`
-- (its `⊆` is exactly `col_mem`; the old `_of_density` route was unsound at the free level-0
-- coordinate, so the faithful plus/minus `col_mem` supersedes it). -/

/-- **`Col u ∈ I(𝒢)ζ_p ⟹ u ∈ 𝒞_{∞,1}`** (RJW §12.5, the injectivity corollary).
**Axiom-clean**: uses only the *proved* density-crossing `⊇` half `zetaIdeal_le_col_image`
(`Col u ∈ I(𝒢)ζ_p ⊆ Col '' 𝒞_{∞,1}` gives a cyclotomic `c` with `Col c = Col u`) together with
`ker Col = ℤ_p(1) ⊆ 𝒞_{∞,1}` (`mem_ker_Col_iff_mem_ZpOne`, `ZpOne_le_cycloTower1`): then
`u·c⁻¹ ∈ ℤ_p(1) ⊆ 𝒞_{∞,1}`, so `u = (u·c⁻¹)·c ∈ 𝒞_{∞,1}`. -/
theorem mem_cycloTower1_of_col_mem_zetaIdeal (hp2 : p ≠ 2) {u : NormCompatUnits p}
    (hu : u ∈ unitsTower1 p) (hCol : Col p u ∈ PadicMeasure.zetaIdeal p hp2) :
    u ∈ cycloTower1 p := by
  -- the `⊇` half of the image identity gives a cyclotomic `c` with `Col c = Col u`
  have hCol' : Col p u ∈ Col p '' (cycloTower1 p : Set (NormCompatUnits p)) :=
    zetaIdeal_le_col_image p hp2 hCol
  obtain ⟨c, hc, hcCol⟩ := hCol'
  -- `Col (u·c⁻¹) = Col u − Col c = 0`
  have hinv : Col p c⁻¹ = -Col p c := by
    have h := Col_add p c c⁻¹
    rw [mul_inv_cancel, Col_one] at h
    linear_combination -h
  have hker : Col p (u * c⁻¹) = 0 := by
    rw [Col_add, ← hcCol, hinv]; ring
  -- so `u·c⁻¹ ∈ ℤ_p(1) ⊆ 𝒞_{∞,1}`; and `c ∈ 𝒞_{∞,1}`, hence `u ∈ 𝒞_{∞,1}`
  have hcunit : u * c⁻¹ ∈ unitsTower1 p :=
    mul_mem hu ((unitsTower1 p).inv_mem (cycloTower1_le_unitsTower1 p hc))
  have hzp : u * c⁻¹ ∈ cycloTower1 p :=
    ZpOne_le_cycloTower1 p ((mem_ker_Col_iff_mem_ZpOne p hp2 hcunit).1 hker)
  rw [show u = (u * c⁻¹) * c by rw [mul_assoc, inv_mul_cancel, mul_one]]
  exact mul_mem hzp hc

/-- The level-`n` coordinate as a monoid hom `𝒰_∞ →* ℂ_[p]ˣ` (multiplicative + unital levelwise). -/
def elemsMonoidHom (n : ℕ) : NormCompatUnits p →* ℂ_[p]ˣ where
  toFun u := u.elems n
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The level-`n` image of the generating subgroup** `M = ⟨σ_a·wγ(a₀)⟩` is exactly the
`𝒢_n`-translate subgroup of `wγ(a₀)`'s level-`n` coordinate (`Subgroup.map_closure` +
`galNCU_elems_eq_galAutValU`). -/
theorem map_elemsMonoidHom_cycloGenSubgroup (hp2 : p ≠ 2) (n : ℕ) :
    Subgroup.map (elemsMonoidHom p n) (cycloGenSubgroup p hp2)
      = cycloTranslateSubgroup p n ((wGamma p hp2).elems n) := by
  rw [cycloGenSubgroup, MonoidHom.map_closure, cycloTranslateSubgroup]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (galNCU_elems_eq_galAutValU p a (wGamma p hp2) n)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨galNCU p a (wGamma p hp2), ⟨a, rfl⟩, galNCU_elems_eq_galAutValU p a (wGamma p hp2) n⟩

/-- **T1223 — `u ∈ 𝒞⁺_{∞,1} ⟹ Col u ∈ I(𝒢)ζ_p`** (RJW LemmaGeneratorCinfty1(ii) + the `Col`-image
of the plus generator). `Col u ∈ closure(Col '' M)` by the level-`0`-saturated density
`Col_mem_closure_image_of_levelwise`: at each level `n ≥ 1`, `u.elems n ∈ 𝒞⁺_{n,1} ⊆
closure(D_n)` (T1222 `cycloClosureOnePlus_le_closure_wGammaTranslate`), and `D_n =
elems_n '' M` (`map_elemsMonoidHom_cycloGenSubgroup`) modulo the continuous `Units.val`. Then
`closure(Col '' M) ⊆ I(𝒢)ζ_p` (each `Col(σ_a·wγ) ∈ I(𝒢)ζ_p`, `cycloGenSubgroup_le_colPreimageZeta`;
`I(𝒢)ζ_p` weak-* closed, `isClosed_zetaIdeal`). -/
theorem col_mem_zetaIdeal_of_mem_cycloTower1Plus (hp2 : p ≠ 2) {u : NormCompatUnits p}
    (hu : u ∈ cycloTower1Plus p) : Col p u ∈ PadicMeasure.zetaIdeal p hp2 := by
  have hcl : Col p u ∈ closure (Col p '' (cycloGenSubgroup p hp2 : Set (NormCompatUnits p))) := by
    apply Col_mem_closure_image_of_levelwise
    intro n hn
    have h1222 : (u.elems n) ∈
        closure (cycloTranslateSubgroup p n ((wGamma p hp2).elems n) : Set ℂ_[p]ˣ) :=
      cycloClosureOnePlus_le_closure_wGammaTranslate p hp2 hn (hu n hn)
    have himg : (fun s : NormCompatUnits p => (s.elems n : ℂ_[p]))
          '' (cycloGenSubgroup p hp2 : Set (NormCompatUnits p))
        = (Units.val : ℂ_[p]ˣ → ℂ_[p])
          '' (cycloTranslateSubgroup p n ((wGamma p hp2).elems n) : Set ℂ_[p]ˣ) := by
      rw [← map_elemsMonoidHom_cycloGenSubgroup p hp2 n, Subgroup.coe_map, ← Set.image_comp]
      rfl
    rw [himg]
    exact image_closure_subset_closure_image Units.continuous_val ⟨u.elems n, h1222, rfl⟩
  refine (closure_minimal ?_ (PadicMeasure.isClosed_zetaIdeal p hp2)) hcl
  rintro _ ⟨v, hv, rfl⟩
  exact cycloGenSubgroup_le_colPreimageZeta p hp2 hv

/-- **T1224' — the minus part of `𝒞_{∞,1}` is `ℤ_p(1)`** (RJW lem:cyc units gen (ii): `𝒟_n =
⟨ξ,𝒟⁺_n⟩`, so the `c`-anti-invariant part of the cyclotomic closure is the `ξ`-power tower). A
cyclotomic-tower unit `z` fixed up to inversion by complex conjugation `σ_{-1}` lies in
`ℤ_p(1) = ZpOne`. -/
theorem mem_ZpOne_of_mem_cycloTower1_cAnti (hp2 : p ≠ 2) {z : NormCompatUnits p}
    (hz : z ∈ cycloTower1 p) (hc : galNCU p (-1) z = z⁻¹) : z ∈ ZpOne p := by
  sorry

/-- **`u ∈ 𝒞_{∞,1} ⟹ Col u ∈ I(𝒢)ζ_p`** (RJW §12.5, the well-definedness half). Currently still
derived from the image identity `col_image_cycloTower1_eq_zetaIdeal` (whose `⊆` branch carries the
remaining sorry). The faithful Route-P proof (to replace this) is: split `Col u` into `c`-plus and
`c`-minus parts — `u·σ_{-1}(u) ∈ 𝒞⁺_{∞,1}` gives `(1+[−1])·Col u ∈ I(𝒢)ζ_p`
(`col_mem_zetaIdeal_of_mem_cycloTower1Plus`, T1223); `u·σ_{-1}(u)⁻¹` is `c`-anti-invariant in
`𝒞_{∞,1}` hence in `ℤ_p(1)` (`mem_ZpOne_of_mem_cycloTower1_cAnti`, T1224'), so
`(1−[−1])·Col u = 0` and `(1+[−1])·Col u = 2·Col u ∈ I(𝒢)ζ_p`; `2` a unit (`p` odd,
`isUnit_two_padicInt`) gives `Col u ∈ I(𝒢)ζ_p`. -/
theorem col_mem_zetaIdeal_of_mem_cycloTower1 (hp2 : p ≠ 2) {u : NormCompatUnits p}
    (hu' : u ∈ cycloTower1 p) : Col p u ∈ PadicMeasure.zetaIdeal p hp2 := by
  have hcmem : galNCU p (-1) u ∈ cycloTower1 p := galNCU_neg_one_mem_cycloTower1 p hu'
  have hColc : Col p (galNCU p (-1) u) = PadicMeasure.dirac p (-1) * Col p u :=
    Col_galNCU_eq_dirac_mul p (-1) u
  -- the `c`-plus part `u·σ_{-1}(u) ∈ 𝒞⁺_{∞,1}`
  have huc_cyclo : u * galNCU p (-1) u ∈ cycloTower1 p := mul_mem hu' hcmem
  have huc_fix : galNCU p (-1) (u * galNCU p (-1) u) = u * galNCU p (-1) u := by
    rw [galNCU_mul, galNCU_neg_one_involutive p hp2, mul_comm]
  have huc_plus : u * galNCU p (-1) u ∈ unitsTower1Plus p :=
    galNCU_neg_one_fixed_mem_unitsTower1Plus p hp2 (cycloTower1_le_unitsTower1 p huc_cyclo) huc_fix
  have hplus : u * galNCU p (-1) u ∈ cycloTower1Plus p := by
    intro n hn
    have hcn := huc_cyclo n hn; have hpn := huc_plus n hn
    rw [cycloClosureOne, Subgroup.mem_inf] at hcn
    rw [localUnitsOnePlus, Subgroup.mem_inf] at hpn
    rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf]
    exact ⟨⟨hcn.1, hpn.2⟩, hcn.2⟩
  have hColplus : Col p (u * galNCU p (-1) u) ∈ PadicMeasure.zetaIdeal p hp2 :=
    col_mem_zetaIdeal_of_mem_cycloTower1Plus p hp2 hplus
  -- the `c`-minus part `u·σ_{-1}(u)⁻¹ ∈ ℤ_p(1)`, so `Col(u·σ_{-1}(u)⁻¹) = 0`
  have hanti : galNCU p (-1) (u * (galNCU p (-1) u)⁻¹) = (u * (galNCU p (-1) u)⁻¹)⁻¹ := by
    rw [galNCU_mul, galNCU_inv, galNCU_neg_one_involutive p hp2, mul_inv_rev, inv_inv]
  have hColminus : Col p (u * (galNCU p (-1) u)⁻¹) = 0 :=
    (mem_ker_Col_iff_mem_ZpOne p hp2
      (mul_mem (cycloTower1_le_unitsTower1 p hu')
        ((unitsTower1 p).inv_mem (cycloTower1_le_unitsTower1 p hcmem)))).2
      (mem_ZpOne_of_mem_cycloTower1_cAnti p hp2
        (mul_mem hu' ((cycloTower1 p).inv_mem hcmem)) hanti)
  have hColcinv : Col p (galNCU p (-1) u)⁻¹ = -Col p (galNCU p (-1) u) := by
    have h := Col_add p (galNCU p (-1) u) (galNCU p (-1) u)⁻¹
    rw [mul_inv_cancel, Col_one] at h; linear_combination -h
  -- `Col(u·c⁻¹) = Col u − [−1]·Col u = 0` ⟹ `[−1]·Col u = Col u`
  have hfix : PadicMeasure.dirac p (-1) * Col p u = Col p u := by
    have h0 : Col p (u * (galNCU p (-1) u)⁻¹)
        = Col p u - PadicMeasure.dirac p (-1) * Col p u := by
      rw [Col_add, hColcinv, hColc]; ring
    rw [hColminus] at h0; linear_combination h0
  -- `Col(u·c) = (1+[−1])·Col u = 2·Col u ∈ I(𝒢)ζ_p`; `2` a unit ⟹ `Col u ∈ I(𝒢)ζ_p`
  have h2 : (2 : ℤ_[p]) • Col p u ∈ PadicMeasure.zetaIdeal p hp2 := by
    have hsum : Col p (u * galNCU p (-1) u) = (2 : ℤ_[p]) • Col p u := by
      rw [Col_add, hColc, hfix, two_smul]
    rwa [hsum] at hColplus
  obtain ⟨v, hv⟩ := PadicLFunctions.isUnit_two_padicInt p hp2
  have hfin := (PadicMeasure.zetaIdeal p hp2).smul_of_tower_mem ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) h2
  rwa [smul_smul,
    show ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (2 : ℤ_[p]) = 1 from by
      rw [← hv, ← Units.val_mul, inv_mul_cancel, Units.val_one], one_smul] at hfin

/-- **The §12.5 image computation** `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p` (RJW thm:iwasawa 2). The `⊆`
inclusion is the faithful plus/minus `col_mem_zetaIdeal_of_mem_cycloTower1`; the `⊇` is the
density-crossing `zetaIdeal_le_col_image`. -/
theorem col_image_cycloTower1_eq_zetaIdeal (hp2 : p ≠ 2) :
    (Col p '' (cycloTower1 p : Set (NormCompatUnits p))) = PadicMeasure.zetaIdeal p hp2 := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact col_mem_zetaIdeal_of_mem_cycloTower1 p hp2 hu
  · exact zetaIdeal_le_col_image p hp2

theorem col_mem_zetaIdeal_iff_mem_cycloTower1 (hp2 : p ≠ 2) {u : NormCompatUnits p}
    (hu : u ∈ unitsTower1 p) :
    Col p u ∈ PadicMeasure.zetaIdeal p hp2 ↔ u ∈ cycloTower1 p :=
  ⟨mem_cycloTower1_of_col_mem_zetaIdeal p hp2 hu, col_mem_zetaIdeal_of_mem_cycloTower1 p hp2⟩

/-! ## The descent of the Coleman map (RJW thm:iwasawa 2 (i)) -/

/-- **RJW thm:iwasawa 2 (i), the genuine map**: the Coleman map descends to a homomorphism
`𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p`, `[u] ↦ [Col u]`, packaged multiplicatively. It is the
restriction of `ColMul` (`u ↦ [Col u]`) to `𝒰_{∞,1}`, descended through the subgroup
`𝒞_{∞,1}` by `QuotientGroup.lift`: the cyclotomic units land in `ker` because `Col u ∈
I(𝒢)ζ_p` for `u ∈ 𝒞_{∞,1}` (the `→` direction of the image computation
`col_mem_zetaIdeal_iff_mem_cycloTower1`). This is the SES injection of RJW's diagram. -/
def colDescentMul (hp2 : p ≠ 2) :
    (↥(unitsTower1 p) ⧸ (cycloTower1 p).subgroupOf (unitsTower1 p)) →*
      Multiplicative (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2) := by
  refine QuotientGroup.lift ((cycloTower1 p).subgroupOf (unitsTower1 p))
    ((ColMul p hp2).comp (unitsTower1 p).subtype) ?_
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, (unitsTower1 p).coe_subtype, ColMul_apply]
  -- `[Col x] = 0` because `Col x ∈ I(𝒢)ζ_p` for the cyclotomic unit `x`
  have hmem : Col p (x : NormCompatUnits p) ∈ PadicMeasure.zetaIdeal p hp2 :=
    col_mem_zetaIdeal_of_mem_cycloTower1 p hp2 hx
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hmem]; rfl

/-- **RJW thm:iwasawa 2 (i), additive shape**: the descent of `Col` as the additive
homomorphism `𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p` demanded by the statement, obtained from
`colDescentMul` by `MonoidHom.toAdditive`. -/
def colDescent (hp2 : p ≠ 2) :
    Additive (↥(unitsTower1 p) ⧸ (cycloTower1 p).subgroupOf (unitsTower1 p)) →+
      (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2) :=
  MonoidHom.toAdditive (colDescentMul p hp2)

/-! ## The plus-part descent and the isomorphism (RJW thm:iwasawa 2 (ii)) -/

/-- `𝒞⁺_{∞,1} ≤ 𝒞_{∞,1}`: the plus closure-tower sits inside the full closure-tower
(`cycloClosureOnePlus ≤ cycloClosureOne`, dropping the `localUnitsPlus` factor). -/
theorem cycloTower1Plus_le_cycloTower1 : cycloTower1Plus p ≤ cycloTower1 p := by
  intro u hu n hn
  have h := hu n hn
  rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf] at h
  rw [cycloClosureOne, Subgroup.mem_inf]
  exact ⟨h.1.1, h.2⟩

/-- `𝒞⁺_{∞,1} ≤ 𝒰⁺_{∞,1}`: the plus closure-tower is principal-plus
(`cycloClosureOnePlus ≤ localUnitsOnePlus`). -/
theorem cycloTower1Plus_le_unitsTower1Plus : cycloTower1Plus p ≤ unitsTower1Plus p := by
  intro u hu n hn
  have h := hu n hn
  rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf] at h
  rw [localUnitsOnePlus, Subgroup.mem_inf]
  exact ⟨h.2, h.1.2⟩

/-- **The ζ-ideal commutes with the plus-projection**: `I(𝒢⁺)ζ_p = π_*(I(𝒢)ζ_p)`. Both are
principal — `I(𝒢)ζ_p = (zetaNum a₀)` (`zetaIdeal_eq_span`) and
`I(𝒢⁺)ζ_p = (π_*(zetaNum a₀))` (`zetaIdealPlus_eq_span`) for the common witness
`zetaNum a₀ = ([a₀]−1)·ζ_p` at the canonical generator `a₀` — so the result is
`Ideal.map_span` on the singleton. This is the bridge carrying the (i) image computation to
the plus side. -/
theorem zetaIdealPlus_eq_map_projPlus (hp2 : p ≠ 2) :
    PadicMeasure.zetaIdealPlus p hp2
      = (PadicMeasure.zetaIdeal p hp2).map (PadicMeasure.projPlus p) := by
  have hb_gen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n
        (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose) = ⊤ :=
    (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose_spec.2.2
  have hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure.QuotientField p)
        (PadicMeasure.dirac p
          (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose - 1)
        * PadicMeasure.padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure.QuotientField p)
          (PadicMeasure.zetaNum p
            (PadicMeasure.exists_nat_topological_generator p hp2).choose) := by
    rw [PadicMeasure.padicZeta]
    exact IsLocalization.mk'_spec' (PadicMeasure.QuotientField p) _ _
  rw [PadicMeasure.zetaIdealPlus_eq_span p hp2 hb_gen hν,
    PadicMeasure.zetaIdeal_eq_span p hp2 hb_gen hν, Ideal.map_span, Set.image_singleton]

/-- The plus-projection of the ζ-ideal lands in the plus ζ-ideal:
`π_*(I(𝒢)ζ_p) ⊆ I(𝒢⁺)ζ_p` (an equality by `zetaIdealPlus_eq_map_projPlus`; this is the
direction needed for well-definedness of the plus descent). -/
theorem projPlus_zetaIdeal_le_zetaIdealPlus (hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ}
    (hμ : μ ∈ PadicMeasure.zetaIdeal p hp2) :
    PadicMeasure.projPlus p μ ∈ PadicMeasure.zetaIdealPlus p hp2 := by
  rw [zetaIdealPlus_eq_map_projPlus p hp2]
  exact Ideal.mem_map_of_mem _ hμ

/-- **The plus Coleman map as a homomorphism into `Λ(𝒢⁺)/I(𝒢⁺)ζ_p`**, packaged
multiplicatively: `u ↦ [π_*(Col u)] ∈ Multiplicative (Λ(𝒢⁺)/I(𝒢⁺)ζ_p)`. The hom property
is `Col_add` followed by the ring-hom `π_* = projPlus` and the additive quotient map. This is
the plus analogue of `ColMul` and the source of the plus descent. -/
def ColPlusMul (hp2 : p ≠ 2) :
    NormCompatUnits p →* Multiplicative
      (PadicMeasure p (PadicMeasure.GPlus p) ⧸ PadicMeasure.zetaIdealPlus p hp2) where
  toFun u := Multiplicative.ofAdd
    (Ideal.Quotient.mk (PadicMeasure.zetaIdealPlus p hp2) (PadicMeasure.projPlus p (Col p u)))
  map_one' := by
    change Multiplicative.ofAdd (Ideal.Quotient.mk _
      (PadicMeasure.projPlus p (Col p (1 : NormCompatUnits p)))) = 1
    rw [Col_one, map_zero, map_zero]; rfl
  map_mul' u v := by
    change Multiplicative.ofAdd (Ideal.Quotient.mk _
      (PadicMeasure.projPlus p (Col p (u * v)))) = _
    rw [Col_add, map_add, map_add, ofAdd_add]

@[simp] theorem ColPlusMul_apply (hp2 : p ≠ 2) (u : NormCompatUnits p) :
    ColPlusMul p hp2 u = Multiplicative.ofAdd
      (Ideal.Quotient.mk (PadicMeasure.zetaIdealPlus p hp2)
        (PadicMeasure.projPlus p (Col p u))) :=
  rfl

/-- **RJW thm:iwasawa 2 (ii), the genuine plus-descent map**: the plus-part of the Coleman
descent, `[u] ↦ [π_*(Col u)] ∈ Λ(𝒢⁺)/I(𝒢⁺)ζ_p`, packaged multiplicatively on
`𝒰⁺_{∞,1}/𝒞⁺_{∞,1}`. It is the restriction of `ColPlusMul` to `𝒰⁺_{∞,1}`, descended through
`𝒞⁺_{∞,1}`: well-defined because for `u ∈ 𝒞⁺_{∞,1}` we have `u ∈ 𝒞_{∞,1}`
(`cycloTower1Plus_le_cycloTower1`) and `u ∈ 𝒰_{∞,1}`, so `Col u ∈ I(𝒢)ζ_p` (the image
computation `col_mem_zetaIdeal_iff_mem_cycloTower1`), whence `π_*(Col u) ∈ I(𝒢⁺)ζ_p`
(`projPlus_zetaIdeal_le_zetaIdealPlus`). This is the genuine RJW plus map; its bijectivity
(`colDescentPlusMul_bijective`) is the §12.5 collapse. -/
def colDescentPlusMul (hp2 : p ≠ 2) :
    (↥(unitsTower1Plus p) ⧸ (cycloTower1Plus p).subgroupOf (unitsTower1Plus p)) →*
      Multiplicative
        (PadicMeasure p (PadicMeasure.GPlus p) ⧸ PadicMeasure.zetaIdealPlus p hp2) := by
  refine QuotientGroup.lift ((cycloTower1Plus p).subgroupOf (unitsTower1Plus p))
    ((ColPlusMul p hp2).comp (unitsTower1Plus p).subtype) ?_
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, (unitsTower1Plus p).coe_subtype, ColPlusMul_apply]
  -- `[π_*(Col x)] = 0`: `x ∈ 𝒞_{∞,1}` ⟹ `Col x ∈ I(𝒢)ζ_p` ⟹ `π_*(Col x) ∈ I(𝒢⁺)ζ_p`
  have hxcyclo : (x : NormCompatUnits p) ∈ cycloTower1 p :=
    cycloTower1Plus_le_cycloTower1 p hx
  have hmem : Col p (x : NormCompatUnits p) ∈ PadicMeasure.zetaIdeal p hp2 :=
    col_mem_zetaIdeal_of_mem_cycloTower1 p hp2 hxcyclo
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (projPlus_zetaIdeal_le_zetaIdealPlus p hp2 hmem)]; rfl

/-! ## Plus-equivariance of the Coleman map (RJW §12.5, the injectivity input)

The Galois fixed-field characterisation `K_n⁺ = (K_n)^{⟨σ_{-1}⟩}`
(`mem_localUnitsOnePlus_iff_galAut_fixed`, `GaloisAction.lean`) lets us transport
`c`-invariance from a plus-tower unit `u` to its Coleman image `Col u`: a plus-tower unit is
fixed by complex conjugation `σ_{-1}` levelwise, hence `σ_{-1}·u = u` in `𝒰_∞`
(`galNCU`), and `Col(σ_{-1}·u) = [−1]·Col u = c·Col u` (`Col_galNCU_eq_dirac_mul`), so
`c·Col u = Col u`, i.e. `Col u ∈ Λ(𝒢)⁺`. -/

/-- A plus-tower unit is fixed by complex conjugation `σ_{-1}` on `𝒰_∞`: `σ_{-1}·u = u`.
Levelwise `(σ_{-1}·u)_n = σ_{-1}(u_n) = u_n` — for `n ≥ 1` because `u_n ∈ 𝒰⁺_{n,1}` is
`σ_{-1}`-fixed (`mem_localUnitsOnePlus_iff_galAut_fixed`), and for `n = 0` because
`σ_{-1} = id` on `K_0 = ℚ_p` (`galAut … 0 = AlgEquiv.refl`). -/
theorem galNCU_neg_one_of_mem_unitsTower1Plus (hp2 : p ≠ 2) {u : NormCompatUnits p}
    (hu : u ∈ unitsTower1Plus p) : galNCU p (-1) u = u := by
  refine NormCompatUnits.ext (funext fun n => Units.ext ?_)
  rw [galNCU_elems_val]
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- `n = 0`: `σ_{-1} = AlgEquiv.refl` on `K_0`
    subst hn0
    rw [show galAut p (-1) 0 = AlgEquiv.refl from by rw [galAut, dif_neg (by omega)]]
    rfl
  · -- `n ≥ 1`: `u_n ∈ 𝒰⁺_{n,1}` is `σ_{-1}`-fixed
    have hun : u.elems n ∈ localUnitsOne p n := (Subgroup.mem_inf.1 (hu n hn)).1
    exact (mem_localUnitsOnePlus_iff_galAut_fixed p hp2 hn hun).1 (hu n hn)

/-- **Plus-equivariance of the Coleman map** (RJW §12.5): for a plus-tower unit
`u ∈ 𝒰⁺_{∞,1}`, the Coleman image `Col u` is `c`-invariant, i.e. lies in the plus part
`Λ(𝒢)⁺`. Proof: `σ_{-1}·u = u` (`galNCU_neg_one_of_mem_unitsTower1Plus`), so
`c·Col u = [−1]·Col u = Col(σ_{-1}·u) = Col u` (`Col_galNCU_eq_dirac_mul`, `cAct`). -/
theorem Col_mem_plusPart_of_mem_unitsTower1Plus (hp2 : p ≠ 2) {u : NormCompatUnits p}
    (hu : u ∈ unitsTower1Plus p) : Col p u ∈ PadicMeasure.plusPart p := by
  rw [PadicMeasure.mem_plusPart_iff]
  -- `[−1]·Col u = Col(σ_{-1}·u) = Col u`
  rw [← Col_galNCU_eq_dirac_mul p (-1) u, galNCU_neg_one_of_mem_unitsTower1Plus p hp2 hu]

/-- `𝒞⁺_{∞,1} = 𝒞_{∞,1} ⊓ 𝒰⁺_{∞,1}`: the plus closure-tower is exactly the principal-plus
units inside the full closure-tower (levelwise `cycloClosureOnePlus = cycloClosureOne ⊓
localUnitsPlus`, the only reshuffle of the `⊓`-factors). The `←` inclusion is the step
`u ∈ 𝒞_{∞,1} ∧ u ∈ 𝒰⁺_{∞,1} ⟹ u ∈ 𝒞⁺_{∞,1}` of the injectivity argument. -/
theorem mem_cycloTower1Plus_of_mem_cycloTower1_unitsTower1Plus {u : NormCompatUnits p}
    (hc : u ∈ cycloTower1 p) (hp : u ∈ unitsTower1Plus p) : u ∈ cycloTower1Plus p := by
  intro n hn
  have hcn := hc n hn
  have hpn := hp n hn
  rw [cycloClosureOne, Subgroup.mem_inf] at hcn
  rw [localUnitsOnePlus, Subgroup.mem_inf] at hpn
  rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf]
  exact ⟨⟨hcn.1, hpn.2⟩, hcn.2⟩

/-- The even idempotent `e⁺ = ½([1] + [−1]) ∈ Λ(𝒢)` (the projector onto `Λ(𝒢)⁺`). -/
private noncomputable def ePlus (hp2 : p ≠ 2) : PadicMeasure p ℤ_[p]ˣ :=
  (((PadicLFunctions.isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
    • (1 + PadicMeasure.dirac p (-1 : ℤ_[p]ˣ))

/-- `[−1]·[−1] = 1` in `Λ(𝒢)`. -/
private theorem dirac_neg_one_sq :
    PadicMeasure.dirac p (-1 : ℤ_[p]ˣ) * PadicMeasure.dirac p (-1 : ℤ_[p]ˣ) = 1 := by
  rw [PadicMeasure.units_dirac_mul_dirac, show (-1 : ℤ_[p]ˣ) * (-1) = 1 by rw [neg_mul_neg,
    one_mul], ← PadicMeasure.units_one_def]

/-- `e⁺ ∈ Λ(𝒢)⁺`: `[−1]·e⁺ = ½([−1] + [1]) = e⁺`. -/
private theorem ePlus_mem_plusPart (hp2 : p ≠ 2) : ePlus p hp2 ∈ PadicMeasure.plusPart p := by
  rw [PadicMeasure.mem_plusPart_iff, ePlus, mul_smul_comm, mul_add, mul_one,
    dirac_neg_one_sq p, add_comm]

/-- `π_*` is `ℤ_[p]`-linear (its underlying map is `pushforward`, a `LinearMap`). -/
private theorem projPlus_smul (c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]ˣ) :
    PadicMeasure.projPlus p (c • μ) = c • PadicMeasure.projPlus p μ :=
  (PadicMeasure.pushforward p (PadicMeasure.quotientMk p)).map_smul c μ

/-- `π_*(e⁺) = 1`: under the quotient `mk (−1) = mk 1`, so `e⁺ ↦ ½(1 + 1) = 1`. -/
private theorem projPlus_ePlus (hp2 : p ≠ 2) :
    PadicMeasure.projPlus p (ePlus p hp2) = 1 := by
  rw [ePlus, projPlus_smul, map_add, map_one, PadicMeasure.projPlus_dirac,
    show (QuotientGroup.mk (-1 : ℤ_[p]ˣ) : PadicMeasure.GPlus p) = QuotientGroup.mk 1 from by
      rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff]
      exact ⟨1, by rw [zpow_one, inv_neg, neg_mul, inv_mul_cancel]⟩]
  rw [show (PadicMeasure.dirac p (QuotientGroup.mk (1 : ℤ_[p]ˣ) : PadicMeasure.GPlus p))
      = 1 from by rw [← PadicMeasure.projPlus_dirac, ← PadicMeasure.units_one_def, map_one],
    show (1 : PadicMeasure p (PadicMeasure.GPlus p)) + 1
      = (2 : ℤ_[p]) • (1 : PadicMeasure p (PadicMeasure.GPlus p)) from by rw [two_smul], smul_smul,
    (PadicLFunctions.isUnit_two_padicInt p hp2).val_inv_mul, one_smul]

/-- The plus ζ-ideal pulls back to the ζ-ideal on `c`-invariant measures: if `μ ∈ Λ(𝒢)⁺`
and `π_*(μ) ∈ I(𝒢⁺)ζ_p`, then `μ ∈ I(𝒢)ζ_p`. `I(𝒢⁺)ζ_p = π_*(I(𝒢)ζ_p)`
(`zetaIdealPlus_eq_map_projPlus`), so `π_*(μ) = π_*(ν)` for some `ν ∈ I(𝒢)ζ_p`. Replacing `ν`
by its plus part `e⁺·ν` (still in `I(𝒢)ζ_p` since it is an ideal, and with the same
pushforward since `π_*(e⁺) = 1`), both `μ` and `e⁺·ν` lie in `Λ(𝒢)⁺` where `π_*` is injective
(`plusSection_projPlus`), so `μ = e⁺·ν ∈ I(𝒢)ζ_p`. -/
theorem mem_zetaIdeal_of_mem_plusPart_projPlus (hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ}
    (hμ : μ ∈ PadicMeasure.plusPart p)
    (hproj : PadicMeasure.projPlus p μ ∈ PadicMeasure.zetaIdealPlus p hp2) :
    μ ∈ PadicMeasure.zetaIdeal p hp2 := by
  -- `π_*(μ) ∈ π_*(I(𝒢)ζ_p)`, so `π_*(ν) = π_*(μ)` with `ν ∈ I(𝒢)ζ_p`
  rw [zetaIdealPlus_eq_map_projPlus p hp2, Ideal.mem_map_iff_of_surjective _
    (PadicMeasure.projPlus_surjective p hp2)] at hproj
  obtain ⟨ν, hν, hμν⟩ := hproj
  -- the plus part `e⁺·ν ∈ I(𝒢)ζ_p ∩ Λ(𝒢)⁺` with `π_*(e⁺·ν) = π_*(ν) = π_*(μ)`
  set ν' := ePlus p hp2 * ν with hν'
  have hν'ideal : ν' ∈ PadicMeasure.zetaIdeal p hp2 := Ideal.mul_mem_left _ _ hν
  have hν'plus : ν' ∈ PadicMeasure.plusPart p := by
    rw [hν', mul_comm]; exact PadicMeasure.mul_mem_plusPart p (ePlus_mem_plusPart p hp2)
  have hprojν' : PadicMeasure.projPlus p ν' = PadicMeasure.projPlus p μ := by
    rw [hν', map_mul, projPlus_ePlus p hp2]
    exact (one_mul _).trans hμν
  -- `π_*` injective on `Λ(𝒢)⁺`, so `μ = ν' ∈ I(𝒢)ζ_p`
  have hμeq : ν' = μ := by
    have h := congrArg (PadicMeasure.plusSection p hp2) hprojν'
    rwa [PadicMeasure.plusSection_projPlus p hp2 hν'plus,
      PadicMeasure.plusSection_projPlus p hp2 hμ] at h
  rw [← hμeq]; exact hν'ideal

/-- **The plus-descent `colDescentPlusMul` is injective** (RJW §12.5, the `⟨c⟩`-invariants
half now discharged via the Galois fixed-field). For a plus-tower unit `u` with
`[π_*(Col u)] = 0`:
* `Col u ∈ Λ(𝒢)⁺` (plus-equivariance `Col_mem_plusPart_of_mem_unitsTower1Plus`, from the
  Galois characterisation `K_n⁺ = (K_n)^{⟨σ_{-1}⟩}`);
* `π_*(Col u) ∈ I(𝒢⁺)ζ_p`, so `Col u ∈ I(𝒢)ζ_p` (`mem_zetaIdeal_of_mem_plusPart_projPlus`);
* hence `u ∈ 𝒞_{∞,1}` (`col_mem_zetaIdeal_iff_mem_cycloTower1`, the `→` direction), and
  `u ∈ 𝒞⁺_{∞,1}` since `u` is plus (`mem_cycloTower1Plus_of_mem_cycloTower1_unitsTower1Plus`),
i.e. `[u] = 0`. (Transitively this still rests on the deferred image identity `col_image`
through `col_mem_zetaIdeal_iff_mem_cycloTower1`; no *additional* gap is introduced.) -/
theorem colDescentPlusMul_injective (hp2 : p ≠ 2) :
    Function.Injective (colDescentPlusMul p hp2) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | _ u =>
    -- `colDescentPlusMul [u] = ofAdd [π_*(Col u)] = 1`, i.e. `π_*(Col u) ∈ I(𝒢⁺)ζ_p`
    rw [colDescentPlusMul, QuotientGroup.lift_mk, MonoidHom.comp_apply,
      (unitsTower1Plus p).coe_subtype, ColPlusMul_apply] at hx
    have hproj : PadicMeasure.projPlus p (Col p (u : NormCompatUnits p))
        ∈ PadicMeasure.zetaIdealPlus p hp2 := by
      rwa [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff,
        Ideal.Quotient.eq_zero_iff_mem] at hx
    -- `Col u ∈ Λ(𝒢)⁺` (plus-equivariance), so `Col u ∈ I(𝒢)ζ_p`
    have hplus : Col p (u : NormCompatUnits p) ∈ PadicMeasure.plusPart p :=
      Col_mem_plusPart_of_mem_unitsTower1Plus p hp2 u.2
    have hzeta : Col p (u : NormCompatUnits p) ∈ PadicMeasure.zetaIdeal p hp2 :=
      mem_zetaIdeal_of_mem_plusPart_projPlus p hp2 hplus hproj
    -- hence `u ∈ 𝒞_{∞,1}`, and being plus, `u ∈ 𝒞⁺_{∞,1}`, i.e. `[u] = 1`
    have huunit : (u : NormCompatUnits p) ∈ unitsTower1 p :=
      unitsTower1Plus_le_unitsTower1 p u.2
    have hcyclo : (u : NormCompatUnits p) ∈ cycloTower1 p :=
      mem_cycloTower1_of_col_mem_zetaIdeal p hp2 huunit hzeta
    have hcycloPlus : (u : NormCompatUnits p) ∈ cycloTower1Plus p :=
      mem_cycloTower1Plus_of_mem_cycloTower1_unitsTower1Plus p hcyclo u.2
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hcycloPlus

/-- **RJW thm:iwasawa 2 (ii) — the milestone bijectivity**: the plus-descent
`colDescentPlusMul : 𝒰⁺_{∞,1}/𝒞⁺_{∞,1} → Λ(𝒢⁺)/I(𝒢⁺)ζ_p` is bijective. The injectivity is
proved (`colDescentPlusMul_injective`), enabled by the Galois fixed-field characterisation
`K_n⁺ = (K_n)^{⟨σ_{-1}⟩}` (`mem_localUnitsOnePlus_iff_galAut_fixed`, `GaloisAction.lean`).

Surjectivity is the one remaining gap, and it reduces to the **single** deferred identity
`col_image_cycloTower1_eq_zetaIdeal` (Main.lean): RJW's `(−)^{⟨c⟩}`-collapse of the
fundamental sequence (i) `0 → 𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p → ℤ_p(1) → 0` makes
`colDescentPlusMul` onto because `ℤ_p(1)^{⟨c⟩} = 0` (`p` odd), and the (i) image
`range Col = ker(χ-moment)` (`range_Col_eq_ker_chiMoment`) together with the image
computation `col_image_cycloTower1_eq_zetaIdeal` pins the cokernel. With that identity in
hand (the §13/IMC-deferred core, the SAME blocker as the injectivity input
`col_mem_zetaIdeal_iff_mem_cycloTower1`), both halves close — the milestone bottlenecks on
exactly `col_image_cycloTower1_eq_zetaIdeal`. -/
theorem colDescentPlusMul_bijective (hp2 : p ≠ 2) :
    Function.Bijective (colDescentPlusMul p hp2) :=
  ⟨colDescentPlusMul_injective p hp2, by
    -- DEFERRED: surjectivity reduces to the `⊆` half of `col_image_cycloTower1_eq_zetaIdeal`
    -- (the well-definedness/cokernel pin). The `⊇` half (density-crossing) is now PROVED
    -- (`zetaIdeal_le_col_image`, via `Coleman/ColContinuity.lean`: `Col '' 𝒞_{∞,1}` closed +
    -- Dirac span dense), and the injectivity input `mem_cycloTower1_of_col_mem_zetaIdeal` is
    -- now axiom-clean. The remaining `⊆` is the deferred cyclic-module density
    -- `𝒞_{∞,1} = closure(Λ(𝒢)·wγ(a₀))` (RJW LemmaGeneratorCinfty1, TeX 3573–3578); with it the
    -- `(−)^{⟨c⟩}`-collapse of the fundamental sequence (i) (`ℤ_p(1)^{⟨c⟩} = 0`,
    -- `range_Col_eq_ker_chiMoment`) gives surjectivity. The continuity layer alone does not
    -- supply this tower-level algebraic density.
    sorry⟩

/-- **RJW thm:iwasawa 2 (ii) — THE MILESTONE (TeX 3592–3593)**: the Coleman map induces an
isomorphism of `Λ(𝒢^+)`-modules `𝒰_{∞,1}^+/𝒞_{∞,1}^+ ≅ Λ(𝒢^+)/I(𝒢^+)ζ_p`. This is
`thm:iwasawa` (stated, then unwired, in the §11 chapter), now proved. Stated as the
existence of a `Λ(𝒢^+)`-linear (here `ℤ_[p]`-linear placeholder; the `Λ(𝒢^+)`-structure
on the quotient is wired at execution) isomorphism between the two quotients. -/
theorem iwasawa_theorem (hp2 : p ≠ 2) :
    Nonempty (
      Additive (↥(unitsTower1Plus p) ⧸ (cycloTower1Plus p).subgroupOf (unitsTower1Plus p)) ≃+
      (PadicMeasure p (PadicMeasure.GPlus p) ⧸ PadicMeasure.zetaIdealPlus p hp2)) :=
  -- the genuine plus-descent `[u] ↦ [π_*(Col u)]`, an iso by `colDescentPlusMul_bijective`,
  -- converted from multiplicative to additive shape (`MulEquiv.toAdditive`)
  ⟨MulEquiv.toAdditive
    (MulEquiv.ofBijective (colDescentPlusMul p hp2) (colDescentPlusMul_bijective p hp2))⟩

/-- **RJW thm:iwasawa 2 (i) (TeX 3590–3591)**: the `Λ(𝒢)`-module short exact sequence
`0 → 𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p → ℤ_p(1) → 0`. Stated as the injection
`𝒰_{∞,1}/𝒞_{∞,1} ↪ Λ(𝒢)/I(𝒢)ζ_p` with cokernel `ℤ_p(1)` (the `χ`-moment). -/
theorem iwasawa_exact_sequence (hp2 : p ≠ 2) :
    Nonempty (
      Additive (↥(unitsTower1 p) ⧸ (cycloTower1 p).subgroupOf (unitsTower1 p)) →+
      (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2)) :=
  ⟨colDescent p hp2⟩

end PadicLFunctions.Coleman
