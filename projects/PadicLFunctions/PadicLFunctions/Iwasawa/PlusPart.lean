import PadicLFunctions.Measure.PseudoMeasure
import PadicLFunctions.EisensteinFamily
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The ±-decomposition of Λ(𝒢) and the plus quotient Λ(𝒢⁺)

RJW (arXiv:2309.15692) §11.1 (`sec:measures on galois groups`, TeX 2964–3042). Per the
notes' own identification (TeX 2970: "From now on, we will let Λ(𝒢) be the space of
measures on 𝒢, which we identify with Λ(ℤ_p^×) via the cyclotomic character"), the
Galois group 𝒢 is `ℤ_[p]ˣ`, complex conjugation `c` is `(-1 : ℤ_[p]ˣ)`, and
`𝒢⁺ = 𝒢/⟨c⟩` is the quotient group `GPlus p = ℤ_[p]ˣ ⧸ zpowers (-1)`
(decomposition replan R11.1).

## Main declarations

* `PadicMeasure.invariants`/`antiInvariants` + `isCompl_invariants_antiInvariants`:
  the general ±-eigenspace splitting for an involution of a module with `2` invertible
  (RJW Lem. `lem:decompose plus minus`, TeX 2994–3002; not in mathlib — PR candidate).
* `PadicMeasure.cAct`: the action of `c` on `Λ(ℤ_p^×)` (convolution by `dirac (-1)`),
  `plusPart`/`minusPart`, and the instance of the decomposition lemma.
* `PadicMeasure.mem_plusPart_iff_forall_odd_moment`: the odd-moment membership
  criterion (RJW TeX 3019–3029; p-general in the c-invariance phrasing).
* `PadicMeasure.GPlus` and the pushforward `projPlus : Λ(𝒢) →+* Λ(𝒢⁺)`,
  the even-part section `plusSection`, and the isomorphism Λ(𝒢)⁺ ≅ Λ(𝒢⁺)
  (RJW TeX 3006–3015; functional-route proof, replan R11.2).
-/

open scoped fwdDiff

noncomputable section

namespace PadicMeasure

/-! ## The general ±-decomposition (RJW Lem. `lem:decompose plus minus`) -/

section involution

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The `+1`-eigenspace (invariants) of an endomorphism `σ : M →ₗ[R] M`. -/
def invariants (σ : M →ₗ[R] M) : Submodule R M :=
  LinearMap.ker (σ - LinearMap.id)

/-- The `−1`-eigenspace (anti-invariants) of an endomorphism `σ : M →ₗ[R] M`. -/
def antiInvariants (σ : M →ₗ[R] M) : Submodule R M :=
  LinearMap.ker (σ + LinearMap.id)

lemma mem_invariants_iff {σ : M →ₗ[R] M} {x : M} : x ∈ invariants σ ↔ σ x = x := by
  rw [invariants, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

lemma mem_antiInvariants_iff {σ : M →ₗ[R] M} {x : M} :
    x ∈ antiInvariants σ ↔ σ x = -x := by
  rw [antiInvariants, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    add_eq_zero_iff_eq_neg]

/-- The plus-projection formula: `(x + σx)/2` lands in the invariants. -/
theorem smul_add_apply_mem_invariants [Invertible (2 : R)] (σ : M →ₗ[R] M)
    (hσ : σ ∘ₗ σ = LinearMap.id) (x : M) :
    (⅟(2 : R)) • (x + σ x) ∈ invariants σ := by
  have hσσ : σ (σ x) = x := LinearMap.ext_iff.1 hσ x
  rw [mem_invariants_iff, map_smul, map_add, hσσ, add_comm]

/-- The minus-projection formula: `(x − σx)/2` lands in the anti-invariants. -/
theorem smul_sub_apply_mem_antiInvariants [Invertible (2 : R)] (σ : M →ₗ[R] M)
    (hσ : σ ∘ₗ σ = LinearMap.id) (x : M) :
    (⅟(2 : R)) • (x - σ x) ∈ antiInvariants σ := by
  have hσσ : σ (σ x) = x := LinearMap.ext_iff.1 hσ x
  rw [mem_antiInvariants_iff, map_smul, map_sub, hσσ, ← smul_neg, neg_sub]

/-- **RJW Lem. `lem:decompose plus minus` (TeX 2994–3002)**: for an involution `σ` of an
`R`-module `M` with `2` invertible in `R`, the module decomposes as the internal direct
sum of the `±1`-eigenspaces, via the idempotents `(1 ± σ)/2`. (The source states this
for a module with a continuous 𝒢-action; only the action of `c` is used, i.e. exactly
an involution.) Not in mathlib (verified absent); PR candidate. -/
theorem isCompl_invariants_antiInvariants [Invertible (2 : R)] (σ : M →ₗ[R] M)
    (hσ : σ ∘ₗ σ = LinearMap.id) :
    IsCompl (invariants σ) (antiInvariants σ) := by
  refine ⟨?_, ?_⟩
  · -- Disjointness: `σx = x` and `σx = −x` force `x = −x`, hence `2•x = 0`, hence `x = 0`.
    rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [mem_invariants_iff] at hx
    rw [mem_antiInvariants_iff] at hx'
    have hxx : x = -x := hx.symm.trans hx'
    have h2 : (2 : R) • x = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 hxx
    have := invOf_smul_smul (2 : R) x
    rwa [h2, smul_zero, eq_comm] at this
  · -- Codisjointness: `x = ⅟2•(x+σx) + ⅟2•(x−σx)` with parts in the two eigenspaces.
    rw [codisjoint_iff_le_sup]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨(⅟(2 : R)) • (x + σ x), smul_add_apply_mem_invariants σ hσ x,
      (⅟(2 : R)) • (x - σ x), smul_sub_apply_mem_antiInvariants σ hσ x, ?_⟩
    rw [← smul_add, show x + σ x + (x - σ x) = (2 : R) • x by rw [two_smul]; abel,
      invOf_smul_smul]

end involution

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## ℤ_p-bilinearity of the convolution product

The `SMulCommClass`/`IsScalarTower` instances making `Λ(ℤ_p^×)` an honest
ℤ_[p]-algebra-like object (the gap noted at the §8 pass). -/

instance : SMulCommClass ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure p ℤ_[p]ˣ) := by
  refine ⟨fun c μ ν => LinearMap.ext fun f => ?_⟩
  -- `c • (μ * ν) = μ * (c • ν)`: pull the scalar through the inner integral
  change (c • (μ * ν)) f = (μ * (c • ν)) f
  rw [LinearMap.smul_apply, conv_mul_apply, conv_mul_apply]
  have hinner : innerInt p (c • ν) (f.comp (mulCM₂ ℤ_[p]ˣ))
      = c • innerInt p ν (f.comp (mulCM₂ ℤ_[p]ˣ)) := by
    ext x
    rw [innerInt_apply, ContinuousMap.smul_apply, innerInt_apply, LinearMap.smul_apply]
  rw [hinner, map_smul]

instance : IsScalarTower ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure p ℤ_[p]ˣ) := by
  refine ⟨fun c μ ν => LinearMap.ext fun f => ?_⟩
  -- `(c • μ) * ν = c • (μ * ν)`: the outer measure carries the scalar pointwise
  change ((c • μ) * ν) f = (c • (μ * ν)) f
  rw [LinearMap.smul_apply, conv_mul_apply, conv_mul_apply, LinearMap.smul_apply]

/-! ## The c-action on Λ(𝒢) (c = complex conjugation = −1 ∈ ℤ_p^× under χ) -/

/-- The action of complex conjugation on `Λ(𝒢) = Λ(ℤ_p^×)`: convolution by the Dirac
measure at `c = -1` (under the cyclotomic identification, RJW TeX 2970/2992). -/
def cAct : PadicMeasure p ℤ_[p]ˣ →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p]ˣ :=
  LinearMap.mulLeft ℤ_[p] (dirac p (-1 : ℤ_[p]ˣ))

@[simp]
lemma cAct_apply (μ : PadicMeasure p ℤ_[p]ˣ) :
    cAct p μ = dirac p (-1 : ℤ_[p]ˣ) * μ :=
  LinearMap.mulLeft_apply ℤ_[p] _ _

/-- `c` is an involution: `[−1]·[−1] = [1]`. -/
theorem cAct_involutive : cAct p ∘ₗ cAct p = LinearMap.id := by
  refine LinearMap.ext fun μ => ?_
  rw [LinearMap.comp_apply, cAct_apply, cAct_apply, LinearMap.id_apply, ← mul_assoc,
    units_dirac_mul_dirac, show (-1 : ℤ_[p]ˣ) * (-1) = 1 by rw [neg_mul_neg, one_mul],
    ← units_one_def, one_mul]

/-- `Λ(𝒢)⁺`: the c-invariant measures (the image of the idempotent `(1+c)/2`).
Under the identification of RJW TeX 3017 this *is* `Λ(𝒢⁺)` viewed inside `Λ(𝒢)`. -/
def plusPart : Submodule ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) :=
  invariants (cAct p)

/-- `Λ(𝒢)⁻`: the c-anti-invariant measures. -/
def minusPart : Submodule ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) :=
  antiInvariants (cAct p)

lemma mem_plusPart_iff {μ : PadicMeasure p ℤ_[p]ˣ} :
    μ ∈ plusPart p ↔ dirac p (-1 : ℤ_[p]ˣ) * μ = μ := by
  rw [plusPart, mem_invariants_iff, cAct_apply]

lemma mem_minusPart_iff {μ : PadicMeasure p ℤ_[p]ˣ} :
    μ ∈ minusPart p ↔ dirac p (-1 : ℤ_[p]ˣ) * μ = -μ := by
  rw [minusPart, mem_antiInvariants_iff, cAct_apply]

/-- `plusPart` is closed under multiplication by arbitrary measures (it is the ideal
`e⁺Λ(𝒢)`). -/
theorem mul_mem_plusPart {μ ν : PadicMeasure p ℤ_[p]ˣ} (hμ : μ ∈ plusPart p) :
    ν * μ ∈ plusPart p := by
  rw [mem_plusPart_iff] at hμ ⊢
  rw [mul_left_comm, hμ]

/-- **RJW Lem. `lem:decompose plus minus` for Λ(𝒢)** (TeX 3004: "We are assuming that
`p` is odd, so Λ(𝒢) ≅ Λ(𝒢)⁺ ⊕ Λ(𝒢)⁻"). -/
theorem isCompl_plusPart_minusPart (hp2 : p ≠ 2) :
    IsCompl (plusPart p) (minusPart p) := by
  haveI : Invertible (2 : ℤ_[p]) := (PadicLFunctions.isUnit_two_padicInt p hp2).invertible
  exact isCompl_invariants_antiInvariants (cAct p) (cAct_involutive p)

/-! ## The odd-moment criterion (RJW TeX 3019–3029) -/

/-- Moments of the c-translate: `∫ x^k d([−1]·μ) = (−1)^k ∫ x^k dμ`
(the computation `χ(c) = −1` of the source's proof, TeX 3026–3028). -/
theorem cAct_apply_unitsPowCM (μ : PadicMeasure p ℤ_[p]ˣ) (k : ℕ) :
    (dirac p (-1 : ℤ_[p]ˣ) * μ) (unitsPowCM p k) = (-1) ^ k * μ (unitsPowCM p k) := by
  have hdirac : (dirac p (-1 : ℤ_[p]ˣ)) (unitsPowCM p k) = (-1) ^ k := by
    rw [dirac_apply]
    change ((-1 : ℤ_[p]ˣ) : ℤ_[p]) ^ k = (-1) ^ k
    rw [Units.val_neg, Units.val_one]
  rw [units_mul_apply_unitsPowCM, hdirac]

/-- **RJW §11.1, third lemma (TeX 3019–3029)**: `μ ∈ Λ(𝒢⁺)` (= c-invariance, by the
TeX 3017 identification) if and only if all odd moments `∫_𝒢 χ(x)^k·μ`, `k ≥ 1` odd,
vanish. This direction-pair is p-general (`ℤ_[p]` has characteristic zero); the
*decomposition* interpretation needs `p ≠ 2`. -/
theorem mem_plusPart_iff_forall_odd_moment {μ : PadicMeasure p ℤ_[p]ˣ} :
    μ ∈ plusPart p ↔ ∀ k : ℕ, Odd k → μ (unitsPowCM p k) = 0 := by
  rw [mem_plusPart_iff]
  constructor
  · -- c-invariance: for odd `k`, the moment equals its own negative, hence vanishes.
    intro h k hk
    have heval := LinearMap.congr_fun h (unitsPowCM p k)
    rw [cAct_apply_unitsPowCM, hk.neg_one_pow, neg_one_mul] at heval
    exact add_self_eq_zero.1 (add_eq_zero_iff_eq_neg.2 heval.symm)
  · -- all odd moments vanish: the difference `[−1]·μ − μ` is killed on every `x^k`.
    intro h
    have hzero : (dirac p (-1 : ℤ_[p]ˣ) * μ - μ) = 0 := by
      refine eq_zero_of_forall_unitsPowCM_eq_zero p _ fun k _ => ?_
      rw [LinearMap.sub_apply, cAct_apply_unitsPowCM]
      rcases Nat.even_or_odd k with hk | hk
      · rw [hk.neg_one_pow, one_mul, sub_self]
      · rw [h k hk, mul_zero, sub_zero]
    exact sub_eq_zero.1 hzero

/-! ## The quotient group 𝒢⁺ = ℤ_p^×/{±1} and Λ(𝒢⁺) -/

/-- `𝒢⁺ = 𝒢/⟨c⟩`, identified through the cyclotomic character with `ℤ_p^×/{±1}`
(RJW TeX 2992). The quotient of the compact group `ℤ_[p]ˣ` by the closed (finite)
subgroup `{±1}`; mathlib provides the compact topological-group structure, and the
generalised convolution algebra (`PadicMeasure.conv`, replan R11.5) provides the ring
structure on its measures. -/
abbrev GPlus := ℤ_[p]ˣ ⧸ Subgroup.zpowers (-1 : ℤ_[p]ˣ)

/-- The quotient projection `𝒢 → 𝒢⁺` as a continuous map. -/
def quotientMk : C(ℤ_[p]ˣ, GPlus p) :=
  ⟨QuotientGroup.mk, continuous_quotient_mk'⟩

/-- The pushforward `π_* : Λ(𝒢) → Λ(𝒢⁺)` along the quotient projection — the
"natural surjection" of RJW TeX 3012, as the inverse-limit-free measure-functional
incarnation. Ring-hom because `mk` is a (continuous) monoid hom. -/
def projPlus : PadicMeasure p ℤ_[p]ˣ →+* PadicMeasure p (GPlus p) where
  toFun := pushforward p (quotientMk p)
  map_one' := by
    -- `π_* δ_1 = δ_{mk 1} = δ_1`
    rw [conv_one_def, pushforward_dirac, conv_one_def]; congr 1
  map_mul' μ ν := by
    -- the two inner integrals agree pointwise via `mk (x*y) = mk x * mk y`
    refine LinearMap.ext fun f => ?_
    rw [pushforward_apply, conv_mul_apply, conv_mul_apply, pushforward_apply]
    congr 1
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma projPlus_apply (μ : PadicMeasure p ℤ_[p]ˣ) (f : C(GPlus p, ℤ_[p])) :
    projPlus p μ f = μ (f.comp (quotientMk p)) := rfl

@[simp]
lemma projPlus_dirac (u : ℤ_[p]ˣ) :
    projPlus p (dirac p u) = dirac p (QuotientGroup.mk u : GPlus p) := rfl

/-- The augmentation commutes with the projection: `deg⁺ ∘ π_* = deg`. -/
theorem deg_projPlus (μ : PadicMeasure p ℤ_[p]ˣ) :
    deg p (projPlus p μ) = deg p μ := by
  change (projPlus p μ) 1 = μ 1
  rw [projPlus_apply]; congr 1

/-! ## The even-part section and the isomorphism Λ(𝒢)⁺ ≅ Λ(𝒢⁺) -/

/-- Translation by `−1` on `ℤ_[p]ˣ`, as a continuous map (the `c`-translation of
function arguments). -/
def negTranslate : C(ℤ_[p]ˣ, ℤ_[p]ˣ) :=
  ⟨fun u => -u, by
    have hfun : (fun u : ℤ_[p]ˣ => -u) = (fun u : ℤ_[p]ˣ => (-1 : ℤ_[p]ˣ) * u) := by
      funext u; rw [neg_one_mul]
    rw [hfun]; exact continuous_const.mul continuous_id⟩

/-- **Key computation**: convolution by `dirac (−1)` is argument-translation by `−1`.
`(dirac (−1) ⋆ μ) f = ∫ f(−u) dμ(u)`. Used throughout the ±-section results below. -/
private lemma dirac_neg_one_mul_apply (μ : PadicMeasure p ℤ_[p]ˣ) (f : C(ℤ_[p]ˣ, ℤ_[p])) :
    (dirac p (-1 : ℤ_[p]ˣ) * μ) f = μ (f.comp (negTranslate p)) := by
  rw [conv_mul_apply, dirac_apply, innerInt_apply]
  congr 1
  exact ContinuousMap.ext fun u => by
    change f ((-1 : ℤ_[p]ˣ) * u) = f (-u)
    rw [neg_one_mul]

/-- The even part of a continuous function on `𝒢`: `f ↦ (f + f∘c)/2` (`p ≠ 2`). -/
def evenPart (hp2 : p ≠ 2) (f : C(ℤ_[p]ˣ, ℤ_[p])) : C(ℤ_[p]ˣ, ℤ_[p]) :=
  (((PadicLFunctions.isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
    • (f + f.comp (negTranslate p))

/-- An even continuous function on `𝒢` descends to a continuous function on `𝒢⁺`
(soundness: the `{±1}`-cosets are `{u, −u}`; continuity: `mk` is a quotient map). -/
def descendEven (g : C(ℤ_[p]ˣ, ℤ_[p])) (hg : ∀ u : ℤ_[p]ˣ, g (-u) = g u) :
    C(GPlus p, ℤ_[p]) :=
  ⟨fun x => Quotient.liftOn' x g (by
    -- soundness: the `{±1}`-coset of `x` is `{x, −x}`, on which `g` is constant
    intro x y hxy
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_zpowers_iff] at hxy
    obtain ⟨k, hk⟩ := hxy
    rcases Int.even_or_odd k with hke | hko
    · rw [hke.neg_one_zpow] at hk
      have hyx : y = x := by
        have h := hk.symm; rw [inv_mul_eq_one] at h; exact h.symm
      rw [hyx]
    · rw [hko.neg_one_zpow] at hk
      have hy : y = -x := by
        have h := hk.symm; rw [inv_mul_eq_iff_eq_mul] at h; rw [h, mul_neg_one]
      rw [hy, hg]), by
    -- continuity: `mk` is a quotient map, and the lift composed with `mk` is `g`
    have hmk := QuotientGroup.isQuotientMap_mk (Subgroup.zpowers (-1 : ℤ_[p]ˣ))
    rw [hmk.continuous_iff]
    exact g.continuous⟩

@[simp]
lemma descendEven_mk (g : C(ℤ_[p]ˣ, ℤ_[p])) (hg : ∀ u : ℤ_[p]ˣ, g (-u) = g u)
    (u : ℤ_[p]ˣ) :
    descendEven p g hg (QuotientGroup.mk u) = g u := rfl

/-- `descendEven` depends only on the underlying function (its coherence proof is
irrelevant), so equal functions descend to the same measure-function. -/
private lemma descendEven_congr {g₁ g₂ : C(ℤ_[p]ˣ, ℤ_[p])} (h : g₁ = g₂)
    (h₁ : ∀ u : ℤ_[p]ˣ, g₁ (-u) = g₁ u) (h₂ : ∀ u : ℤ_[p]ˣ, g₂ (-u) = g₂ u) :
    descendEven p g₁ h₁ = descendEven p g₂ h₂ := by subst h; rfl

lemma evenPart_even (hp2 : p ≠ 2) (f : C(ℤ_[p]ˣ, ℤ_[p])) (u : ℤ_[p]ˣ) :
    evenPart p hp2 f (-u) = evenPart p hp2 f u := by
  simp only [evenPart, ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.comp_apply]
  change _ • (f (-u) + f (-(-u))) = _ • (f u + f (-u))
  rw [neg_neg, add_comm]

/-- The even part of an already-even function is the function itself (here the scalar
`(2)⁻¹·(f + f) = (2)⁻¹·2·f = f`). -/
private lemma evenPart_of_even (hp2 : p ≠ 2) (f : C(ℤ_[p]ˣ, ℤ_[p]))
    (hf : ∀ u : ℤ_[p]ˣ, f (-u) = f u) : evenPart p hp2 f = f := by
  ext u
  simp only [evenPart, ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.comp_apply, smul_eq_mul]
  change _ * (f u + f (-u)) = f u
  rw [hf u, ← two_mul, ← mul_assoc,
    (PadicLFunctions.isUnit_two_padicInt p hp2).val_inv_mul, one_mul]

/-- The even part is invariant under precomposition with the `c`-translation
(`(f∘c)+((f∘c)∘c) = f + f∘c` since `c²=id`). -/
private lemma evenPart_comp_negTranslate (hp2 : p ≠ 2) (f : C(ℤ_[p]ˣ, ℤ_[p])) :
    evenPart p hp2 (f.comp (negTranslate p)) = evenPart p hp2 f := by
  ext u
  simp only [evenPart, ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.comp_apply]
  change _ • (f (-u) + f (-(-u))) = _ • (f u + f (-u))
  rw [neg_neg, add_comm]

/-- The even-part section `σ : Λ(𝒢⁺) → Λ(𝒢)`: `(σν)(f) := ν(descend((f + f∘c)/2))`.
This is the functional-analytic replacement (replan R11.2) for the source's
finite-level inverse of the natural surjection. -/
def plusSection (hp2 : p ≠ 2) :
    PadicMeasure p (GPlus p) →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p]ˣ where
  toFun ν :=
    { toFun := fun f => ν (descendEven p (evenPart p hp2 f) (evenPart_even p hp2 f))
      map_add' := fun f g => by
        -- linearity of `ν` reduces to additivity of `evenPart` (pointwise after `mk`)
        rw [← map_add]
        congr 1
        ext x
        induction x using QuotientGroup.induction_on with
        | _ u =>
          rw [ContinuousMap.add_apply, descendEven_mk, descendEven_mk, descendEven_mk]
          simp only [evenPart, ContinuousMap.smul_apply, ContinuousMap.add_apply,
            ContinuousMap.comp_apply, smul_eq_mul]
          change _ * (f u + g u + (f (-u) + g (-u)))
            = _ * (f u + f (-u)) + _ * (g u + g (-u))
          ring
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        ext x
        induction x using QuotientGroup.induction_on with
        | _ u =>
          rw [ContinuousMap.smul_apply, descendEven_mk, descendEven_mk]
          simp only [evenPart, ContinuousMap.smul_apply, ContinuousMap.add_apply,
            ContinuousMap.comp_apply, smul_eq_mul]
          change _ * (c • f u + c • f (-u)) = c • (_ * (f u + f (-u)))
          simp only [smul_eq_mul]; ring }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The section lands in the plus part. -/
theorem plusSection_mem_plusPart (hp2 : p ≠ 2) (ν : PadicMeasure p (GPlus p)) :
    plusSection p hp2 ν ∈ plusPart p := by
  rw [mem_plusPart_iff]
  refine LinearMap.ext fun f => ?_
  -- `c`-invariance: `(σν)(f∘c) = (σν)(f)` because `evenPart (f∘c) = evenPart f`
  rw [dirac_neg_one_mul_apply]
  change ν (descendEven p (evenPart p hp2 (f.comp (negTranslate p))) _)
    = ν (descendEven p (evenPart p hp2 f) _)
  congr 1
  exact descendEven_congr p (evenPart_comp_negTranslate p hp2 f) _ _

/-- `mk (−u) = mk u` in `𝒢⁺` (the defining `{±1}`-collapse). -/
private lemma quotientMk_neg (u : ℤ_[p]ˣ) :
    (QuotientGroup.mk (-u) : GPlus p) = QuotientGroup.mk u := by
  rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  exact ⟨1, by rw [zpow_one, inv_neg, neg_mul, inv_mul_cancel]⟩

/-- Any pullback `g ∘ mk` from `𝒢⁺` is an even function on `𝒢`. -/
private lemma comp_quotientMk_even (g : C(GPlus p, ℤ_[p])) (u : ℤ_[p]ˣ) :
    (g.comp (quotientMk p)) (-u) = (g.comp (quotientMk p)) u := by
  change g (QuotientGroup.mk (-u)) = g (QuotientGroup.mk u)
  rw [quotientMk_neg]

/-- `descendEven (g ∘ mk) = g`: descending a pullback recovers the original. -/
private lemma descendEven_comp_quotientMk (g : C(GPlus p, ℤ_[p]))
    (hg : ∀ u : ℤ_[p]ˣ, (g.comp (quotientMk p)) (-u) = (g.comp (quotientMk p)) u) :
    descendEven p (g.comp (quotientMk p)) hg = g := by
  ext x
  induction x using QuotientGroup.induction_on with
  | _ u => rw [descendEven_mk]; rfl

/-- `π_* ∘ σ = id`: the section is a right inverse (hence `π_*` is surjective). -/
theorem projPlus_plusSection (hp2 : p ≠ 2) (ν : PadicMeasure p (GPlus p)) :
    projPlus p (plusSection p hp2 ν) = ν := by
  refine LinearMap.ext fun g => ?_
  rw [projPlus_apply]
  change ν (descendEven p (evenPart p hp2 (g.comp (quotientMk p))) _) = ν g
  congr 1
  -- `evenPart (g∘mk) = g∘mk` (even), and `descendEven (g∘mk) = g`
  rw [descendEven_congr p (evenPart_of_even p hp2 _ (comp_quotientMk_even p g)) _
    (comp_quotientMk_even p g)]
  exact descendEven_comp_quotientMk p g (comp_quotientMk_even p g)

/-- Descending an even function and pulling it back recovers it: `descend g ∘ mk = g`
(here `g = evenPart f`). -/
private lemma descendEven_comp (g : C(ℤ_[p]ˣ, ℤ_[p])) (hg : ∀ u : ℤ_[p]ˣ, g (-u) = g u) :
    (descendEven p g hg).comp (quotientMk p) = g := by
  ext u; change descendEven p g hg (QuotientGroup.mk u) = g u; rw [descendEven_mk]

/-- For a `c`-invariant `μ`, the even part integrates to the same value: `μ (evenPart f) = μ f`. -/
private lemma apply_evenPart_of_mem_plusPart (hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ}
    (hμ : μ ∈ plusPart p) (f : C(ℤ_[p]ˣ, ℤ_[p])) :
    μ (evenPart p hp2 f) = μ f := by
  -- `μ (f∘c) = μ f` since `dirac(−1)·μ = μ`
  have hcomp : μ (f.comp (negTranslate p)) = μ f := by
    rw [← dirac_neg_one_mul_apply, (mem_plusPart_iff p).1 hμ]
  rw [evenPart, map_smul, map_add, hcomp, smul_eq_mul, ← two_mul, ← mul_assoc,
    (PadicLFunctions.isUnit_two_padicInt p hp2).val_inv_mul, one_mul]

/-- `σ ∘ π_* = id` on the plus part: a c-invariant measure is determined by its
pushforward (the injectivity half of RJW TeX 3006–3015). -/
theorem plusSection_projPlus (hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ}
    (hμ : μ ∈ plusPart p) :
    plusSection p hp2 (projPlus p μ) = μ := by
  refine LinearMap.ext fun f => ?_
  change (projPlus p μ) (descendEven p (evenPart p hp2 f) (evenPart_even p hp2 f)) = μ f
  rw [projPlus_apply, descendEven_comp, apply_evenPart_of_mem_plusPart p hp2 hμ]

theorem projPlus_surjective (hp2 : p ≠ 2) :
    Function.Surjective (projPlus p) :=
  fun ν => ⟨plusSection p hp2 ν, projPlus_plusSection p hp2 ν⟩

/-- **RJW §11.1, second lemma (TeX 3006–3015)**: the natural isomorphism
`Λ(𝒢)⁺ ≅ Λ(𝒢⁺)`, realised by `π_*` restricted to the plus part, with inverse the
even-part section. (Multiplicativity is `projPlus.map_mul` on representatives.) -/
def plusEquiv (hp2 : p ≠ 2) :
    plusPart p ≃ₗ[ℤ_[p]] PadicMeasure p (GPlus p) :=
  LinearEquiv.ofLinear
    (pushforward p (quotientMk p) ∘ₗ (plusPart p).subtype)
    ((plusSection p hp2).codRestrict (plusPart p) (plusSection_mem_plusPart p hp2))
    (by
      -- `π_* ∘ σ = id` (note `pushforward (quotientMk) = projPlus` definitionally)
      refine LinearMap.ext fun ν => ?_
      exact projPlus_plusSection p hp2 ν)
    (by
      -- `σ ∘ π_* = id` on the plus part, via `Subtype.ext`
      refine LinearMap.ext fun μ => ?_
      exact Subtype.ext (plusSection_projPlus p hp2 μ.2))

/-- The projection kills the minus part: an even pullback `g∘mk` is integrated to `0`
by a `c`-anti-invariant measure (it equals its own negative). -/
private lemma projPlus_eq_zero_of_mem_minusPart {ρ : PadicMeasure p ℤ_[p]ˣ}
    (hρ : ρ ∈ minusPart p) : projPlus p ρ = 0 := by
  refine LinearMap.ext fun g => ?_
  rw [projPlus_apply, LinearMap.zero_apply]
  -- the pullback `g ∘ mk` is even, hence fixed by the `c`-translation
  have heven : (g.comp (quotientMk p)).comp (negTranslate p) = g.comp (quotientMk p) :=
    ContinuousMap.ext fun u => by
      change (g.comp (quotientMk p)) (-u) = (g.comp (quotientMk p)) u
      exact comp_quotientMk_even p g u
  -- but on a `c`-anti-invariant measure this value equals its negative
  have hneg : ρ (g.comp (quotientMk p)) = -ρ (g.comp (quotientMk p)) := by
    have h := dirac_neg_one_mul_apply p ρ (g.comp (quotientMk p))
    rw [heven, (mem_minusPart_iff p).1 hρ, LinearMap.neg_apply] at h
    exact h.symm
  exact add_self_eq_zero.1 (add_eq_zero_iff_eq_neg.2 hneg)

/-- The kernel of `π_*` is the minus part… -/
theorem projPlus_eq_zero_iff (hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ} :
    projPlus p μ = 0 ↔ μ ∈ minusPart p := by
  constructor
  · intro h
    -- decompose `μ = μ⁺ + μ⁻`; then `projPlus μ = projPlus μ⁺`, so `μ⁺ = σ 0 = 0`
    obtain ⟨a, b, hab, -⟩ :=
      Submodule.existsUnique_add_of_isCompl (isCompl_plusPart_minusPart p hp2) μ
    have hpa : projPlus p (a : PadicMeasure p ℤ_[p]ˣ) = 0 := by
      have : projPlus p μ = projPlus p (a : PadicMeasure p ℤ_[p]ˣ) := by
        rw [← hab, map_add, projPlus_eq_zero_of_mem_minusPart p b.2, add_zero]
      rw [← this, h]
    have haz : (a : PadicMeasure p ℤ_[p]ˣ) = 0 := by
      have := plusSection_projPlus p hp2 a.2
      rw [hpa, map_zero] at this
      exact this.symm
    rw [← hab, haz, zero_add]
    exact b.2
  · intro h
    exact projPlus_eq_zero_of_mem_minusPart p h

/-- …equivalently the principal ideal `([−1] − [1])·Λ(𝒢)` (so
`Λ(𝒢⁺) ≅ Λ(𝒢)/([−1]−[1])` — the ring-quotient picture used for transporting the
augmentation-ideal results). -/
theorem ker_projPlus (hp2 : p ≠ 2) :
    RingHom.ker (projPlus p)
      = Ideal.span {(dirac p (-1 : ℤ_[p]ˣ) - 1 : PadicMeasure p ℤ_[p]ˣ)} := by
  refine Ideal.ext fun x => ?_
  rw [RingHom.mem_ker, projPlus_eq_zero_iff p hp2, mem_minusPart_iff,
    Ideal.mem_span_singleton]
  constructor
  · -- `dirac(−1)·x = −x` ⟹ `x = ([−1]−1)·((−½)·x)`, so `([−1]−1) ∣ x`
    intro hx
    refine ⟨(-(((PadicLFunctions.isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) • x, ?_⟩
    rw [mul_smul_comm, sub_mul, hx, one_mul,
      show (-x - x : PadicMeasure p ℤ_[p]ˣ) = -((2 : ℤ_[p]) • x) from by rw [two_smul]; abel,
      smul_neg, neg_smul, neg_neg, smul_smul,
      (PadicLFunctions.isUnit_two_padicInt p hp2).val_inv_mul, one_smul]
  · -- conversely `([−1]−1)·c` is `c`-anti-invariant (`[−1]·([−1]−1) = 1−[−1] = −([−1]−1)`)
    rintro ⟨c, rfl⟩
    rw [← mul_assoc, mul_sub, units_dirac_mul_dirac, neg_mul_neg, one_mul, mul_one,
      ← units_one_def,
      show (1 : PadicMeasure p ℤ_[p]ˣ) - dirac p (-1 : ℤ_[p]ˣ) = -(dirac p (-1) - 1) from by abel]
    exact neg_mul _ _

end PadicMeasure
