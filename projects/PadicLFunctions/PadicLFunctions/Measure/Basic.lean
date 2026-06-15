import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.MetricSpace.Ultra.ContinuousMaps

/-!
# p-adic measures on a compact space

Following Rodrigues Jacinto–Williams, *An introduction to p-adic L-functions*
(arXiv:2309.15692) §3.2, we define the space of `ℤ_[p]`-valued p-adic measures on a
topological space `X` as the space of `ℤ_[p]`-linear functionals on `C(X, ℤ_[p])`.

The source (Def. 3.6, `def:measures`) defines `L`-valued measures as the *continuous*
dual of `C(G, L)` and singles out the `𝒪_L`-valued ones; over `ℤ_[p]`, continuity of an
`ℤ_[p]`-linear functional is automatic (`PadicMeasure.norm_apply_le`,
`PadicMeasure.continuous`), so no continuity hypothesis is needed in the definition.
This file is the `𝒪 = ℤ_[p]` case; the general coefficient case is deferred to the §5
development pass (see `.mathlib-quality/plan.md`, Generality Decisions).

## Main definitions

* `PadicMeasure p X`: `ℤ_[p]`-valued measures on `X`.
* `PadicMeasure.dirac`: the Dirac measure at a point (source Ex. 3.7, `ex:dirac`).
* `PadicMeasure.pushforward`: pushforward along a continuous map; specialises to the
  `σ_a`, `φ` operators and the embedding `Λ(ℤ_p^×) ↪ Λ(ℤ_p)` later.

## Main results

* `PadicMeasure.norm_apply_le` / `PadicMeasure.continuous`: automatic boundedness and
  continuity (source: footnote to Def. 3.6 — boundedness ⟺ continuity).
* `PadicMeasure.exists_locallyConstant_norm_sub_le`: density of locally constant
  functions (source: Rem. 3.8, `rem:locally constant`, lines 782–802).
* `PadicMeasure.ext_locallyConstant`: a measure is determined by its values on locally
  constant functions (source: Eq. (3.1), `eq:restrict measures`).
-/

open scoped fwdDiff

variable (p : ℕ) [hp : Fact p.Prime]

instance (n : ℕ) : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩

noncomputable section

/-- The space of `ℤ_[p]`-valued *p-adic measures* on a topological space `X`: `ℤ_[p]`-linear
functionals on the continuous functions `C(X, ℤ_[p])`. Over `ℤ_[p]` every linear functional
is automatically bounded (norm ≤ 1) and continuous, so this agrees with the continuous
dual used in the source.

Source: RJW Def. 3.6 (`def:measures`, TeX line 760) together with the `𝒪_L`-valued
convention of line 765. -/
abbrev PadicMeasure (X : Type*) [TopologicalSpace X] :=
  C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]

namespace PadicMeasure

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section basic

/-- The *Dirac measure* at `x : X`: the functional `φ ↦ φ x`.

Source: RJW Ex. 3.7 (`ex:dirac`, TeX lines 774–779). -/
def dirac (x : X) : PadicMeasure p X where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma dirac_apply (x : X) (f : C(X, ℤ_[p])) : dirac p x f = f x := rfl

/-- Precomposition with a continuous map `m : C(X, Y)`, as a linear map
`C(Y, ℤ_[p]) →ₗ[ℤ_[p]] C(X, ℤ_[p])`. Auxiliary for `PadicMeasure.pushforward`. -/
def compRight (m : C(X, Y)) : C(Y, ℤ_[p]) →ₗ[ℤ_[p]] C(X, ℤ_[p]) where
  toFun f := f.comp m
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
lemma compRight_apply (m : C(X, Y)) (f : C(Y, ℤ_[p])) : compRight p m f = f.comp m := rfl

/-- The *pushforward* of a measure along a continuous map `m : C(X, Y)`:
`(pushforward m μ) f = ∫ f ∘ m dμ`. Specialises to `σ_a` and `φ` (RJW §3.5.4) and to
the embedding `Λ(ℤ_p^×) → Λ(ℤ_p)` (RJW Rem. 3.33). -/
def pushforward (m : C(X, Y)) : PadicMeasure p X →ₗ[ℤ_[p]] PadicMeasure p Y where
  toFun μ := μ.comp (compRight p m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma pushforward_apply (m : C(X, Y)) (μ : PadicMeasure p X) (f : C(Y, ℤ_[p])) :
    pushforward p m μ f = μ (f.comp m) := rfl

@[simp]
lemma pushforward_dirac (m : C(X, Y)) (x : X) :
    pushforward p m (dirac p x) = dirac p (m x) := rfl

end basic

section compact

variable [CompactSpace X]

/-- Every `ℤ_[p]`-linear functional on `C(X, ℤ_[p])` is bounded with norm at most `1`:
if `‖f‖ ≤ p^{-m}` then `f = p^m • g` for a continuous `g`, so `‖μ f‖ ≤ p^{-m}`.

Source: RJW Def. 3.6, footnote (boundedness of measures; TeX line 759), combined with
the `𝒪_L`-valuedness convention of line 765. -/
theorem norm_apply_le (μ : PadicMeasure p X) (f : C(X, ℤ_[p])) : ‖μ f‖ ≤ ‖f‖ := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have hf : f = 0 := by ext x; exact (IsEmpty.false x).elim
    simp [hf]
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  -- the sup norm is attained, and is a power of `p`
  obtain ⟨x₀, -, hx₀'⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    ((map_continuous f).norm.continuousOn)
  have hx₀ : ∀ x, ‖f x‖ ≤ ‖f x₀‖ := fun x => hx₀' (Set.mem_univ x)
  have hfx₀ : f x₀ ≠ 0 := by
    intro h
    refine hf (ContinuousMap.ext fun x => norm_le_zero_iff.1 ?_)
    simpa [h] using hx₀ x
  have hnorm : ‖f‖ = ‖f x₀‖ :=
    le_antisymm ((f.norm_le (norm_nonneg _)).2 hx₀) (f.norm_coe_le_norm x₀)
  set n := (f x₀).valuation with hn
  have hval : ‖f x₀‖ = (p : ℝ) ^ (-n : ℤ) := PadicInt.norm_eq_zpow_neg_valuation hfx₀
  -- every value of `f` is divisible by `p ^ n`, so `f = p ^ n • g`
  have hple : ∀ x, ‖f x‖ ≤ (p : ℝ) ^ (-n : ℤ) := fun x => by
    rw [← hval, ← hnorm]; exact f.norm_coe_le_norm x
  have hpn : ((p : ℚ_[p]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hbound : ∀ x : X, ‖(f x : ℚ_[p]) / (p : ℚ_[p]) ^ n‖ ≤ 1 := fun x => by
    rw [norm_div, Padic.norm_p_pow,
      div_le_one (zpow_pos (by exact_mod_cast hp.out.pos) _), ← PadicInt.norm_def]
    exact hple x
  set g : C(X, ℤ_[p]) :=
    ⟨fun x => ⟨(f x : ℚ_[p]) / (p : ℚ_[p]) ^ n, hbound x⟩,
      Continuous.subtype_mk
        ((continuous_subtype_val.comp (map_continuous f)).div_const _) hbound⟩ with hg
  have hfg : f = (p : ℤ_[p]) ^ n • g := by
    ext x
    refine Subtype.ext ?_
    simp only [hg, ContinuousMap.smul_apply, smul_eq_mul, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_natCast, ContinuousMap.coe_mk]
    field_simp
  calc ‖μ f‖ = ‖(p : ℤ_[p]) ^ n * μ g‖ := by rw [hfg, map_smul, smul_eq_mul]
    _ = ‖(p : ℤ_[p]) ^ n‖ * ‖μ g‖ := norm_mul _ _
    _ ≤ (p : ℝ) ^ (-n : ℤ) * 1 := by
        rw [PadicInt.norm_p_pow]
        exact mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _)
          (zpow_nonneg (Nat.cast_nonneg p) _)
    _ = ‖f‖ := by rw [mul_one, hnorm, hval]

/-- Measures are automatically continuous (the source's "measures are continuous (or
equivalently, bounded)", TeX line 765). -/
theorem continuous (μ : PadicMeasure p X) : Continuous μ :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun f g => by
    simpa only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul] using
      norm_apply_le p μ (f - g)).continuous

/-- Residue discs mod `p^k` are open in `ℤ_p`: the reduction `toZModPow k` is locally
constant. Workhorse for density and for the `ψ`-operator's digit shift. -/
lemma isOpen_toZModPow_fiber (k : ℕ) (a : ZMod (p ^ k)) :
    IsOpen {z : ℤ_[p] | PadicInt.toZModPow k z = a} := by
  rw [Metric.isOpen_iff]
  intro z hz
  refine ⟨(p : ℝ) ^ (-k : ℤ), zpow_pos (by exact_mod_cast hp.out.pos) _, fun y hy => ?_⟩
  have hmem : PadicInt.toZModPow k (y - z) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow _ k).1
      (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hy))
  rw [map_sub, sub_eq_zero] at hmem
  simpa only [Set.mem_setOf_eq, hmem] using hz

/-- The canonical-digit lift `x ↦ [x mod p^k] : ℤ_p → ℤ_p` is locally constant
(hence continuous). -/
lemma isLocallyConstant_toZModPow_val (k : ℕ) :
    IsLocallyConstant fun x : ℤ_[p] => (((PadicInt.toZModPow k x).val : ℕ) : ℤ_[p]) :=
  (IsLocallyConstant.comp (fun s => by
      rw [← Set.biUnion_preimage_singleton]
      exact isOpen_biUnion fun a _ => isOpen_toZModPow_fiber p k a)
    fun a : ZMod (p ^ k) => ((a.val : ℕ) : ℤ_[p]))

/-- **Density of locally constant functions**: any continuous `f : X → ℤ_[p]` on a
compact space is uniformly approximated by locally constant functions. The preimages of
the (clopen) balls of radius `ε` form a clopen cover; pass to a finite subcover,
disjointify, and pick values.

Source: RJW Rem. 3.8 (`rem:locally constant`, TeX lines 782–791): "any continuous
function `φ ∈ 𝒞(G, 𝒪_L)` can be p-adically approximated by its locally constant
truncations". Not in mathlib (verified absent); PR candidate. -/
theorem exists_locallyConstant_norm_sub_le (f : C(X, ℤ_[p])) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : LocallyConstant X ℤ_[p], ‖f - (g : C(X, ℤ_[p]))‖ ≤ ε := by
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  have hopen := isOpen_toZModPow_fiber p k
  -- the mod-`p^k` reduction of `f` is locally constant
  set q : X → ZMod (p ^ k) := fun x => PadicInt.toZModPow k (f x) with hq
  have hlc : IsLocallyConstant q := fun s => by
    rw [← Set.biUnion_preimage_singleton]
    exact isOpen_biUnion fun a _ => (hopen a).preimage (map_continuous f)
  -- lift back via the canonical representatives
  refine ⟨⟨fun x => ((q x).val : ℤ_[p]), hlc.comp fun a => ((a.val : ℕ) : ℤ_[p])⟩,
    ((f - _).norm_le hε.le).2 fun x => ?_⟩
  have hgx : PadicInt.toZModPow k (((q x).val : ℤ_[p])) = q x := by
    rw [map_natCast]
    exact ZMod.natCast_rightInverse (q x)
  have hle : ‖f x - ((q x).val : ℤ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
      map_sub, hgx, sub_self]
  calc ‖(f - _) x‖ = ‖f x - ((q x).val : ℤ_[p])‖ := by
        simp [ContinuousMap.sub_apply]
    _ ≤ (p : ℝ) ^ (-k : ℤ) := hle
    _ ≤ ε := hk.le

/-- On `ℤ_p`, a locally constant function (into any type) factors through a
finite quotient `toZModPow n`: local constancy is uniform on the compact
`ℤ_p`. Not in mathlib (PR candidate). -/
theorem _root_.LocallyConstant.exists_eq_comp_toZModPow {α : Type*}
    (Φ : LocallyConstant ℤ_[p] α) :
    ∃ (n : ℕ) (g : ZMod (p ^ n) → α), ⇑Φ = g ∘ (PadicInt.toZModPow n) := by
  classical
  have hker : ∀ (m : ℕ) (z w : ℤ_[p]),
      PadicInt.toZModPow m z = PadicInt.toZModPow m w
        ↔ ‖z - w‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    intro m z w
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, sub_eq_zero]
  -- each point has a `toZModPow`-fibre on which `Φ` is constant
  have hpt : ∀ x : ℤ_[p], ∃ n : ℕ, ∀ y : ℤ_[p],
      PadicInt.toZModPow n y = PadicInt.toZModPow n x → Φ y = Φ x := by
    intro x
    have hopen : IsOpen {y : ℤ_[p] | Φ y = Φ x} :=
      Φ.isLocallyConstant.isOpen_fiber (Φ x)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x rfl
    obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
    refine ⟨n, fun y hy => ?_⟩
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt ((hker n y x).mp hy) hn
  choose nx hnx using hpt
  -- finitely many such fibres cover `ℤ_p`
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover isCompact_univ
    (fun x => {y : ℤ_[p] | PadicInt.toZModPow (nx x) y
      = PadicInt.toZModPow (nx x) x})
    (fun x _ => ((isOpen_toZModPow_fiber p (nx x)
      (PadicInt.toZModPow (nx x) x)).mem_nhds rfl))
  set n : ℕ := t.sup nx with hn
  -- `Φ` is constant on every `toZModPow n`-fibre
  have hconst : ∀ x y : ℤ_[p],
      PadicInt.toZModPow n y = PadicInt.toZModPow n x → Φ y = Φ x := by
    intro x y hy
    obtain ⟨xi, hxi, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    have hxU' : PadicInt.toZModPow (nx xi) x
        = PadicInt.toZModPow (nx xi) xi := hxU
    have hxin : ‖x - xi‖ ≤ (p : ℝ) ^ (-(nx xi : ℤ)) := (hker _ x xi).mp hxU'
    have hyx : ‖y - x‖ ≤ (p : ℝ) ^ (-(nx xi : ℤ)) := by
      refine ((hker n y x).mp hy).trans ?_
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_lt.le
      have hle : nx xi ≤ n := Finset.le_sup hxi
      exact zpow_le_zpow_right₀ hp1 (neg_le_neg (by exact_mod_cast hle))
    have hyxi : PadicInt.toZModPow (nx xi) y = PadicInt.toZModPow (nx xi) xi := by
      refine (hker _ y xi).mpr ?_
      calc ‖y - xi‖ = ‖(y - x) + (x - xi)‖ := by ring_nf
        _ ≤ max ‖y - x‖ ‖x - xi‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ (p : ℝ) ^ (-(nx xi : ℤ)) := max_le hyx hxin
    rw [hnx xi y hyxi, hnx xi x hxU']
  refine ⟨n, fun a => Φ ((a.val : ℤ_[p])), funext fun x => ?_⟩
  refine (hconst x ((((PadicInt.toZModPow n x).val : ℕ)) : ℤ_[p]) ?_).symm
  rw [map_natCast]
  exact ZMod.natCast_rightInverse _

/-- A measure is determined by its values on locally constant functions.

Source: RJW Eq. (3.1) (`eq:restrict measures`, TeX lines 787–799): restriction defines
an isomorphism `ℳ(G, 𝒪_L) ≅ ℳ^lc(G, 𝒪_L)`; injectivity is this statement. -/
theorem ext_locallyConstant {μ ν : PadicMeasure p X}
    (h : ∀ g : LocallyConstant X ℤ_[p], μ (g : C(X, ℤ_[p])) = ν (g : C(X, ℤ_[p]))) :
    μ = ν := by
  refine LinearMap.ext fun f => eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨g, hg⟩ := exists_locallyConstant_norm_sub_le p f hε
  have key : μ f - ν f = μ (f - (g : C(X, ℤ_[p]))) - ν (f - (g : C(X, ℤ_[p]))) := by
    simp only [map_sub, h g]
    ring
  rw [dist_eq_norm, key, sub_eq_add_neg]
  calc ‖μ (f - (g : C(X, ℤ_[p]))) + -(ν (f - (g : C(X, ℤ_[p]))))‖
      ≤ max ‖μ (f - (g : C(X, ℤ_[p])))‖ ‖-(ν (f - (g : C(X, ℤ_[p]))))‖ :=
        IsUltrametricDist.norm_add_le_max _ _
    _ ≤ ‖f - (g : C(X, ℤ_[p]))‖ := by
        rw [norm_neg]
        exact max_le (norm_apply_le p μ _) (norm_apply_le p ν _)
    _ ≤ ε := hg

end compact

end PadicMeasure
