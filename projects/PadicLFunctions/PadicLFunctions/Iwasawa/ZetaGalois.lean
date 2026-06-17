import PadicLFunctions.Iwasawa.PlusPart
import PadicLFunctions.KubotaLeopoldt.ZetaP

/-!
# ζ_p as a pseudo-measure on 𝒢⁺ and the ideal I(𝒢)ζ_p

RJW (arXiv:2309.15692) §11.1 corollary + §11.2 (TeX 2992, 3033–3059), on the
identified Galois side (replan R11.1; `𝒢⁺ = GPlus p`).

## Main declarations

* `PadicMeasure.odd_moment_factor_eq_zero` + `padicZeta_odd_moment_eq_zero`: the
  interpolated odd moments of ζ_p vanish — at `k = 1` via the Euler factor `1 − p⁰ = 0`,
  at odd `k ≥ 3` via `B_k = 0` (TeX 2992; **erratum #13**: the source's proof line
  "ζ(1−k) = 0 for odd k ≥ 1" fails at `k = 1`).
* `PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta`: c-invariance
  `([−1]−[1])·ζ_p = 0` — the descent input.
* `PadicMeasure.padicZetaPlus` + `isPlusPseudoMeasure_padicZetaPlus`: **the corollary
  of RJW TeX 3033** — ζ_p descends to a pseudo-measure on 𝒢⁺.
* `PadicMeasure.zetaIdeal`/`zetaIdealPlus`: the ideals `I(𝒢)ζ_p` and `I(𝒢⁺)ζ_p`
  (**RJW Proposition, TeX 3052–3057**), with their `Ideal.span` descriptions via the
  principality of the augmentation ideals.
-/

noncomputable section

namespace PadicMeasure

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## Odd moments of ζ_p vanish (TeX 2992 + the corrected TeX 3038 argument) -/

/-- The interpolation factor `(1 − p^{k−1})·ζ(1−k)` vanishes for every odd `k ≥ 1`:
at `k = 1` the Euler factor is `1 − p⁰ = 0` (ζ(0) = −1/2 itself does NOT vanish —
erratum #13); at odd `k ≥ 3`, `ζ(1−k) = −B_k/k = 0` (`bernoulli_eq_zero_of_odd`). -/
theorem odd_moment_factor_eq_zero {k : ℕ} (hk : Odd k) :
    (1 - (p : ℚ_[p]) ^ (k - 1)) * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) = 0 := by
  obtain rfl | hk1 := eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hk.pos.ne')
  · -- `k = 1`: the Euler factor `1 − p⁰ = 0`
    simp
  · -- odd `k ≥ 3`: `ζ(1−k) = −B_k/k = 0` since `B_k = 0`
    have hzero : zetaNeg (k - 1) = 0 := by
      rw [zetaNeg, Nat.sub_add_cancel hk.pos, bernoulli_eq_zero_of_odd hk hk1, mul_zero,
        zero_div]
    rw [hzero, Rat.cast_zero, mul_zero]

/-- The odd moments of every witness `([b]−[1])·ζ_p` vanish: this is the precise
content of TeX 2992 "ζ_p vanishes at the characters χ^k for odd k" — including
`k = 1`, which the membership criterion requires. -/
theorem padicZeta_odd_moment_eq_zero (hp2 : p ≠ 2) (b : ℤ_[p]ˣ) {k : ℕ} (hk : Odd k)
    (ν : PadicMeasure p ℤ_[p]ˣ)
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p b - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν) :
    ν (unitsPowCM p k) = 0 := by
  -- The moment is `(b^k − 1) · [(1 − p^{k−1}) · ζ(1−k)]`, and the bracket vanishes.
  have hm := padicZeta_moments p hp2 b hk.pos ν hν
  rw [mul_assoc, odd_moment_factor_eq_zero p hk, mul_zero] at hm
  -- Descend the ℚ_p-equation back to ℤ_p (the coercion is injective).
  refine Subtype.coe_injective ?_
  change ((ν (unitsPowCM p k) : ℤ_[p]) : ℚ_[p]) = ((0 : ℤ_[p]) : ℚ_[p])
  rw [hm]
  norm_num

/-! ## c-invariance of ζ_p -/

/-- **The descent input**: `([−1]−[1])·ζ_p = 0` in `Q(𝒢)`, i.e. ζ_p is invariant
under complex conjugation. (The `b = −1` witness has *all* moments zero: even ones by
`(−1)^k − 1 = 0`, odd ones by `padicZeta_odd_moment_eq_zero`.) -/
theorem dirac_neg_one_sub_one_mul_padicZeta (hp2 : p ≠ 2) :
    algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p (-1 : ℤ_[p]ˣ) - 1)
        * padicZeta p hp2
      = 0 := by
  -- The `b = −1` witness has *all* moments zero, hence is the zero measure.
  obtain ⟨ν, hν⟩ := padicZeta_isPseudoMeasure p hp2 (-1)
  have hzero : ν = 0 := by
    refine eq_zero_of_forall_unitsPowCM_eq_zero p ν fun k hk => ?_
    have hm := padicZeta_moments p hp2 (-1) hk ν hν
    have hb : ((-1 : ℤ_[p]ˣ) : ℚ_[p]) = -1 := by push_cast; ring
    rw [hb] at hm
    refine Subtype.coe_injective ?_
    change ((ν (unitsPowCM p k) : ℤ_[p]) : ℚ_[p]) = ((0 : ℤ_[p]) : ℚ_[p])
    rcases Nat.even_or_odd k with he | ho
    · -- even moments: `(−1)^k − 1 = 0`
      rw [he.neg_one_pow, sub_self, zero_mul, zero_mul] at hm
      rw [hm]; norm_num
    · -- odd moments: the interpolation factor vanishes
      rw [mul_assoc, odd_moment_factor_eq_zero p ho, mul_zero] at hm
      rw [hm]; norm_num
  rwa [hzero, map_zero] at hν

/-- Witness symmetry: the witnesses of `([g]−[1])·ζ_p` and `([−g]−[1])·ζ_p`
coincide — the well-definedness of pushing witnesses to `𝒢⁺`. -/
theorem padicZeta_witness_neg (hp2 : p ≠ 2) (g : ℤ_[p]ˣ)
    {ν ν' : PadicMeasure p ℤ_[p]ˣ}
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p g - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν)
    (hν' : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p (-g) - 1)
        * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν') :
    ν = ν' := by
  -- `([−g]−[g])·ζ_p = [g]·(([−1]−[1])·ζ_p) = 0`, so the two witnesses agree.
  have hfac : (dirac p (-g) - dirac p g : PadicMeasure p ℤ_[p]ˣ)
      = dirac p g * (dirac p (-1 : ℤ_[p]ˣ) - 1) := by
    rw [mul_sub, units_dirac_mul_dirac, mul_one, mul_neg_one]
  have hkey : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν'
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν := by
    have hsub : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν'
        - algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν = 0 := by
      rw [← hν', ← hν, ← sub_mul]
      have : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p (-g) - 1)
          - algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p g - 1)
          = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)
              (dirac p g) * algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)
                (dirac p (-1 : ℤ_[p]ˣ) - 1) := by
        rw [← map_mul, ← hfac, ← map_sub]
        ring_nf
      rw [this, mul_assoc, dirac_neg_one_sub_one_mul_padicZeta p hp2, mul_zero]
    rwa [sub_eq_zero] at hsub
  exact (IsFractionRing.injective (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) hkey).symm

/-! ## ζ_p as a pseudo-measure on 𝒢⁺ (RJW corollary, TeX 3033–3039) -/

/-- The total fraction ring `Q(𝒢⁺)` of the Iwasawa algebra `Λ(𝒢⁺)`. -/
abbrev QuotientFieldPlus := FractionRing (PadicMeasure p (GPlus p))

/-- The structure map `Λ(𝒢⁺) → Q(𝒢⁺)`, named once (the raw `algebraMap` keeps an
unresolved instance metavariable inside `def`-bodies over the quotient group — a
known elaboration-order trap; naming it sidesteps the postponement). -/
def toQPlus : PadicMeasure p (GPlus p) →+* QuotientFieldPlus p :=
  algebraMap _ _

/-- A *pseudo-measure on `𝒢⁺`* (RJW Def. 3.34 applied to `G = 𝒢⁺`). -/
def IsPlusPseudoMeasure (q : QuotientFieldPlus p) : Prop :=
  ∀ g : GPlus p, ∃ ν : PadicMeasure p (GPlus p),
    toQPlus p (dirac p g - 1) * q = toQPlus p ν

/-- Regularity transports along the projection: if `[a]−[1]` is a non-zero-divisor in
`Λ(𝒢)`, then `[ā]−[1]` is one in `Λ(𝒢⁺)` (lift along the even-part section, land in
`Λ⁺ ⊓ ker π_* = 0`, conclude on the 𝒢-side). No 𝒢⁺-moment theory needed. -/
theorem dirac_mk_sub_one_mem_nonZeroDivisors (hp2 : p ≠ 2) {a : ℤ_[p]ˣ}
    (ha : (dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ)
      ∈ nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)) :
    (dirac p (QuotientGroup.mk a : GPlus p) - 1 : PadicMeasure p (GPlus p))
      ∈ nonZeroDivisors (PadicMeasure p (GPlus p)) := by
  -- A non-zero-divisor in a `CommRing` is detected by one-sided cancellation.
  rw [mem_nonZeroDivisors_iff]
  -- The key elimination: `ν * ([ā]−[1]) = 0 → ν = 0`, lifting `ν` along the section.
  have key : ∀ ν : PadicMeasure p (GPlus p),
      ν * (dirac p (QuotientGroup.mk a : GPlus p) - 1) = 0 → ν = 0 := by
    intro ν hν
    set μ := plusSection p hp2 ν with hμ
    -- `π_*(μ · ([a]−[1])) = ν · ([ā]−[1]) = 0`.
    have hproj : projPlus p (μ * (dirac p a - 1))
        = ν * (dirac p (QuotientGroup.mk a : GPlus p) - 1) := by
      rw [map_mul, map_sub, map_one, projPlus_dirac, hμ, projPlus_plusSection p hp2]
    rw [hν] at hproj
    -- so `μ · ([a]−[1]) ∈ ker π_* = minusPart`.
    have hmem_minus : μ * (dirac p a - 1) ∈ minusPart p :=
      (projPlus_eq_zero_iff p hp2).1 hproj
    -- and `μ · ([a]−[1]) ∈ plusPart` (μ is even and plusPart is a multiplicative ideal).
    have hmem_plus : μ * (dirac p a - 1) ∈ plusPart p := by
      rw [mul_comm]
      exact mul_mem_plusPart p (plusSection_mem_plusPart p hp2 ν)
    -- the two parts intersect trivially ⟹ `μ · ([a]−[1]) = 0`.
    have hzero : μ * (dirac p a - 1) = 0 :=
      (Submodule.disjoint_def.1 (isCompl_plusPart_minusPart p hp2).disjoint)
        _ hmem_plus hmem_minus
    -- `[a]−[1]` is a non-zero-divisor ⟹ `μ = 0` ⟹ `ν = π_* μ = 0`.
    have hμ0 : μ = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff ha).1 hzero
    rw [← projPlus_plusSection p hp2 ν, ← hμ, hμ0, map_zero]
  -- in a `CommRing` both cancellation directions follow from `key` via `mul_comm`.
  exact ⟨fun x hx => key x (by rw [mul_comm x]; exact hx), key⟩

/-- **ζ_p as a pseudo-measure on 𝒢⁺** (the object of RJW's corollary, TeX 3033):
`ζ_p⁺ := π_*(x⁻¹ Res μ_a) / ([ā]−[1])`, for the same packed integer topological
generator `a` as `padicZeta`. -/
def padicZetaPlus (hp2 : p ≠ 2) : QuotientFieldPlus p :=
  IsLocalization.mk' (QuotientFieldPlus p)
    (projPlus p (zetaNum p (exists_nat_topological_generator p hp2).choose))
    (⟨dirac p (QuotientGroup.mk
        ((exists_nat_topological_generator p hp2).choose_spec.choose) : GPlus p) - 1,
      dirac_mk_sub_one_mem_nonZeroDivisors p hp2
        (dirac_sub_one_mem_nonZeroDivisors p
          (topGen_pow_ne_one p
            (exists_nat_topological_generator p hp2).choose_spec.choose_spec.2.2))⟩ :
      nonZeroDivisors (PadicMeasure p (GPlus p)))

/-- Compatibility of the descents: pushing a 𝒢-side witness forward gives the
𝒢⁺-side witness at the image group element — "ζ_p descends". -/
theorem projPlus_padicZeta_witness (hp2 : p ≠ 2) (g : ℤ_[p]ˣ)
    {ν : PadicMeasure p ℤ_[p]ˣ}
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p g - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν) :
    toQPlus p (dirac p (QuotientGroup.mk g : GPlus p) - 1) * padicZetaPlus p hp2
      = toQPlus p (projPlus p ν) := by
  classical
  -- destructure the packed integer topological generator (same pack as `padicZeta`).
  set m := (exists_nat_topological_generator p hp2).choose with hm
  set u := (exists_nat_topological_generator p hp2).choose_spec.choose with hu
  -- the defining relation `([u]−1)·ζ_p = zetaNum m` (mirror `padicZeta_moments`).
  have hspec : algebraMap _ (QuotientField p) (dirac p u - 1) * padicZeta p hp2
      = algebraMap _ _ (zetaNum p m) := by
    rw [padicZeta]
    exact IsLocalization.mk'_spec' (QuotientField p) _ _
  -- pull the two witness identities back to `Λ(ℤ_p^×)`: `([u]−1)·ν = ([g]−1)·zetaNum m`.
  have hkey : (dirac p u - 1) * ν = (dirac p g - 1) * zetaNum p m := by
    apply IsFractionRing.injective (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)
    rw [map_mul, map_mul, ← hν, ← hspec]
    ring
  -- push forward by `π_*` (a ring hom): `([ḡ]−1)·π_*(zetaNum m) = ([ū]−1)·π_*ν`.
  have hkeyP : (dirac p (QuotientGroup.mk g : GPlus p) - 1)
        * projPlus p (zetaNum p m)
      = (dirac p (QuotientGroup.mk u : GPlus p) - 1) * projPlus p ν := by
    have := congrArg (projPlus p) hkey
    simp only [map_mul, map_sub, map_one, projPlus_dirac] at this
    exact this.symm
  -- conclude in `Q(𝒢⁺)` via the `mk'` algebra and unit-cancellation of the denominator.
  -- abbreviate the denominator `c = [ū]−1` and its non-zero-divisor witness.
  set c : nonZeroDivisors (PadicMeasure p (GPlus p)) :=
    ⟨dirac p (QuotientGroup.mk u : GPlus p) - 1,
      dirac_mk_sub_one_mem_nonZeroDivisors p hp2
        (dirac_sub_one_mem_nonZeroDivisors p
          (topGen_pow_ne_one p
            (exists_nat_topological_generator p hp2).choose_spec.choose_spec.2.2))⟩ with hc
  -- `padicZetaPlus` is exactly the `mk'` with this numerator/denominator.
  have hzp : padicZetaPlus p hp2
      = IsLocalization.mk' (QuotientFieldPlus p) (projPlus p (zetaNum p m)) c := rfl
  -- the image of `c` is a unit in the localization.
  have hcunit : IsUnit (algebraMap (PadicMeasure p (GPlus p)) (QuotientFieldPlus p) (c : _)) :=
    IsLocalization.map_units (QuotientFieldPlus p) c
  -- cancel that unit: it suffices to prove the equation multiplied by `algebraMap c`.
  rw [hzp, toQPlus, ← hcunit.mul_left_inj, mul_assoc, IsLocalization.mk'_spec,
    ← map_mul, ← map_mul]
  -- now it is `algebraMap` applied to the pushed-forward 𝒢-side identity (`hkeyP`).
  congr 1
  linear_combination hkeyP

/-- **RJW §11.1, Corollary (TeX 3033–3039)**: the p-adic zeta function is a
pseudo-measure on `𝒢⁺`. -/
theorem isPlusPseudoMeasure_padicZetaPlus (hp2 : p ≠ 2) :
    IsPlusPseudoMeasure p (padicZetaPlus p hp2) := by
  -- every group element of `𝒢⁺` lifts to a unit; transport its 𝒢-side witness forward.
  intro gPlus
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gPlus
  obtain ⟨ν, hν⟩ := padicZeta_isPseudoMeasure p hp2 g
  exact ⟨projPlus p ν, projPlus_padicZeta_witness p hp2 g hν⟩

/-! ## The ideal generated by ζ_p (RJW §11.2, TeX 3043–3059) -/

/-- **`I(𝒢)ζ_p`** (RJW Proposition, TeX 3052): the set of measures of the form
`λ·ζ_p` with `λ` in the augmentation ideal — an ideal of `Λ(𝒢)` by the
pseudo-measure property (the ideal axioms hold directly; the `Ideal.span`
description below is the computational form). -/
def zetaIdeal (hp2 : p ≠ 2) : Ideal (PadicMeasure p ℤ_[p]ˣ) where
  carrier := {x | ∃ l ∈ augmentationIdeal p (G := ℤ_[p]ˣ),
    algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) x
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) l * padicZeta p hp2}
  add_mem' := by
    rintro x y ⟨l₁, hl₁, he₁⟩ ⟨l₂, hl₂, he₂⟩
    exact ⟨l₁ + l₂, Ideal.add_mem _ hl₁ hl₂, by rw [map_add, he₁, he₂, map_add, add_mul]⟩
  zero_mem' := ⟨0, Ideal.zero_mem _, by rw [map_zero, zero_mul]⟩
  smul_mem' := by
    rintro c x ⟨l, hl, he⟩
    refine ⟨c • l, Submodule.smul_mem _ _ hl, ?_⟩
    rw [smul_eq_mul, smul_eq_mul, map_mul, he, map_mul, mul_assoc]

lemma mem_zetaIdeal_iff (hp2 : p ≠ 2) {x : PadicMeasure p ℤ_[p]ˣ} :
    x ∈ zetaIdeal p hp2 ↔ ∃ l ∈ augmentationIdeal p (G := ℤ_[p]ˣ),
      algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) x
        = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) l * padicZeta p hp2 :=
  Iff.rfl

/-- The computational description: `I(𝒢)ζ_p` is the principal ideal generated by any
witness of `([b]−[1])·ζ_p` at a topological generator `b` (via the principality
`augmentationIdeal_eq_span`). -/
theorem zetaIdeal_eq_span (hp2 : p ≠ 2) {b : ℤ_[p]ˣ}
    (hb : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n b) = ⊤)
    {ν : PadicMeasure p ℤ_[p]ˣ}
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p b - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν) :
    zetaIdeal p hp2 = Ideal.span {ν} := by
  -- `[b]−[1]` lies in the augmentation ideal.
  have hbmem : (dirac p b - 1 : PadicMeasure p ℤ_[p]ˣ) ∈ augmentationIdeal p := by
    rw [augmentationIdeal, RingHom.mem_ker, map_sub, map_one,
      show deg p (dirac p b) = 1 from rfl, sub_self]
  apply le_antisymm
  · -- `I(𝒢)ζ_p ⊆ (ν)`: every `x = l·ζ_p` with `l = ([b]−1)·ρ` factors through `ν`.
    rintro x ⟨l, hl, he⟩
    rw [augmentationIdeal_eq_span p hb, Ideal.mem_span_singleton] at hl
    obtain ⟨ρ, rfl⟩ := hl
    rw [Ideal.mem_span_singleton]
    -- `x = ρ·ν` after cancelling into the localization.
    refine ⟨ρ, IsFractionRing.injective (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ?_⟩
    rw [he, map_mul, map_mul, ← hν]
    ring
  · -- `(ν) ⊆ I(𝒢)ζ_p`: `ν` itself is the witness `([b]−1)·ζ_p`.
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ⟨dirac p b - 1, hbmem, hν.symm⟩

/-- The image `ā` of a topological generator generates the augmentation ideal of
`Λ(𝒢⁺)`: `I(𝒢⁺) = ([ā]−[1])·Λ(𝒢⁺)` (transport of `augmentationIdeal_eq_span`
along the surjection `π_*`, using `deg⁺ ∘ π_* = deg`). -/
theorem augmentationIdealPlus_eq_span (hp2 : p ≠ 2) {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤) :
    augmentationIdeal p (G := GPlus p)
      = Ideal.span {(dirac p (QuotientGroup.mk a : GPlus p) - 1 :
          PadicMeasure p (GPlus p))} := by
  apply le_antisymm
  · -- `I(𝒢⁺) ⊆ ([ā]−1)`: lift `y = π_* x`, transfer principality from `Λ(𝒢)`.
    intro y hy
    obtain ⟨x, rfl⟩ := projPlus_surjective p hp2 y
    -- `deg x = deg(π_* x) = 0`, so `x ∈ I(𝒢)`.
    have hxmem : x ∈ augmentationIdeal p (G := ℤ_[p]ˣ) := by
      rw [augmentationIdeal, RingHom.mem_ker, ← deg_projPlus p x]
      exact RingHom.mem_ker.1 hy
    rw [augmentationIdeal_eq_span p ha, Ideal.mem_span_singleton] at hxmem
    obtain ⟨ρ, rfl⟩ := hxmem
    -- `π_*((dirac a−1)·ρ) = ([ā]−1)·π_* ρ ∈ ([ā]−1)`.
    rw [Ideal.mem_span_singleton]
    exact ⟨projPlus p ρ, by rw [map_mul, map_sub, map_one, projPlus_dirac]⟩
  · -- `([ā]−1) ⊆ I(𝒢⁺)`: the generator has degree `1 − 1 = 0`.
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change (dirac p (QuotientGroup.mk a : GPlus p) - 1 : PadicMeasure p (GPlus p))
      ∈ augmentationIdeal p
    rw [augmentationIdeal, RingHom.mem_ker, map_sub, map_one,
      show deg p (dirac p (QuotientGroup.mk a : GPlus p)) = 1 from rfl, sub_self]

/-- **`I(𝒢⁺)ζ_p`** (RJW Proposition, TeX 3052, plus half): the corresponding ideal
of `Λ(𝒢⁺)` — the right-hand side of Iwasawa's theorem (`thm:iwasawa`, stated on the
§12 board). -/
def zetaIdealPlus (hp2 : p ≠ 2) : Ideal (PadicMeasure p (GPlus p)) where
  carrier := {x | ∃ l ∈ augmentationIdeal p (G := GPlus p),
    toQPlus p x = toQPlus p l * padicZetaPlus p hp2}
  add_mem' := by
    rintro x y ⟨l₁, hl₁, he₁⟩ ⟨l₂, hl₂, he₂⟩
    exact ⟨l₁ + l₂, Ideal.add_mem _ hl₁ hl₂, by rw [map_add, he₁, he₂, map_add, add_mul]⟩
  zero_mem' := ⟨0, Ideal.zero_mem _, by rw [map_zero, zero_mul]⟩
  smul_mem' := by
    rintro c x ⟨l, hl, he⟩
    refine ⟨c • l, Submodule.smul_mem _ _ hl, ?_⟩
    rw [smul_eq_mul, smul_eq_mul, map_mul, he, map_mul, mul_assoc]

lemma mem_zetaIdealPlus_iff (hp2 : p ≠ 2) {x : PadicMeasure p (GPlus p)} :
    x ∈ zetaIdealPlus p hp2 ↔ ∃ l ∈ augmentationIdeal p (G := GPlus p),
      toQPlus p x = toQPlus p l * padicZetaPlus p hp2 :=
  Iff.rfl

theorem zetaIdealPlus_eq_span (hp2 : p ≠ 2) {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤)
    {ν : PadicMeasure p ℤ_[p]ˣ}
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p a - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν) :
    zetaIdealPlus p hp2 = Ideal.span {projPlus p ν} := by
  -- the 𝒢⁺-side witness identity at `ā` (push `hν` forward).
  have hwit : toQPlus p (dirac p (QuotientGroup.mk a : GPlus p) - 1) * padicZetaPlus p hp2
      = toQPlus p (projPlus p ν) := projPlus_padicZeta_witness p hp2 a hν
  -- `[ā]−1` lies in the augmentation ideal of `Λ(𝒢⁺)`.
  have hamem : (dirac p (QuotientGroup.mk a : GPlus p) - 1 : PadicMeasure p (GPlus p))
      ∈ augmentationIdeal p (G := GPlus p) := by
    rw [augmentationIdeal, RingHom.mem_ker, map_sub, map_one,
      show deg p (dirac p (QuotientGroup.mk a : GPlus p)) = 1 from rfl, sub_self]
  apply le_antisymm
  · -- `I(𝒢⁺)ζ_p ⊆ (π_* ν)`: every `x = l·ζ_p⁺` with `l = ([ā]−1)·ρ` factors through `π_* ν`.
    rintro x ⟨l, hl, he⟩
    rw [augmentationIdealPlus_eq_span p hp2 ha, Ideal.mem_span_singleton] at hl
    obtain ⟨ρ, rfl⟩ := hl
    rw [Ideal.mem_span_singleton]
    refine ⟨ρ, IsFractionRing.injective (PadicMeasure p (GPlus p)) (QuotientFieldPlus p) ?_⟩
    -- `toQPlus = algebraMap`, so the localization injectivity applies to `he`/`hwit`.
    change toQPlus p x = toQPlus p (projPlus p ν * ρ)
    rw [he, map_mul, map_mul, mul_right_comm, hwit]
  · -- `(π_* ν) ⊆ I(𝒢⁺)ζ_p`: `π_* ν` is the witness `([ā]−1)·ζ_p⁺`.
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ⟨dirac p (QuotientGroup.mk a : GPlus p) - 1, hamem, hwit.symm⟩

end PadicMeasure
