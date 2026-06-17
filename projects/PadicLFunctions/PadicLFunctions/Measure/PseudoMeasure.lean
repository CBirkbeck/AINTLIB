import PadicLFunctions.Measure.UnitsZp
import PadicLFunctions.Measure.Fubini
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# The convolution algebra Λ(ℤ_p^×) and pseudo-measures

RJW (arXiv:2309.15692) §3.6 (`sec:pseudo-measures`). The group `ℤ_p^×` is multiplicative,
so the convolution product on `ℳ(ℤ_p^×, ℤ_p)` uses the *multiplicative* structure
(RJW Rem. 3.33, Eq. (3.11) `eq:convolution`):

  `∫ f d(μ ⋆ λ) = ∫ (∫ f(xy) dμ(x)) dλ(y)`.

Pseudo-measures (RJW Def. 3.34) live in the total fraction ring `Q(ℤ_p^×)` of
`Λ(ℤ_p^×)`. The key results are the zero-divisor lemma (RJW Lem. 3.36,
`lem:zero divisor`) and the description of the augmentation ideal as the principal
ideal `([a]−[1])` for a topological generator `a` (RJW Def. 3.37 + Lem. 3.38,
`lem:pseudo-measure existence`), whose source proof goes through the finite levels
`𝒪_L[(ℤ/p^n)^×]` and passes to the inverse limit; the finite levels are implemented
by `PadicMeasure.levelMap` below.

Throughout this file `p` is odd where stated (the source's standing assumption from §4
onwards; `(ℤ/p^n)^×` cyclic requires it).
-/

open scoped fwdDiff
open PowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

section convolution

/-! The convolution algebra is defined for an arbitrary compact commutative topological
monoid `G` — the generality of RJW Rem. 3.33 ("for any profinite abelian `G`"). This
section was generalised in place from its original hardcoded `G = ℤ_[p]ˣ` by the §11
pass (decomposition replan R11.5); the `ℤ_p^×`-named specialisations below preserve
every downstream-facing statement verbatim. -/

variable (G : Type*) [TopologicalSpace G] [CommMonoid G] [ContinuousMul G] [CompactSpace G]

/-- Multiplication on a topological monoid `G` as a single continuous map. -/
def mulCM₂ : C(G × G, G) := ⟨fun q => q.1 * q.2, continuous_mul⟩

variable {G}

/-- Convolution of measures on the (multiplicative) compact commutative monoid `G`:
`∫ f d(μ ⋆ ν) = ∫ (∫ f(xy) dν(y)) dμ(x)`.

Source: RJW Eq. (3.11) (`eq:convolution`, TeX lines 1173–1175) + Rem. 3.33. -/
noncomputable def conv (μ ν : PadicMeasure p G) : PadicMeasure p G where
  toFun f := μ (innerInt p ν (f.comp (mulCM₂ G)))
  map_add' f g := by rw [ContinuousMap.add_comp, innerInt_add, map_add]
  map_smul' c f := by rw [ContinuousMap.smul_comp, innerInt_smul, map_smul, RingHom.id_apply]

noncomputable instance : Mul (PadicMeasure p G) := ⟨conv p⟩

noncomputable instance : One (PadicMeasure p G) := ⟨dirac p 1⟩

lemma conv_mul_def (μ ν : PadicMeasure p G) : μ * ν = conv p μ ν := rfl

@[simp]
lemma conv_mul_apply (μ ν : PadicMeasure p G) (f : C(G, ℤ_[p])) :
    (μ * ν) f = μ (innerInt p ν (f.comp (mulCM₂ G))) := rfl

omit [ContinuousMul G] [CompactSpace G] in
lemma conv_one_def : (1 : PadicMeasure p G) = dirac p 1 := rfl

/-- The Iwasawa algebra `Λ(G) = ℳ(G, ℤ_p)` of a compact commutative topological monoid
as a commutative ring under convolution. Commutativity is the Fubini swap
(`integral_swap`); associativity is the triple-integral computation.

Source: RJW Rem. 3.11 ("One checks that this does give an algebra structure") +
Rem. 3.33. -/
noncomputable instance : CommRing (PadicMeasure p G) where
  mul_assoc a b c := by
    refine LinearMap.ext fun f => ?_
    change a (innerInt p b ((innerInt p c (f.comp (mulCM₂ G))).comp (mulCM₂ G)))
      = a (innerInt p (conv p b c) (f.comp (mulCM₂ G)))
    congr 1
    ext x
    change b _ = b _
    congr 1
    ext y
    change c _ = c _
    congr 1
    ext z
    change f (x * y * z) = f (x * (y * z))
    rw [mul_assoc]
  one_mul a := by
    refine LinearMap.ext fun f => ?_
    change a ((f.comp (mulCM₂ G)).curry 1) = a f
    congr 1
    ext y
    change f (1 * y) = f y
    rw [one_mul]
  mul_one a := by
    refine LinearMap.ext fun f => ?_
    change a (innerInt p (dirac p 1) (f.comp (mulCM₂ G))) = a f
    congr 1
    ext x
    change f (x * 1) = f x
    rw [mul_one]
  left_distrib a b c := by
    refine LinearMap.ext fun f => ?_
    change a (innerInt p (b + c) (f.comp (mulCM₂ G))) = _
    rw [innerInt_measure_add, map_add]
    rfl
  right_distrib a b c := by
    refine LinearMap.ext fun f => ?_
    change (a + b) (innerInt p c (f.comp (mulCM₂ G))) = _
    rw [LinearMap.add_apply]
    rfl
  zero_mul a := LinearMap.ext fun f => rfl
  mul_zero a := by
    refine LinearMap.ext fun f => ?_
    change a (innerInt p (0 : PadicMeasure p G) (f.comp (mulCM₂ G))) = 0
    rw [innerInt_measure_zero, map_zero]
  mul_comm a b := by
    refine LinearMap.ext fun f => ?_
    change a (innerInt p b (f.comp (mulCM₂ G))) = b (innerInt p a (f.comp (mulCM₂ G)))
    rw [integral_swap]
    congr 1
    ext y
    change a _ = a _
    congr 1
    ext x
    change f (x * y) = f (y * x)
    rw [mul_comm]

@[simp]
theorem conv_dirac_mul_dirac (u v : G) :
    (dirac p u : PadicMeasure p G) * dirac p v = dirac p (u * v) :=
  LinearMap.ext fun _f => rfl

section degree

/-- The degree (augmentation) map `Λ(G) → ℤ_p`, `μ ↦ ∫_G 1 dμ`.

Source: RJW Def. 3.37 (`DefAugmentationIdealFiniteLevel`, TeX lines 1245–1253); the
inverse-limit degree map is evaluation at the constant function `1`. -/
noncomputable def deg : PadicMeasure p G →+* ℤ_[p] where
  toFun μ := μ 1
  map_one' := by
    change (1 : C(G, ℤ_[p])) 1 = 1
    rfl
  map_mul' μ ν := by
    change μ (innerInt p ν ((1 : C(G, ℤ_[p])).comp (mulCM₂ G))) = μ 1 * ν 1
    have h1 : innerInt p ν ((1 : C(G, ℤ_[p])).comp (mulCM₂ G))
        = ν 1 • (1 : C(G, ℤ_[p])) := by
      ext x
      change ν _ = _
      have hc : ((1 : C(G, ℤ_[p])).comp (mulCM₂ G)).curry x
          = (1 : C(G, ℤ_[p])) := ContinuousMap.ext fun y => rfl
      rw [hc]
      simp [smul_eq_mul]
    rw [h1, map_smul, smul_eq_mul, mul_comm]
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The augmentation ideal `I(G) = ker(deg)`. Source: RJW Def. 3.37. -/
noncomputable def augmentationIdeal : Ideal (PadicMeasure p G) :=
  RingHom.ker (deg p)

end degree

end convolution

section unitsSpecialisations

/-! Specialisations at `G = ℤ_p^×` — every name and statement below is exactly what the
pre-generalisation file exported, so downstream users (`ZetaP`, `EisensteinFamily`,
`TameConductor`, `MeasureR/UnitsRing`, …) are unaffected. -/

/-- Multiplication on `ℤ_[p]ˣ` as a single continuous map. -/
abbrev unitsMulCM₂ : C(ℤ_[p]ˣ × ℤ_[p]ˣ, ℤ_[p]ˣ) := mulCM₂ ℤ_[p]ˣ

/-- Convolution of measures on the multiplicative group `ℤ_p^×`:
`∫ f d(μ ⋆ ν) = ∫ (∫ f(xy) dν(y)) dμ(x)`.

Source: RJW Eq. (3.11) (`eq:convolution`, TeX lines 1173–1175). -/
noncomputable abbrev unitsConv (μ ν : PadicMeasure p ℤ_[p]ˣ) : PadicMeasure p ℤ_[p]ˣ :=
  conv p μ ν

lemma units_mul_def (μ ν : PadicMeasure p ℤ_[p]ˣ) : μ * ν = unitsConv p μ ν := rfl

@[simp]
lemma units_mul_apply (μ ν : PadicMeasure p ℤ_[p]ˣ) (f : C(ℤ_[p]ˣ, ℤ_[p])) :
    (μ * ν) f = μ (innerInt p ν (f.comp (unitsMulCM₂ p))) := rfl

lemma units_one_def : (1 : PadicMeasure p ℤ_[p]ˣ) = dirac p 1 := rfl

@[simp]
theorem units_dirac_mul_dirac (u v : ℤ_[p]ˣ) :
    (dirac p u : PadicMeasure p ℤ_[p]ˣ) * dirac p v = dirac p (u * v) :=
  conv_dirac_mul_dirac p u v

end unitsSpecialisations

section finiteLevel

/-- Reduction `ℤ_p^× → (ℤ/p^n)^×` (units functor applied to `PadicInt.toZModPow`). -/
noncomputable def unitsToZModPow (n : ℕ) : ℤ_[p]ˣ →* (ZMod (p ^ n))ˣ :=
  Units.map (PadicInt.toZModPow n).toMonoidHom

@[simp]
lemma unitsToZModPow_coe (n : ℕ) (u : ℤ_[p]ˣ) :
    ((unitsToZModPow p n u : (ZMod (p ^ n))ˣ) : ZMod (p ^ n))
      = PadicInt.toZModPow n (u : ℤ_[p]) := rfl

/-- Residue discs mod `p^n` are clopen in `ℤ_p` (open and with open complement). -/
lemma isClopen_toZModPow_fiber (n : ℕ) (a : ZMod (p ^ n)) :
    IsClopen {z : ℤ_[p] | PadicInt.toZModPow n z = a} := by
  classical
  refine ⟨?_, isOpen_toZModPow_fiber p n a⟩
  rw [← isOpen_compl_iff]
  have hcompl : {z : ℤ_[p] | PadicInt.toZModPow n z = a}ᶜ
      = ⋃ b ∈ Finset.univ.erase a, {z : ℤ_[p] | PadicInt.toZModPow n z = b} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_erase,
      Finset.mem_univ, and_true, exists_prop]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨b, hb, hzb⟩ => hzb ▸ hb⟩
  rw [hcompl]
  exact isOpen_biUnion fun b _ => isOpen_toZModPow_fiber p n b

/-- The fibre of `unitsToZModPow n` over a residue `g` is clopen in `ℤ_p^×`. -/
lemma isClopen_unitsToZModPow_fiber (n : ℕ) (g : (ZMod (p ^ n))ˣ) :
    IsClopen (unitsToZModPow p n ⁻¹' {g}) := by
  have hset : unitsToZModPow p n ⁻¹' {g}
      = (Units.val) ⁻¹' {z : ℤ_[p] | PadicInt.toZModPow n z = (g : ZMod (p ^ n))} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨fun h => by rw [← h]; rfl, fun h => Units.ext h⟩
  rw [hset]
  exact (isClopen_toZModPow_fiber p n _).preimage Units.continuous_val

/-- The indicator of a level-`n` residue disc, as a continuous map on `ℤ_p^×`. -/
noncomputable def levelChar (n : ℕ) (g : (ZMod (p ^ n))ˣ) : C(ℤ_[p]ˣ, ℤ_[p]) :=
  (LocallyConstant.charFn ℤ_[p] (isClopen_unitsToZModPow_fiber p n g) : C(ℤ_[p]ˣ, ℤ_[p]))

lemma levelChar_apply_eq {n : ℕ} {g : (ZMod (p ^ n))ˣ} {u : ℤ_[p]ˣ}
    (h : unitsToZModPow p n u = g) : levelChar p n g u = 1 := by
  simp only [levelChar, LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn]
  rw [Set.indicator_of_mem (show u ∈ unitsToZModPow p n ⁻¹' {g} from h), Pi.one_apply]

lemma levelChar_apply_ne {n : ℕ} {g : (ZMod (p ^ n))ˣ} {u : ℤ_[p]ˣ}
    (h : unitsToZModPow p n u ≠ g) : levelChar p n g u = 0 := by
  simp only [levelChar, LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn]
  rw [Set.indicator_of_notMem (show u ∉ unitsToZModPow p n ⁻¹' {g} from h)]

/-- The finite-level map `Λ(ℤ_p^×) → ℤ_p[(ℤ/p^n)^×]` sending a measure to
`∑_{g} μ(𝟙_{g\text{-fibre}}) · [g]`. These are the maps whose inverse limit is the
Iwasawa algebra; we use them (rather than the full limit) for RJW Lem. 3.38.

Source: RJW TeX lines 888–892 (the map `μ ↦ λ_H = ∑ μ(aH)[a]`). -/
noncomputable def levelMap (n : ℕ) :
    PadicMeasure p ℤ_[p]ˣ →+* MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ where
  toFun μ := ∑ g : (ZMod (p ^ n))ˣ, MonoidAlgebra.single g (μ (levelChar p n g))
  map_one' := by
    classical
    rw [MonoidAlgebra.one_def, Finset.sum_eq_single (1 : (ZMod (p ^ n))ˣ)]
    · rw [show ((1 : PadicMeasure p ℤ_[p]ˣ)) (levelChar p n 1) = 1 from by
        rw [units_one_def, dirac_apply, levelChar_apply_eq p (map_one (unitsToZModPow p n))]]
    · intro g _ hg
      rw [show ((1 : PadicMeasure p ℤ_[p]ˣ)) (levelChar p n g) = 0 from by
          rw [units_one_def, dirac_apply,
            levelChar_apply_ne p (by rw [map_one]; exact fun h => hg h.symm)],
        MonoidAlgebra.single_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  map_mul' μ ν := by
    classical
    -- the inner integral of a level indicator is again a level indicator
    have hcurry : ∀ (c : (ZMod (p ^ n))ˣ) (x : ℤ_[p]ˣ),
        ((levelChar p n c).comp (unitsMulCM₂ p)).curry x
          = levelChar p n ((unitsToZModPow p n x)⁻¹ * c) := by
      intro c x
      ext y
      change levelChar p n c (x * y) = _
      by_cases hy : unitsToZModPow p n y = (unitsToZModPow p n x)⁻¹ * c
      · rw [levelChar_apply_eq p (by rw [map_mul, hy, mul_inv_cancel_left]),
          levelChar_apply_eq p hy]
      · rw [levelChar_apply_ne p (fun hxy => hy ?_), levelChar_apply_ne p hy]
        rw [map_mul] at hxy
        rw [← hxy, inv_mul_cancel_left]
    -- hence the convolution against a level indicator is a finite sum
    have hconv : ∀ c : (ZMod (p ^ n))ˣ,
        (μ * ν) (levelChar p n c)
          = ∑ a : (ZMod (p ^ n))ˣ, μ (levelChar p n a) * ν (levelChar p n (a⁻¹ * c)) := by
      intro c
      rw [units_mul_apply]
      have hfn : innerInt p ν ((levelChar p n c).comp (unitsMulCM₂ p))
          = ∑ a : (ZMod (p ^ n))ˣ,
              ν (levelChar p n (a⁻¹ * c)) • levelChar p n a := by
        ext x
        rw [innerInt_apply, hcurry c x]
        rw [show (∑ a : (ZMod (p ^ n))ˣ,
            ν (levelChar p n (a⁻¹ * c)) • levelChar p n a) x
            = ∑ a : (ZMod (p ^ n))ˣ,
              ν (levelChar p n (a⁻¹ * c)) * levelChar p n a x from by
          simp [Finset.sum_apply]]
        rw [Finset.sum_eq_single (unitsToZModPow p n x)]
        · rw [levelChar_apply_eq p rfl, mul_one]
        · intro a _ ha
          rw [levelChar_apply_ne p (fun h => ha h.symm), mul_zero]
        · exact fun h => absurd (Finset.mem_univ _) h
      rw [hfn, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    -- expand the product of the two finite sums and reindex
    rw [show (∑ g : (ZMod (p ^ n))ˣ, MonoidAlgebra.single g (μ (levelChar p n g))) *
        (∑ h : (ZMod (p ^ n))ˣ, MonoidAlgebra.single h (ν (levelChar p n h)))
        = ∑ g : (ZMod (p ^ n))ˣ, ∑ h : (ZMod (p ^ n))ˣ,
            MonoidAlgebra.single (g * h) (μ (levelChar p n g) * ν (levelChar p n h)) from by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ =>
        MonoidAlgebra.single_mul_single g h _ _]
    calc ∑ c : (ZMod (p ^ n))ˣ, MonoidAlgebra.single c ((μ * ν) (levelChar p n c))
        = ∑ c : (ZMod (p ^ n))ˣ, ∑ a : (ZMod (p ^ n))ˣ,
            MonoidAlgebra.single c
              (μ (levelChar p n a) * ν (levelChar p n (a⁻¹ * c))) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hconv c]
          exact map_sum (Finsupp.singleAddHom c) _ _
      _ = ∑ a : (ZMod (p ^ n))ˣ, ∑ c : (ZMod (p ^ n))ˣ,
            MonoidAlgebra.single c
              (μ (levelChar p n a) * ν (levelChar p n (a⁻¹ * c))) := Finset.sum_comm
      _ = ∑ g : (ZMod (p ^ n))ˣ, ∑ h : (ZMod (p ^ n))ˣ,
            MonoidAlgebra.single (g * h)
              (μ (levelChar p n g) * ν (levelChar p n h)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          refine (Fintype.sum_equiv (Equiv.mulLeft g)
            (fun h => MonoidAlgebra.single (g * h)
              (μ (levelChar p n g) * ν (levelChar p n h)))
            (fun c => MonoidAlgebra.single c
              (μ (levelChar p n g) * ν (levelChar p n (g⁻¹ * c)))) (fun h => ?_)).symm
          rw [show (Equiv.mulLeft g) h = g * h from rfl, inv_mul_cancel_left]
  map_zero' := by
    classical
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [LinearMap.zero_apply, MonoidAlgebra.single_zero]
  map_add' μ ν := by
    classical
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => by
      rw [LinearMap.add_apply, MonoidAlgebra.single_add]

/-- The `g`-coefficient of `levelMap n μ` is the measure of the `g`-disc. -/
lemma levelMap_apply_coeff (n : ℕ) (μ : PadicMeasure p ℤ_[p]ˣ) (g : (ZMod (p ^ n))ˣ) :
    (levelMap p n μ) g = μ (levelChar p n g) := by
  classical
  rw [show (levelMap p n μ) g = (∑ c : (ZMod (p ^ n))ˣ,
      MonoidAlgebra.single c (μ (levelChar p n c))) g from rfl,
    show (∑ c : (ZMod (p ^ n))ˣ, MonoidAlgebra.single c (μ (levelChar p n c))) g
      = ∑ c : (ZMod (p ^ n))ˣ, (MonoidAlgebra.single c (μ (levelChar p n c))) g from
    map_sum (Finsupp.applyAddHom (M := ℤ_[p]) g) _ _]
  simp only [MonoidAlgebra.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma levelMap_eq_zero_iff (n : ℕ) (μ : PadicMeasure p ℤ_[p]ˣ) :
    levelMap p n μ = 0 ↔ ∀ g : (ZMod (p ^ n))ˣ, μ (levelChar p n g) = 0 := by
  constructor
  · intro h g
    rw [← levelMap_apply_coeff p n μ g, h]
    rfl
  · intro h
    change (∑ c : (ZMod (p ^ n))ˣ, MonoidAlgebra.single c (μ (levelChar p n c))) = 0
    exact Finset.sum_eq_zero fun c _ => by rw [h c, MonoidAlgebra.single_zero]

/-- The level indicators sum to `1` (partition of `ℤ_p^×` into residue discs). -/
lemma sum_levelChar (n : ℕ) :
    (∑ g : (ZMod (p ^ n))ˣ, levelChar p n g) = (1 : C(ℤ_[p]ˣ, ℤ_[p])) := by
  ext u
  rw [show (∑ g : (ZMod (p ^ n))ˣ, levelChar p n g) u
      = ∑ g : (ZMod (p ^ n))ˣ, levelChar p n g u from by
    simp [Finset.sum_apply], Finset.sum_eq_single (unitsToZModPow p n u)]
  · rw [levelChar_apply_eq p rfl, ContinuousMap.one_apply]
  · intro c _ hcu
    exact levelChar_apply_ne p fun hc => hcu hc.symm
  · exact fun hu => absurd (Finset.mem_univ _) hu

lemma levelMap_dirac (n : ℕ) (u : ℤ_[p]ˣ) :
    levelMap p n (dirac p u) = MonoidAlgebra.single (unitsToZModPow p n u) 1 := by
  change (∑ g : (ZMod (p ^ n))ˣ, MonoidAlgebra.single g ((dirac p u) (levelChar p n g))) = _
  rw [Finset.sum_eq_single (unitsToZModPow p n u)]
  · rw [dirac_apply, levelChar_apply_eq p rfl]
  · intro g _ hgu
    rw [dirac_apply, levelChar_apply_ne p fun hg => hgu hg.symm, MonoidAlgebra.single_zero]
  · exact fun hu => absurd (Finset.mem_univ _) hu

lemma levelMap_smul (n : ℕ) (c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]ˣ) :
    levelMap p n (c • μ) = c • levelMap p n μ := by
  change (∑ g : (ZMod (p ^ n))ˣ, MonoidAlgebra.single g ((c • μ) (levelChar p n g)))
      = c • ∑ g : (ZMod (p ^ n))ˣ, MonoidAlgebra.single g (μ (levelChar p n g))
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, smul_eq_mul]
  rw [show c • (MonoidAlgebra.single g (μ (levelChar p n g)) :
      MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ)
      = MonoidAlgebra.single g (c • μ (levelChar p n g)) from
    MonoidAlgebra.smul_single c g _, smul_eq_mul]

/-- Compatibility of the reductions: level `n` factors through any level `m ≥ n`. -/
lemma unitsToZModPow_le {n m : ℕ} (h : n ≤ m) (a : ℤ_[p]ˣ) :
    unitsToZModPow p n a
      = ZMod.unitsMap (pow_dvd_pow p h) (unitsToZModPow p m a) := by
  apply Units.ext
  change PadicInt.toZModPow n (a : ℤ_[p])
      = ZMod.castHom (pow_dvd_pow p h) _ (PadicInt.toZModPow m (a : ℤ_[p]))
  exact (RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n m h) _).symm

/-- The reduction `ℤ_p^× → (ℤ/p^n)^×` is surjective: lift the canonical representative. -/
lemma unitsToZModPow_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (unitsToZModPow p n) := by
  intro c
  set z : ℤ_[p] := (((c : ZMod (p ^ n)).val : ℕ) : ℤ_[p]) with hz
  have hzc : PadicInt.toZModPow n z = (c : ZMod (p ^ n)) := by
    rw [hz, map_natCast]
    exact ZMod.natCast_rightInverse _
  have hunit : IsUnit z := by
    rw [PadicInt.isUnit_iff]
    by_contra hne
    have hlt : ‖z‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one z) hne
    have hker : PadicInt.toZModPow 1 z = 0 := by
      have hle : ‖z‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
        rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
        simpa using hlt
      have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow z 1).1 hle
      rwa [← PadicInt.ker_toZModPow, RingHom.mem_ker] at hmem
    -- but `z` is a unit mod `p^n`, hence a unit mod `p`
    have hcast : PadicInt.toZModPow 1 z
        = ZMod.castHom (pow_dvd_pow p hn) _ (PadicInt.toZModPow n z) :=
      (RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow 1 n hn) _).symm
    rw [hcast, hzc] at hker
    have hu : IsUnit (ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 1)) (c : ZMod (p ^ n))) :=
      c.isUnit.map (ZMod.castHom (pow_dvd_pow p hn) (ZMod (p ^ 1)))
    rw [hker] at hu
    haveI : Nontrivial (ZMod (p ^ 1)) := by
      rw [pow_one]; infer_instance
    exact not_isUnit_zero hu
  exact ⟨hunit.unit, Units.ext (by rw [unitsToZModPow_coe, IsUnit.unit_spec]; exact hzc)⟩

/-- The level sets `{v | v ≡ u mod p^n}` form a neighbourhood basis in `ℤ_p^×`. -/
lemma exists_level_subset {u : ℤ_[p]ˣ} {U : Set ℤ_[p]ˣ} (hU : IsOpen U) (hu : u ∈ U) :
    ∃ n, {v : ℤ_[p]ˣ | unitsToZModPow p n v = unitsToZModPow p n u} ⊆ U := by
  have himg : IsOpen ((unitsHomeo p) '' U) := (unitsHomeo p).isOpen_image.2 hU
  obtain ⟨V, hV, hVW⟩ := isOpen_induced_iff.1 himg
  have humem : ((u : ℤ_[p])) ∈ V := by
    have hmem : (unitsHomeo p u) ∈ (unitsHomeo p) '' U := Set.mem_image_of_mem _ hu
    rw [← hVW] at hmem
    exact hmem
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV _ humem
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨n, fun v hv => ?_⟩
  have hnorm : ‖(v : ℤ_[p]) - (u : ℤ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
      map_sub, sub_eq_zero]
    exact congrArg Units.val hv
  have hvV : ((v : ℤ_[p])) ∈ V :=
    hball (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_le_of_lt hnorm hn)
  have hmem : (unitsHomeo p v) ∈ (unitsHomeo p) '' U := by
    rw [← hVW]
    exact hvV
  obtain ⟨w, hwU, hw⟩ := hmem
  rwa [(unitsHomeo p).injective hw] at hwU

/-- Every locally constant function on `ℤ_p^×` factors through a finite level. -/
lemma exists_level_factorization (g : LocallyConstant ℤ_[p]ˣ ℤ_[p]) :
    ∃ N, 0 < N ∧ ∀ u v : ℤ_[p]ˣ,
      unitsToZModPow p N u = unitsToZModPow p N v → g u = g v := by
  classical
  have hpt : ∀ u : ℤ_[p]ˣ, ∃ n,
      {v : ℤ_[p]ˣ | unitsToZModPow p n v = unitsToZModPow p n u} ⊆ {v | g v = g u} :=
    fun u => exists_level_subset p (g.isLocallyConstant.isClopen_fiber (g u)).isOpen rfl
  choose nfun hnfun using hpt
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover isCompact_univ
    (fun u : ℤ_[p]ˣ =>
      {v : ℤ_[p]ˣ | unitsToZModPow p (nfun u) v = unitsToZModPow p (nfun u) u})
    (fun u => (isClopen_unitsToZModPow_fiber p (nfun u) (unitsToZModPow p (nfun u) u)).isOpen)
    (fun u _ => Set.mem_iUnion.2 ⟨u, rfl⟩)
  refine ⟨max (t.sup nfun) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun u v huv => ?_⟩
  obtain ⟨w, hwt, hw⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ u))
  have hn_le : nfun w ≤ max (t.sup nfun) 1 :=
    le_trans (Finset.le_sup hwt) (le_max_left _ _)
  have huv' : unitsToZModPow p (nfun w) u = unitsToZModPow p (nfun w) v := by
    rw [unitsToZModPow_le p hn_le u, unitsToZModPow_le p hn_le v, huv]
  have hvw : v ∈ {x : ℤ_[p]ˣ | unitsToZModPow p (nfun w) x = unitsToZModPow p (nfun w) w} := by
    rw [Set.mem_setOf_eq, ← huv']
    exact hw
  exact (hnfun w hw).trans (hnfun w hvw).symm

/-- The finite-level maps are jointly injective: a measure vanishing on every
finite-level indicator is zero (locally constant functions on `ℤ_p^×` factor through
some level). Source: RJW Rem. 3.8 + Prop. 3.10 (inverse-limit description). -/
theorem levelMap_jointly_injective (μ : PadicMeasure p ℤ_[p]ˣ)
    (h : ∀ n, levelMap p n μ = 0) : μ = 0 := by
  classical
  have hcoeff : ∀ (n : ℕ) (g : (ZMod (p ^ n))ˣ), μ (levelChar p n g) = 0 :=
    fun n => (levelMap_eq_zero_iff p n μ).1 (h n)
  refine ext_locallyConstant p fun g => ?_
  rw [LinearMap.zero_apply]
  obtain ⟨N, hN, hfac⟩ := exists_level_factorization p g
  have hg : (g : C(ℤ_[p]ˣ, ℤ_[p]))
      = ∑ c : (ZMod (p ^ N))ˣ,
          g ((unitsToZModPow_surjective p N hN c).choose) • levelChar p N c := by
    ext u
    have hval : (∑ c : (ZMod (p ^ N))ˣ,
        g ((unitsToZModPow_surjective p N hN c).choose) • levelChar p N c) u
        = ∑ c : (ZMod (p ^ N))ˣ,
          g ((unitsToZModPow_surjective p N hN c).choose) * levelChar p N c u := by
      simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
        Pi.smul_apply, smul_eq_mul]
    rw [hval]
    have hsum : (∑ c : (ZMod (p ^ N))ˣ,
        g ((unitsToZModPow_surjective p N hN c).choose) * levelChar p N c u) = g u := by
      rw [Finset.sum_eq_single (unitsToZModPow p N u)]
      · rw [levelChar_apply_eq p rfl, mul_one]
        exact hfac _ u ((unitsToZModPow_surjective p N hN _).choose_spec)
      · intro c _ hcu
        rw [levelChar_apply_ne p fun hc => hcu hc.symm, mul_zero]
      · exact fun hu => absurd (Finset.mem_univ _) hu
    rw [hsum]
    rfl
  rw [hg, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [map_smul, hcoeff N c, smul_zero]

/-- Refinement: the level-`m` discs inside a level-`n` disc sum to its indicator. -/
lemma sum_levelChar_fiber {n m : ℕ} (h : n ≤ m) (cbar : (ZMod (p ^ n))ˣ) :
    (∑ c ∈ Finset.univ.filter
        (fun c : (ZMod (p ^ m))ˣ => ZMod.unitsMap (pow_dvd_pow p h) c = cbar),
      levelChar p m c) = levelChar p n cbar := by
  classical
  ext u
  rw [show (∑ c ∈ Finset.univ.filter
      (fun c : (ZMod (p ^ m))ˣ => ZMod.unitsMap (pow_dvd_pow p h) c = cbar),
      levelChar p m c) u
      = ∑ c ∈ Finset.univ.filter
        (fun c : (ZMod (p ^ m))ˣ => ZMod.unitsMap (pow_dvd_pow p h) c = cbar),
        levelChar p m c u from by simp [Finset.sum_apply]]
  by_cases hu : unitsToZModPow p n u = cbar
  · rw [levelChar_apply_eq p hu, Finset.sum_eq_single (unitsToZModPow p m u)]
    · exact levelChar_apply_eq p rfl
    · intro c _ hcu
      exact levelChar_apply_ne p fun h' => hcu h'.symm
    · intro hmem
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _,
        by rw [← unitsToZModPow_le p h u, hu]⟩) hmem
  · rw [levelChar_apply_ne p hu]
    refine Finset.sum_eq_zero fun c hc => ?_
    rw [Finset.mem_filter] at hc
    refine levelChar_apply_ne p fun hqu => hu ?_
    rw [← hc.2, ← hqu, ← unitsToZModPow_le p h u]

/-- The level maps are compatible with coefficient transport along the reductions. -/
lemma mapDomain_levelMap {n m : ℕ} (h : n ≤ m) (μ : PadicMeasure p ℤ_[p]ˣ) :
    Finsupp.mapDomain (ZMod.unitsMap (pow_dvd_pow p h)) (levelMap p m μ)
      = levelMap p n μ := by
  classical
  change Finsupp.mapDomain _
      (∑ c : (ZMod (p ^ m))ˣ, MonoidAlgebra.single c (μ (levelChar p m c))) = _
  rw [Finsupp.mapDomain_finsetSum]
  simp_rw [show ∀ c : (ZMod (p ^ m))ˣ, Finsupp.mapDomain
      (ZMod.unitsMap (pow_dvd_pow p h)) (MonoidAlgebra.single c (μ (levelChar p m c)))
      = MonoidAlgebra.single (ZMod.unitsMap (pow_dvd_pow p h) c) (μ (levelChar p m c)) from
    fun c => Finsupp.mapDomain_single]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun c : (ZMod (p ^ m))ˣ => ZMod.unitsMap (pow_dvd_pow p h) c)
    (t := Finset.univ) (fun c _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun cbar _ => ?_
  calc (∑ c ∈ Finset.univ.filter
      (fun c : (ZMod (p ^ m))ˣ => ZMod.unitsMap (pow_dvd_pow p h) c = cbar),
        MonoidAlgebra.single (ZMod.unitsMap (pow_dvd_pow p h) c) (μ (levelChar p m c)))
      = ∑ c ∈ Finset.univ.filter
          (fun c : (ZMod (p ^ m))ˣ => ZMod.unitsMap (pow_dvd_pow p h) c = cbar),
          MonoidAlgebra.single cbar (μ (levelChar p m c)) :=
        Finset.sum_congr rfl fun c hc => by rw [(Finset.mem_filter.1 hc).2]
    _ = MonoidAlgebra.single cbar (∑ c ∈ Finset.univ.filter
          (fun c : (ZMod (p ^ m))ˣ => ZMod.unitsMap (pow_dvd_pow p h) c = cbar),
          μ (levelChar p m c)) :=
        (map_sum (Finsupp.singleAddHom cbar) _ _).symm
    _ = MonoidAlgebra.single cbar (μ (∑ c ∈ Finset.univ.filter
          (fun c : (ZMod (p ^ m))ˣ => ZMod.unitsMap (pow_dvd_pow p h) c = cbar),
          levelChar p m c)) := by rw [map_sum]
    _ = MonoidAlgebra.single cbar (μ (levelChar p n cbar)) := by
        rw [sum_levelChar_fiber p h cbar]

/-- Telescoping: `[c] − 1` lies in the ideal generated by `[g] − 1` whenever `c` is a
power of `g`. -/
lemma single_sub_one_mem_span {n : ℕ} {gbar : (ZMod (p ^ n))ˣ}
    (hg : Subgroup.zpowers gbar = ⊤) (c : (ZMod (p ^ n))ˣ) :
    (MonoidAlgebra.single c 1 - 1 : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ)
      ∈ Ideal.span {MonoidAlgebra.single gbar 1 - 1} := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, gbar ^ k = c := by
    have hmem : c ∈ Subgroup.zpowers gbar := hg ▸ Subgroup.mem_top c
    exact mem_powers_iff_mem_zpowers.2 hmem
  subst hk
  induction k with
  | zero =>
    simp only [pow_zero, ← MonoidAlgebra.one_def, sub_self]
    exact Ideal.zero_mem _
  | succ m ih =>
    have key : (MonoidAlgebra.single (gbar ^ (m + 1)) 1 - 1 :
          MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ)
        = MonoidAlgebra.single gbar 1 * (MonoidAlgebra.single (gbar ^ m) 1 - 1)
          + (MonoidAlgebra.single gbar 1 - 1) := by
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_one, ← pow_succ']
      ring
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.subset_span rfl)

/-- Reconstruction: a group-ring element is the sum of its single components. -/
lemma sum_single_coeff {n : ℕ} (y : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ) :
    (∑ c : (ZMod (p ^ n))ˣ, MonoidAlgebra.single c (y c)) = y :=
  Finsupp.univ_sum_single y

/-- An element of the group ring with vanishing coefficient sum lies in the ideal
generated by `[g]−1`, for `g` a generator (RJW TeX lines 1265–1268). -/
lemma mem_span_of_sum_eq_zero {n : ℕ} {gbar : (ZMod (p ^ n))ˣ}
    (hg : Subgroup.zpowers gbar = ⊤) (x : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ)
    (hx : ∑ c : (ZMod (p ^ n))ˣ, x c = 0) :
    x ∈ Ideal.span
      {(MonoidAlgebra.single gbar 1 - 1 : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ)} := by
  classical
  have hdecomp : x = ∑ c : (ZMod (p ^ n))ˣ,
      (x c) • ((MonoidAlgebra.single c 1 - 1 : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ)) := by
    calc x = ∑ c : (ZMod (p ^ n))ˣ, MonoidAlgebra.single c (x c) := (sum_single_coeff p x).symm
      _ = ∑ c : (ZMod (p ^ n))ˣ,
          ((x c) • (MonoidAlgebra.single c 1 - 1 : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ)
            + (x c) • (1 : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← smul_add, sub_add_cancel]
          rw [show (x c) • (MonoidAlgebra.single c 1 : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ)
              = MonoidAlgebra.single c (x c) from by
            rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]]
      _ = (∑ c : (ZMod (p ^ n))ˣ,
            (x c) • (MonoidAlgebra.single c 1 - 1 : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ))
          + (∑ c : (ZMod (p ^ n))ˣ, x c) • (1 : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ) := by
          rw [Finset.sum_add_distrib, Finset.sum_smul]
      _ = ∑ c : (ZMod (p ^ n))ˣ,
            (x c) • (MonoidAlgebra.single c 1 - 1 : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ) := by
          rw [hx, zero_smul, add_zero]
  rw [hdecomp]
  exact Ideal.sum_mem _ fun c _ => by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (single_sub_one_mem_span p hg c)

/-- The coefficient sum of `levelMap n E` is the degree of `E`. -/
lemma sum_levelMap_coeff (n : ℕ) (E : PadicMeasure p ℤ_[p]ˣ) :
    ∑ c : (ZMod (p ^ n))ˣ, (levelMap p n E) c = deg p E := by
  simp_rw [levelMap_apply_coeff]
  rw [← map_sum E, sum_levelChar]
  rfl

/-- Evaluation of `([a]−[1])·ν`: translation difference. -/
lemma dirac_sub_one_mul_apply (a : ℤ_[p]ˣ) (ν : PadicMeasure p ℤ_[p]ˣ)
    (f : C(ℤ_[p]ˣ, ℤ_[p])) :
    ((dirac p a - 1) * ν) f
      = ν ((f.comp (unitsMulCM₂ p)).curry a) - ν ((f.comp (unitsMulCM₂ p)).curry 1) := by
  change ((dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ))
      (innerInt p ν (f.comp (unitsMulCM₂ p))) = _
  rw [LinearMap.sub_apply, dirac_apply, units_one_def, dirac_apply, innerInt_apply,
    innerInt_apply]

end finiteLevel

section zeroDivisor

/-- The function `x ↦ x^k` on `ℤ_p^×`, as a continuous map to `ℤ_p`. -/
def unitsPowCM (k : ℕ) : C(ℤ_[p]ˣ, ℤ_[p]) :=
  ⟨fun u => (u : ℤ_[p]) ^ k, (Units.continuous_val.pow k)⟩

/-- **RJW Lem. 3.36(i) (`lem:zero divisor`)**: a measure on `ℤ_p^×` with
`∫ x^k dμ = 0` for all `k > 0` is zero. Source proof (TeX lines 1228–1229): the Mahler
transform of `ιμ` is constant (binomial polynomials with `n ≥ 1` have no constant
term), and `ψ` fixes constants while killing `ιμ`; hence `𝓐_{ιμ} = 0`. -/
theorem eq_zero_of_forall_unitsPowCM_eq_zero (μ : PadicMeasure p ℤ_[p]ˣ)
    (h : ∀ k, 0 < k → μ (unitsPowCM p k) = 0) : μ = 0 := by
  -- Step 1: the positive Mahler coefficients of `ι μ` vanish
  have hcoeff : ∀ n : ℕ, 0 < n → (iota p μ) (mahler n) = 0 := by
    intro n hn
    obtain ⟨q, hq⟩ : (Polynomial.X : Polynomial ℤ_[p]) ∣ descPochhammer ℤ_[p] n := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, descPochhammer_eval_zero]
      simp [hn.ne']
    have hbridge : ∀ x : ℤ_[p],
        (descPochhammer ℤ_[p] n).eval x = (descPochhammer ℤ n).smeval x := by
      intro x
      rw [← descPochhammer_map (Int.castRingHom ℤ_[p]) n, Polynomial.eval_map,
        Polynomial.eval₂_eq_sum, Polynomial.smeval_eq_sum, Polynomial.sum_def,
        Polynomial.sum_def]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.smul_pow, zsmul_eq_mul]
      rfl
    have hfun : (n.factorial • mahler n : C(ℤ_[p], ℤ_[p]))
        = ⟨fun x => (descPochhammer ℤ_[p] n).eval x,
            (descPochhammer ℤ_[p] n).continuous⟩ := by
      ext x
      change n.factorial • mahler n x = (descPochhammer ℤ_[p] n).eval x
      rw [mahler_apply, hbridge x, Ring.descPochhammer_eq_factorial_smul_choose]
    have hint : (iota p μ) (n.factorial • mahler n) = 0 := by
      rw [hfun]
      change μ ((⟨fun x => (descPochhammer ℤ_[p] n).eval x,
        (descPochhammer ℤ_[p] n).continuous⟩ : C(ℤ_[p], ℤ_[p])).comp (unitsValCM p)) = 0
      have hcomp : ((⟨fun x => (descPochhammer ℤ_[p] n).eval x,
            (descPochhammer ℤ_[p] n).continuous⟩ : C(ℤ_[p], ℤ_[p])).comp (unitsValCM p))
          = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • unitsPowCM p (i + 1) := by
        ext u
        simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, unitsValCM,
          ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
          smul_eq_mul, unitsPowCM]
        rw [hq, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_eq_sum_range,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hcomp, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, h (i + 1) (Nat.succ_pos i), smul_zero]
    rw [map_nsmul] at hint
    refine nsmul_right_injective (M := ℤ_[p]) (Nat.factorial_ne_zero n) ?_
    change n.factorial • ((iota p μ) (mahler n)) = n.factorial • (0 : ℤ_[p])
    rw [hint, smul_zero]
  -- Step 2: `𝓐(ιμ)` is constant, so `ιμ` is a multiple of `δ₀`
  set c₀ := (iota p μ) (mahler 0) with hc₀
  have hμδ : iota p μ = c₀ • dirac p 0 := by
    apply mahlerTransform_injective p
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coeff_mahlerTransform, coeff_mahlerTransform, LinearMap.smul_apply, dirac_apply,
        mahler_apply, Ring.choose_zero_right, smul_eq_mul, mul_one, hc₀]
    · rw [coeff_mahlerTransform, coeff_mahlerTransform, hcoeff n hn, LinearMap.smul_apply,
        dirac_apply, mahler_apply,
        show (0 : ℤ_[p]) = ((0 : ℕ) : ℤ_[p]) from by norm_num, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt hn, Nat.cast_zero, smul_zero]
  -- Step 3: `ψ` kills `ιμ` but fixes multiples of `δ₀`
  have hψ : psi p (iota p μ) = 0 := by
    rw [← isSupportedOn_units_iff_psi_eq_zero]
    exact res_iota p μ
  have hψδ : psi p ((c₀ • dirac p 0 : PadicMeasure p ℤ_[p])) = c₀ • dirac p 0 := by
    have hsd : shiftDiv p 0 = 0 := by
      have hdig : digit p (0 : ℤ_[p]) = 0 := by
        rw [digit, map_zero, ZMod.val_zero, Nat.cast_zero]
      refine Subtype.ext ?_
      change (((0 : ℤ_[p]) : ℚ_[p]) - (digit p (0 : ℤ_[p]) : ℚ_[p])) / (p : ℚ_[p])
          = ((0 : ℤ_[p]) : ℚ_[p])
      rw [hdig]
      simp
    refine LinearMap.ext fun f => ?_
    change (c₀ • dirac p 0)
        ((LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) *
          f.comp (shiftDiv p)) = (c₀ • dirac p 0) f
    rw [LinearMap.smul_apply, LinearMap.smul_apply, dirac_apply, dirac_apply]
    congr 1
    change (LocallyConstant.charFn ℤ_[p] (isClopen_pZp p) : C(ℤ_[p], ℤ_[p])) 0 *
        f (shiftDiv p 0) = f 0
    have h0mem : (0 : ℤ_[p]) ∈ {x : ℤ_[p] | ‖x‖ < 1} := by
      simp [Set.mem_setOf_eq]
    rw [hsd]
    simp only [LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn]
    rw [Set.indicator_of_mem h0mem, Pi.one_apply, one_mul]
  rw [hμδ, hψδ] at hψ
  have hc0 : c₀ = 0 := by
    have heval := LinearMap.congr_fun hψ (1 : C(ℤ_[p], ℤ_[p]))
    simpa using heval
  rw [hc0, zero_smul] at hμδ
  exact iota_injective p (hμδ.trans (map_zero (iota p)).symm)

/-- Power moments are multiplicative for the convolution product:
`∫(xy)^k = (∫x^k)(∫y^k)` (RJW TeX line 1233). -/
lemma units_mul_apply_unitsPowCM (μ ν : PadicMeasure p ℤ_[p]ˣ) (k : ℕ) :
    (μ * ν) (unitsPowCM p k) = μ (unitsPowCM p k) * ν (unitsPowCM p k) := by
  rw [units_mul_apply]
  have hfn : innerInt p ν ((unitsPowCM p k).comp (unitsMulCM₂ p))
      = ν (unitsPowCM p k) • unitsPowCM p k := by
    ext x
    rw [innerInt_apply]
    have hcurry : ((unitsPowCM p k).comp (unitsMulCM₂ p)).curry x
        = ((x : ℤ_[p]) ^ k) • unitsPowCM p k := by
      ext y
      change ((x * y : ℤ_[p]ˣ) : ℤ_[p]) ^ k = _
      simp only [Units.val_mul, mul_pow, ContinuousMap.smul_apply, unitsPowCM,
        ContinuousMap.coe_mk, smul_eq_mul]
    rw [hcurry, map_smul, smul_eq_mul]
    change ((x : ℤ_[p])) ^ k * ν (unitsPowCM p k)
        = (ν (unitsPowCM p k) • unitsPowCM p k) x
    simp only [ContinuousMap.smul_apply, unitsPowCM, ContinuousMap.coe_mk, smul_eq_mul]
    rw [mul_comm]
  rw [hfn, map_smul, smul_eq_mul, mul_comm]

/-- **RJW Lem. 3.36(ii)**: a measure on `ℤ_p^×` with `∫ x^k dμ ≠ 0` for all `k > 0`
is not a zero divisor. Source proof (TeX lines 1232–1234): `∫ (xy)^k d(μ⋆λ) =
(∫ x^k dμ)(∫ y^k dλ)`, then apply (i). -/
theorem mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero (μ : PadicMeasure p ℤ_[p]ˣ)
    (h : ∀ k, 0 < k → μ (unitsPowCM p k) ≠ 0) :
    μ ∈ nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ) := by
  rw [mem_nonZeroDivisors_iff]
  have key : ∀ ν, ν * μ = 0 → ν = 0 := by
    intro ν hν
    apply eq_zero_of_forall_unitsPowCM_eq_zero
    intro k hk
    have heval := LinearMap.congr_fun hν (unitsPowCM p k)
    rw [units_mul_apply_unitsPowCM, LinearMap.zero_apply] at heval
    exact (mul_eq_zero.1 heval).resolve_right (h k hk)
  exact ⟨fun ν hν => key ν (by rwa [mul_comm] at hν), key⟩

end zeroDivisor

/-- `[a]−[1]` is a non-zero-divisor when `a` has no torsion moments: its `k`-th moment
is `a^k − 1 ≠ 0`. Source: RJW TeX line 1240. -/
theorem dirac_sub_one_mem_nonZeroDivisors {a : ℤ_[p]ˣ}
    (ha : ∀ k, 0 < k → (a : ℤ_[p]) ^ k ≠ 1) :
    (dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ) ∈
      nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ) := by
  refine mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero p _ fun k hk => ?_
  have heval : (dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ) (unitsPowCM p k)
      = (a : ℤ_[p]) ^ k - 1 := by
    rw [LinearMap.sub_apply, dirac_apply, units_one_def, dirac_apply]
    simp only [unitsPowCM, ContinuousMap.coe_mk, Units.val_one, one_pow]
  rw [heval, sub_ne_zero]
  exact ha k hk

section pseudoMeasure

/-- The total ring of fractions `Q(ℤ_p^×)` of the Iwasawa algebra `Λ(ℤ_p^×)`.
Source: RJW Def. 3.34 ("let `Q(G)` denote the ring of fractions"). -/
noncomputable abbrev QuotientField :=
  FractionRing (PadicMeasure p ℤ_[p]ˣ)

/-- A *pseudo-measure* on `ℤ_p^×`: an element `λ` of `Q(ℤ_p^×)` with
`([g]−[1])·λ ∈ Λ(ℤ_p^×)` for all `g`.

Source: RJW Def. 3.34 (TeX lines 1185–1191). -/
def IsPseudoMeasure (q : QuotientField p) : Prop :=
  ∀ g : ℤ_[p]ˣ, ∃ ν : PadicMeasure p ℤ_[p]ˣ,
    algebraMap _ (QuotientField p) (dirac p g - 1) * q = algebraMap _ _ ν

/-- Measures are pseudo-measures. -/
theorem isPseudoMeasure_algebraMap (μ : PadicMeasure p ℤ_[p]ˣ) :
    IsPseudoMeasure p (algebraMap _ _ μ) := fun g =>
  ⟨(dirac p g - 1) * μ, by rw [map_mul]⟩

/-- **RJW Lem. 3.36(iii)**: a pseudo-measure all of whose moments `∫ x^k` (`k > 0`)
vanish is zero. The moments of a pseudo-measure `q` are encoded via any `g` with
`g^k ≠ 1`: `∫x^k q := (g^k − 1)^{-1} ∫x^k (([g]−[1])q)`. Here we state it via the
witnessing measures directly. Source: TeX lines 1236–1240. -/
theorem pseudoMeasure_eq_zero_of_moments {a : ℤ_[p]ˣ}
    (ha : ∀ k, 0 < k → (a : ℤ_[p]) ^ k ≠ 1) (q : QuotientField p)
    (hq : IsPseudoMeasure p q)
    (h : ∀ (k : ℕ), 0 < k → ∀ ν : PadicMeasure p ℤ_[p]ˣ,
      algebraMap _ (QuotientField p) (dirac p a - 1) * q = algebraMap _ _ ν →
        ν (unitsPowCM p k) = 0) :
    q = 0 := by
  obtain ⟨ν₀, hν₀⟩ := hq a
  have hzero : ν₀ = 0 :=
    eq_zero_of_forall_unitsPowCM_eq_zero p ν₀ fun k hk => h k hk ν₀ hν₀
  rw [hzero, map_zero] at hν₀
  have hunit : IsUnit (algebraMap _ (QuotientField p) (dirac p a - 1)) :=
    IsLocalization.map_units (QuotientField p)
      ⟨_, dirac_sub_one_mem_nonZeroDivisors p ha⟩
  rcases hunit with ⟨u, hu⟩
  calc q = ↑u⁻¹ * (↑u * q) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = ↑u⁻¹ * 0 := by rw [hu, hν₀]
    _ = 0 := mul_zero _

end pseudoMeasure

section augmentation

/-- For odd `p` there is a *topological generator* of `ℤ_p^×`: an `a` whose image
generates `(ℤ/p^n)^×` for every `n`. The hypothesis `p ≠ 2` is essential:
`(ZMod 8)ˣ` is not cyclic. Proof: the per-level generator sets are nonempty nested
clopen subsets of the compact `ℤ_[p]ˣ`; pick a point of the intersection.
Source: RJW Lem. 3.38 (the proof opens "As p is odd"). -/
theorem exists_topological_generator (hp2 : p ≠ 2) :
    ∃ a : ℤ_[p]ˣ, ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤ := by
  classical
  -- the nested sequence of (clopen, nonempty) generator sets
  set t : ℕ → Set ℤ_[p]ˣ :=
    fun n => {a : ℤ_[p]ˣ | Subgroup.zpowers (unitsToZModPow p n a) = ⊤} with ht
  have hsub : ∀ n, t (n + 1) ⊆ t n := by
    intro n a hagen
    change Subgroup.zpowers (unitsToZModPow p n a) = ⊤
    rw [unitsToZModPow_le p n.le_succ a, ← MonoidHom.map_zpowers, hagen]
    exact Subgroup.map_top_of_surjective _
      (ZMod.unitsMap_surjective (pow_dvd_pow p n.le_succ))
  have hne : ∀ n, (t n).Nonempty := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨1, ?_⟩
      change Subgroup.zpowers (unitsToZModPow p 0 1) = ⊤
      haveI : Subsingleton (ZMod (p ^ 0))ˣ := by rw [pow_zero]; infer_instance
      exact Subsingleton.elim _ _
    · haveI := Fact.mk hp.out
      haveI := ZMod.isCyclic_units_of_prime_pow p hp.out hp2 n
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod (p ^ n))ˣ)
      obtain ⟨a, rfl⟩ := unitsToZModPow_surjective p n hn g
      exact ⟨a, (Subgroup.eq_top_iff' _).2 hg⟩
  have hclosed : ∀ n, IsClosed (t n) := by
    intro n
    have hset : t n = ⋃ g ∈ {g : (ZMod (p ^ n))ˣ | Subgroup.zpowers g = ⊤},
        unitsToZModPow p n ⁻¹' {g} := by
      ext a
      simp only [ht, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage,
        Set.mem_singleton_iff, exists_prop]
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨g, hg, hag⟩ => hag ▸ hg⟩
    rw [hset]
    exact (Set.toFinite _).isClosed_biUnion
      fun g _ => (isClopen_unitsToZModPow_fiber p n g).isClosed
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    t hsub hne ((hclosed 0).isCompact) hclosed
  exact ⟨a, fun n => Set.mem_iInter.1 ha n⟩

/-- For a topological generator `a`, the augmentation ideal is principal, generated by
`[a] − [1]`: at each finite level the augmentation ideal of the (cyclic) group ring
`ℤ_p[(ℤ/p^n)^×]` is generated by `[ā]−[1]`; compatibility and a compactness argument
pass this to the limit. Source: RJW Lem. 3.38, proof (TeX lines 1264–1282). -/
theorem augmentationIdeal_eq_span {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤) :
    augmentationIdeal p = Ideal.span {(dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ)} := by
  classical
  apply le_antisymm
  · -- ker deg ⊆ ([a]−1): produce the quotient by a compactness argument in the weak
    -- topology of pointwise convergence on functionals
    intro μ hμ
    rw [augmentationIdeal, RingHom.mem_ker] at hμ
    rw [Ideal.mem_span_singleton]
    set K : Set (C(ℤ_[p]ˣ, ℤ_[p]) → ℤ_[p]) :=
      (⋂ (f : C(ℤ_[p]ˣ, ℤ_[p])) (g : C(ℤ_[p]ˣ, ℤ_[p])),
        {φ | φ (f + g) = φ f + φ g}) ∩
      ⋂ (c : ℤ_[p]) (f : C(ℤ_[p]ˣ, ℤ_[p])), {φ | φ (c • f) = c * φ f} with hK
    set S : ℕ → Set (C(ℤ_[p]ˣ, ℤ_[p]) → ℤ_[p]) := fun n =>
      K ∩ ⋂ g : (ZMod (p ^ n))ˣ,
        {φ | φ (((levelChar p n g).comp (unitsMulCM₂ p)).curry a)
          - φ (((levelChar p n g).comp (unitsMulCM₂ p)).curry 1)
          - μ (levelChar p n g) = 0} with hS
    have hKclosed : IsClosed K := by
      refine IsClosed.inter (isClosed_iInter fun f => isClosed_iInter fun g => ?_)
        (isClosed_iInter fun c => isClosed_iInter fun f => ?_)
      · exact isClosed_eq (continuous_apply (f + g))
          ((continuous_apply f).add (continuous_apply g))
      · exact isClosed_eq (continuous_apply (c • f))
          (continuous_const.mul (continuous_apply f))
    have hSclosed : ∀ n, IsClosed (S n) := fun n =>
      hKclosed.inter (isClosed_iInter fun g =>
        isClosed_eq
          (((continuous_apply (((levelChar p n g).comp (unitsMulCM₂ p)).curry a)).sub
            (continuous_apply (((levelChar p n g).comp (unitsMulCM₂ p)).curry 1))).sub
            continuous_const)
          continuous_const)
    have hpack : ∀ φ ∈ K, ∃ ν : PadicMeasure p ℤ_[p]ˣ, ⇑ν = φ := by
      intro φ hφ
      rw [hK] at hφ
      obtain ⟨h1, h2⟩ := hφ
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at h1 h2
      exact ⟨IsLinearMap.mk' φ ⟨h1, fun c x => by rw [h2 c x, smul_eq_mul]⟩, rfl⟩
    have hSmem : ∀ (n : ℕ) (ν : PadicMeasure p ℤ_[p]ˣ),
        ⇑ν ∈ S n ↔ levelMap p n ((dirac p a - 1) * ν - μ) = 0 := by
      intro n ν
      rw [hS]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨-, hcond⟩
        rw [levelMap_eq_zero_iff]
        intro g
        rw [LinearMap.sub_apply, dirac_sub_one_mul_apply]
        exact hcond g
      · intro h
        refine ⟨⟨?_, ?_⟩, fun g => ?_⟩
        · simp only [Set.mem_iInter, Set.mem_setOf_eq]
          exact fun f g => map_add ν f g
        · simp only [Set.mem_iInter, Set.mem_setOf_eq]
          exact fun c f => by rw [map_smul, smul_eq_mul]
        · rw [levelMap_eq_zero_iff] at h
          have hg := h g
          rw [LinearMap.sub_apply, dirac_sub_one_mul_apply] at hg
          exact hg
    have hSsub : ∀ n, S (n + 1) ⊆ S n := by
      intro n φ hφ
      obtain ⟨ν, rfl⟩ := hpack φ hφ.1
      rw [hSmem] at hφ ⊢
      rw [← mapDomain_levelMap p n.le_succ, hφ]
      exact Finsupp.mapDomain_zero
    have hSne : ∀ n, (S n).Nonempty := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · refine ⟨⇑(0 : PadicMeasure p ℤ_[p]ˣ), ?_⟩
        rw [hSmem, levelMap_eq_zero_iff]
        intro g
        rw [LinearMap.sub_apply, mul_zero, LinearMap.zero_apply, zero_sub, neg_eq_zero]
        have hg1 : levelChar p 0 g = (1 : C(ℤ_[p]ˣ, ℤ_[p])) := by
          haveI : Subsingleton (ZMod (p ^ 0))ˣ := by rw [pow_zero]; infer_instance
          rw [← sum_levelChar p 0, Fintype.sum_subsingleton _ g]
        rw [hg1]
        exact hμ
      · have hmem : levelMap p n μ ∈ Ideal.span
            {(MonoidAlgebra.single (unitsToZModPow p n a) 1 - 1 :
              MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ)} :=
          mem_span_of_sum_eq_zero p (ha n) _ (by rw [sum_levelMap_coeff]; exact hμ)
        obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hmem
        set ν : PadicMeasure p ℤ_[p]ˣ :=
          ∑ c : (ZMod (p ^ n))ˣ,
            y c • dirac p ((unitsToZModPow_surjective p n hn c).choose) with hν
        refine ⟨⇑ν, ?_⟩
        have hlev : levelMap p n ν = y := by
          rw [hν, map_sum]
          simp_rw [levelMap_smul, levelMap_dirac,
            (unitsToZModPow_surjective p n hn _).choose_spec]
          calc (∑ c : (ZMod (p ^ n))ˣ, y c • MonoidAlgebra.single c (1 : ℤ_[p]))
              = ∑ c : (ZMod (p ^ n))ˣ, MonoidAlgebra.single c (y c) := by
                refine Finset.sum_congr rfl fun c _ => ?_
                rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
            _ = y := sum_single_coeff p y
        rw [hSmem, map_sub, map_mul, map_sub, levelMap_dirac, map_one, hlev, ← hy,
          sub_self]
    obtain ⟨φ, hφ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S hSsub hSne ((hSclosed 0).isCompact) hSclosed
    have hφall := Set.mem_iInter.1 hφ
    obtain ⟨ν, rfl⟩ := hpack φ (hφall 0).1
    refine ⟨ν, ?_⟩
    have hzero : (dirac p a - 1) * ν - μ = 0 := by
      apply levelMap_jointly_injective
      intro n
      rw [← hSmem]
      exact hφall n
    exact (sub_eq_zero.1 hzero).symm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change (dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ) ∈ augmentationIdeal p
    rw [augmentationIdeal, RingHom.mem_ker, map_sub, map_one,
      show deg p (dirac p a) = 1 from rfl, sub_self]

/-- **RJW Lem. 3.38 (`lem:pseudo-measure existence`)**: for a topological generator `a`
and any measure `μ`, the quotient `μ/([a]−[1])` is a pseudo-measure. -/
theorem isPseudoMeasure_mk' {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤)
    (hreg : (dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ) ∈
      nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ))
    (μ : PadicMeasure p ℤ_[p]ˣ) :
    IsPseudoMeasure p
      (IsLocalization.mk' (QuotientField p) μ ⟨_, hreg⟩) := by
  intro g
  have hgmem : (dirac p g - 1 : PadicMeasure p ℤ_[p]ˣ) ∈ augmentationIdeal p := by
    rw [augmentationIdeal, RingHom.mem_ker, map_sub, map_one,
      show deg p (dirac p g) = 1 from rfl, sub_self]
  rw [augmentationIdeal_eq_span p ha, Ideal.mem_span_singleton] at hgmem
  obtain ⟨ν, hν⟩ := hgmem
  refine ⟨ν * μ, ?_⟩
  rw [hν, show algebraMap _ (QuotientField p) ((dirac p a - 1) * ν)
      = algebraMap _ _ ν * algebraMap _ _ (dirac p a - 1) from by rw [map_mul, mul_comm],
    mul_assoc, map_mul]
  congr 1
  exact IsLocalization.mk'_spec' (QuotientField p) μ ⟨_, hreg⟩

/-- `[a]−[1]` is a non-zero-divisor for a topological generator `a` (its moments are
`a^k − 1 ≠ 0`). Source: RJW TeX line 1240 ("But `[a]−[1]` satisfies the condition of
part (ii)") together with the remark after Lem. 3.38. -/
theorem dirac_sub_one_mem_nonZeroDivisors' {a : ℤ_[p]ˣ}
    (ha : ∀ k, 0 < k → (a : ℤ_[p]) ^ k ≠ 1) :
    (dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ) ∈
      nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ) :=
  dirac_sub_one_mem_nonZeroDivisors p ha

/-- Every pseudo-measure has the shape `μ/([a]−[1])`. Source: RJW TeX lines 1284–1285
("Note moreover that *all* pseudo-measures have this shape"). -/
theorem isPseudoMeasure_iff_exists {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤)
    (hreg : (dirac p a - 1 : PadicMeasure p ℤ_[p]ˣ) ∈
      nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ))
    (q : QuotientField p) :
    IsPseudoMeasure p q ↔
      ∃ μ : PadicMeasure p ℤ_[p]ˣ,
        q = IsLocalization.mk' (QuotientField p) μ ⟨_, hreg⟩ := by
  constructor
  · intro hq
    obtain ⟨ν, hν⟩ := hq a
    refine ⟨ν, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    rw [mul_comm] at hν
    exact hν
  · rintro ⟨μ, rfl⟩
    exact isPseudoMeasure_mk' p ha hreg μ

end augmentation

end PadicMeasure
