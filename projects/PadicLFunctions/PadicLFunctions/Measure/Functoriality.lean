import PadicLFunctions.Measure.PseudoMeasure
import PadicLFunctions.Measure.Convolution

/-!
# Functoriality of the convolution measure algebra  (S13-G, CARRIER-BRIDGE step 1)

The measure algebra `PadicMeasure p G = ℳ(G, ℤ_p)` of a compact commutative topological monoid is
*contravariantly functorial in continuous functions* (`pushforward`, `Measure/Basic.lean`) and that
pushforward is a **ring homomorphism** when the underlying map is a (continuous) monoid hom — the
convolution `∫ f d(μ⋆ν) = ∫∫ f(xy) dμ dν` is transported correctly precisely because `m(xy) =
m(x)·m(y)`.  This generalises `projPlus` (`Iwasawa/PlusPart.lean`, the pushforward along the quotient
`ℤ_p^× → 𝒢⁺`) to an arbitrary continuous monoid hom, and upgrades a continuous monoid *isomorphism*
to a ring isomorphism of measure algebras.

This is the transport tool of the carrier bridge `PadicMeasure(𝒢⁺) ≅ IwasawaAlgebraGroup` (it carries
`PadicMeasure(𝒢⁺)` along a group isomorphism `𝒢⁺ ≅ Δ × Γ`).

## Main declarations

* `PadicMeasure.pushforwardRingHom`: a continuous monoid hom `m : G → G'` (as the data of a
  continuous map plus the monoid-hom equations) induces `PadicMeasure p G →+* PadicMeasure p G'`.
* `PadicMeasure.pushforwardRingEquiv`: a continuous monoid *iso* induces `PadicMeasure p G ≃+*
  PadicMeasure p G'`.
-/

noncomputable section

namespace PadicMeasure

variable (p : ℕ) [hp : Fact p.Prime]
variable {G G' : Type*}
  [TopologicalSpace G] [CommMonoid G] [ContinuousMul G] [CompactSpace G]
  [TopologicalSpace G'] [CommMonoid G'] [ContinuousMul G'] [CompactSpace G']

/-- The pushforward of measures along a **continuous monoid homomorphism** `m : G → G'` is a ring
homomorphism `PadicMeasure p G →+* PadicMeasure p G'`.  (Linearity and `0`/`+` are inherited from
`pushforward`; `map_one`/`map_mul` use `m 1 = 1` and `m (x*y) = m x * m y`.) -/
def pushforwardRingHom (m : C(G, G')) (hmul : ∀ x y, m (x * y) = m x * m y) (hone : m 1 = 1) :
    PadicMeasure p G →+* PadicMeasure p G' where
  toFun := pushforward p m
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := by
    rw [conv_one_def, pushforward_dirac, hone, ← conv_one_def]
  map_mul' μ ν := by
    refine LinearMap.ext fun f => ?_
    rw [pushforward_apply, conv_mul_apply, conv_mul_apply, pushforward_apply]
    congr 1
    refine ContinuousMap.ext fun x => ?_
    rw [innerInt_apply, ContinuousMap.comp_apply, innerInt_apply, pushforward_apply]
    congr 1
    refine ContinuousMap.ext fun y => ?_
    simp only [ContinuousMap.curry_apply, ContinuousMap.comp_apply, mulCM₂,
      ContinuousMap.coe_mk]
    rw [hmul x y]

@[simp]
lemma pushforwardRingHom_apply (m : C(G, G')) (hmul : ∀ x y, m (x * y) = m x * m y) (hone : m 1 = 1)
    (μ : PadicMeasure p G) (f : C(G', ℤ_[p])) :
    pushforwardRingHom p m hmul hone μ f = μ (f.comp m) := rfl

/-- A **continuous monoid isomorphism** `e : G ≃ G'` (given as continuous maps `toFun`, `invFun` that
are mutually inverse and a monoid hom) induces a ring isomorphism of measure algebras
`PadicMeasure p G ≃+* PadicMeasure p G'`. -/
def pushforwardRingEquiv (e : C(G, G')) (e' : C(G', G))
    (hmul : ∀ x y, e (x * y) = e x * e y) (hone : e 1 = 1)
    (hleft : ∀ x, e' (e x) = x) (hright : ∀ y, e (e' y) = y) :
    PadicMeasure p G ≃+* PadicMeasure p G' where
  __ := pushforwardRingHom p e hmul hone
  invFun := pushforward p e'
  left_inv μ := by
    refine LinearMap.ext fun f => ?_
    show pushforward p e' (pushforward p e μ) f = μ f
    rw [pushforward_apply, pushforward_apply]
    congr 1
    exact ContinuousMap.ext fun x => by rw [ContinuousMap.comp_assoc]; simp [hleft]
  right_inv ν := by
    refine LinearMap.ext fun f => ?_
    show pushforward p e (pushforward p e' ν) f = ν f
    rw [pushforward_apply, pushforward_apply]
    congr 1
    exact ContinuousMap.ext fun y => by rw [ContinuousMap.comp_assoc]; simp [hright]

@[simp]
lemma pushforwardRingEquiv_apply (e : C(G, G')) (e' : C(G', G))
    (hmul : ∀ x y, e (x * y) = e x * e y) (hone : e 1 = 1)
    (hleft : ∀ x, e' (e x) = x) (hright : ∀ y, e (e' y) = y)
    (μ : PadicMeasure p G) (f : C(G', ℤ_[p])) :
    pushforwardRingEquiv p e e' hmul hone hleft hright μ f = μ (f.comp e) := rfl

/-! ## Pushforward into the additive (Mahler) algebra `Λ(ℤ_p) = ℤ_p⟦T⟧`

The Iwasawa algebra of the additive group is `PadicMeasure p ℤ_[p]` with the **Mahler** ring
structure (`Measure/Convolution.lean`, `δ_a·δ_b = δ_{a+b}`, `1 = δ_0`).  A continuous map
`m : G → ℤ_p` from a multiplicative group that turns multiplication into addition (`m(xy) = mx + my`,
`m 1 = 0`) pushes measures forward to a **ring homomorphism** `PadicMeasure p G →+* PadicMeasure p ℤ_[p]`.
For `G = Γ` the pro-cyclic 1-units and `m = log`, this is the `Γ`-factor of the carrier bridge. -/

/-- Pushforward along a continuous `mul→add` homomorphism `m : G → ℤ_p`, valued in the **Mahler**
(additive) convolution algebra `PadicMeasure p ℤ_[p]`.  Ring hom because `m(xy) = mx + my` matches
the additive convolution (`mul_apply`/`convInner`). -/
def mahlerPushforwardRingHom {G : Type*} [TopologicalSpace G] [CommMonoid G] [ContinuousMul G]
    [CompactSpace G] (m : C(G, ℤ_[p])) (hmul : ∀ x y, m (x * y) = m x + m y) (hone : m 1 = 0) :
    PadicMeasure p G →+* PadicMeasure p ℤ_[p] where
  toFun := pushforward p m
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := by
    rw [conv_one_def, pushforward_dirac, hone, one_def]
  map_mul' μ ν := by
    refine LinearMap.ext fun f => ?_
    rw [pushforward_apply, conv_mul_apply, mul_apply, pushforward_apply]
    congr 1
    refine ContinuousMap.ext fun x => ?_
    simp only [innerInt_apply, convInner, ContinuousMap.comp_apply, pushforward_apply,
      ContinuousMap.coe_mk]
    congr 1
    refine ContinuousMap.ext fun y => ?_
    simp only [ContinuousMap.curry_apply, ContinuousMap.comp_apply, mulCM₂, ContinuousMap.coe_mk]
    rw [hmul x y]

@[simp]
lemma mahlerPushforwardRingHom_apply {G : Type*} [TopologicalSpace G] [CommMonoid G]
    [ContinuousMul G] [CompactSpace G] (m : C(G, ℤ_[p])) (hmul : ∀ x y, m (x * y) = m x + m y)
    (hone : m 1 = 0) (μ : PadicMeasure p G) (f : C(ℤ_[p], ℤ_[p])) :
    mahlerPushforwardRingHom p m hmul hone μ f = μ (f.comp m) := rfl

end PadicMeasure
