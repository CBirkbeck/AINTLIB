# Inventory: ./HasseWeil/Pic0/PicDual.lean

**File purpose:** Builds the Pic⁰ dual isogeny `φ̂ = κ⁻¹ ∘ φ* ∘ κ` (Silverman III.6.1) and proves the dual relation `α ∘ α̂ = [deg α]` together with related uniqueness / additivity results for use in the Route-C Hasse bound.

**Imports:** `HasseWeil.Pic0.IsogenyClassGroup`, `HasseWeil.Pic0.ToClassSurjective`, `HasseWeil.Basic`

---

## Declaration Inventory

---

### `noncomputable def classTransport`
- **Type:** `(m : ClassGroup E.CoordinateRing →* ClassGroup E.CoordinateRing) → E.Point →+ E.Point`
- **What:** Conjugates a monoid endomorphism `m` of `ClassGroup R` by the κ-isomorphism `E.Point.toClassEquiv'` to obtain a point-group endomorphism `κ⁻¹ ∘ m ∘ κ`.
- **How:** Assembles `AddMonoidHom` compositions directly using `toClassEquiv'.toAddMonoidHom`, `symm.toAddMonoidHom`, and the `Additive` wrapping via `AddMonoidHom.mk'`.
- **Hypotheses:** `E` is an elliptic curve over a field with `DecidableEq`.
- **Uses from project:** `WeierstrassCurve.Affine.Point.toClassEquiv'`
- **Used by:** `picDual`, `picPushforward`, `classTransport_apply`, `classTransport_comp_eq`, `picDual_comp_toAddMonoidHom`
- **Visibility:** public
- **Lines:** 88–94 (body ≈ 6 lines)
- **Notes:** None.

---

### `theorem classTransport_apply`
- **Type:** `classTransport m P = (toClassEquiv').symm (Additive.ofMul (m (toClassEquiv' P).toMul))`
- **What:** Simp lemma unfolding `classTransport` pointwise, confirming it is literally `κ⁻¹(m(κ P))`.
- **How:** Proof is `rfl`.
- **Hypotheses:** Same as `classTransport`.
- **Uses from project:** `classTransport`
- **Used by:** `classTransport_comp_eq`
- **Visibility:** public (`@[simp]`)
- **Lines:** 97–102 (proof 1 line)
- **Notes:** None.

---

### `noncomputable def picDual`
- **Type:** `(ch : α.CoordHom) (hinj : Injective ch.toAlgHom) (hfin : Module.Finite R R) → E.Point →+ E.Point`
- **What:** Defines the Pic⁰ dual `α̂ = κ⁻¹ ∘ classMap ∘ κ` as a point endomorphism (Silverman III.6.1(b)), where `classMap` is the ideal extension (divisor pullback `φ*`).
- **How:** One-liner `classTransport (α.classMap ch hinj hfin)`.
- **Hypotheses:** `CoordHom` witness `ch`, injectivity `hinj`, module finiteness `hfin`.
- **Uses from project:** `classTransport`, `Isogeny.classMap`
- **Used by:** `picDual_apply`, `picPushforward_comp_picDual`, `toAddMonoidHom_comp_picDual` (and many downstream theorems)
- **Visibility:** public
- **Lines:** 113–116 (body 1 line)
- **Notes:** Central definition of the file; the `CoordHom` requirements are the main carried hypothesis.

---

### `theorem picDual_apply`
- **Type:** Simp lemma unfolding `α.picDual ch hinj hfin P = (toClassEquiv').symm (ofMul (classMap (toClassEquiv' P).toMul))`
- **What:** Pointwise unfolding of `picDual`, confirming it is `κ⁻¹(φ*(κ P))`.
- **How:** Proof is `rfl`.
- **Hypotheses:** Same as `picDual`.
- **Uses from project:** `picDual`
- **Used by:** Not referenced by any other declaration in this file.
- **Visibility:** public (`@[simp]`)
- **Lines:** 119–125 (proof 1 line)
- **Notes:** Potential dead-code within this file (no intra-file callers found).

---

### `noncomputable def picPushforward`
- **Type:** `(ch : α.CoordHom) (hinj : Injective ch.toAlgHom) (hfin : Module.Finite R R) → E.Point →+ E.Point`
- **What:** The κ-transport of the divisor pushforward `φ_* = classNorm`: `κ⁻¹ ∘ classNorm ∘ κ`.
- **How:** One-liner `classTransport (α.classNorm ch hinj hfin)`.
- **Hypotheses:** Same as `picDual`.
- **Uses from project:** `classTransport`, `Isogeny.classNorm`
- **Used by:** `picPushforward_apply`, `picPushforward_comp_picDual`, `toAddMonoidHom_eq_picPushforward_iff` (and downstream)
- **Visibility:** public
- **Lines:** 136–139 (body 1 line)
- **Notes:** Not the actual point map `toAddMonoidHom`; they are identified via III.3.4 naturality (`hnat`).

---

### `theorem picPushforward_apply`
- **Type:** Simp lemma unfolding `α.picPushforward ch hinj hfin P = (toClassEquiv').symm (ofMul (classNorm (toClassEquiv' P).toMul))`
- **What:** Pointwise unfolding of `picPushforward`.
- **How:** Proof is `rfl`.
- **Hypotheses:** Same as `picPushforward`.
- **Uses from project:** `picPushforward`
- **Used by:** `toAddMonoidHom_eq_picPushforward_iff`
- **Visibility:** public (`@[simp]`)
- **Lines:** 142–148 (proof 1 line)
- **Notes:** None.

---

### `theorem classTransport_comp_eq`
- **Type:** Given `m₁ m₂ : ClassGroup R →* ClassGroup R` with `hcomp : ∀ c, m₂(m₁ c) = c^n`, proves `(classTransport m₂).comp (classTransport m₁) = (mulByInt E n).toAddMonoidHom`
- **What:** The key composition engine: two κ-transports compose to `[n]` whenever their class-group composite is `c ↦ c^n`. The inner `κ ∘ κ⁻¹` cancels and the class-group power becomes `n`-fold point sum.
- **How:** Uses `classTransport_apply` twice, then `apply_symm_apply` to cancel `κ ∘ κ⁻¹`, and `map_nsmul` + `symm_apply_apply` + `natCast_zsmul` to convert class-group power to point `n`-fold sum.
- **Hypotheses:** The composition hypothesis `hcomp` — no additional geometry required.
- **Uses from project:** `classTransport`, `classTransport_apply`, `mulByInt_apply`, `natCast_zsmul`
- **Used by:** `picPushforward_comp_picDual`, `picDual_comp_toAddMonoidHom`
- **Visibility:** public
- **Lines:** 157–180 (proof 24 lines)
- **Notes:** None.

---

### `theorem picPushforward_comp_picDual`
- **Type:** `(α.picPushforward …).comp (α.picDual …) = (mulByInt E (finrank R R)).toAddMonoidHom`
- **What:** κ-transport of Silverman II.3.6(e) `φ_* ∘ φ* = [deg]` as point endomorphisms (finrank form); unconditional modulo the carried `CoordHom`/`Module.Finite` witnesses.
- **How:** Immediately applies `classTransport_comp_eq` with the shipped `classNorm_comp_classMap` as the `hcomp` witness.
- **Hypotheses:** `ch`, `hinj`, `hfin`.
- **Uses from project:** `classTransport_comp_eq`, `Isogeny.classNorm_comp_classMap`
- **Used by:** `picPushforward_comp_picDual_degree`, `toAddMonoidHom_comp_picDual`
- **Visibility:** public
- **Lines:** 199–208 (proof ≈ 2 lines)
- **Notes:** None.

---

### `theorem picPushforward_comp_picDual_degree`
- **Type:** `(α.picPushforward …).comp (α.picDual …) = (mulByInt E (α.degree : ℤ)).toAddMonoidHom`
- **What:** The `α.degree` form of `picPushforward_comp_picDual`, replacing `finrank` by the function-field degree via the tower bridge.
- **How:** Rewrites via `picPushforward_comp_picDual`, then uses `exact_mod_cast` with `degree_eq_finrank_coordinateRing_of_tower_eq` to match exponents.
- **Hypotheses:** `ch`, `hinj`, `hfin`, plus fraction-field tower witnesses `S, S'` with `IsFractionRing`, `IsScalarTower`, `finrank` equalities.
- **Uses from project:** `picPushforward_comp_picDual`, `Isogeny.degree_eq_finrank_coordinateRing_of_tower_eq`
- **Used by:** `toAddMonoidHom_comp_picDual_degree`
- **Visibility:** public
- **Lines:** 216–232 (proof ≈ 4 lines)
- **Notes:** None.

---

### `def Naturality`
- **Type:** `(α : Isogeny E E) (ch …) : Prop` — `∀ P, toClassEquiv' (α.toAddMonoidHom P) = ofMul (classNorm (toClassEquiv' P).toMul)`
- **What:** The III.3.4 naturality predicate: under κ the actual point map `α.toAddMonoidHom` corresponds to the class-group norm `classNorm` (i.e., `κ ∘ α = φ_* ∘ κ`). Carried as a hypothesis; not derivable unconditionally.
- **How:** Pure `Prop` definition — no proof.
- **Hypotheses:** None (it is the statement to be assumed per-isogeny).
- **Uses from project:** None (references `α.classNorm` in the RHS).
- **Used by:** `toAddMonoidHom_eq_picPushforward_iff`, `Naturality_of_toClassEquiv'_some_eq_relNorm0`, `Naturality_of_toClassEquiv'_some_eq_comap`, `naturality_of_coordHom`, `toAddMonoidHom_comp_picDual`, `toAddMonoidHom_comp_picDual_degree`, `picDual_comp_toAddMonoidHom_of_surjective`, and many others.
- **Visibility:** public
- **Lines:** 252–257 (definition, no proof body)
- **Notes:** This is the central carried hypothesis of the whole file; used by ≥ 10 declarations.

---

### `theorem toAddMonoidHom_eq_picPushforward_iff`
- **Type:** `α.toAddMonoidHom = α.picPushforward … ↔ α.Naturality …`
- **What:** The κ-conjugate reformulation: the actual point map equals `picPushforward` iff the naturality predicate holds.
- **How:** Forward uses `picPushforward_apply` + `apply_symm_apply`; backward uses `picPushforward_apply` + `symm_apply_apply`.
- **Hypotheses:** `ch`, `hinj`, `hfin`.
- **Uses from project:** `Naturality`, `picPushforward_apply`
- **Used by:** `toAddMonoidHom_comp_picDual`, `toAddMonoidHom_comp_picDual_degree`, `picDual_comp_toAddMonoidHom`
- **Visibility:** public
- **Lines:** 262–273 (proof ≈ 8 lines)
- **Notes:** Used by 3 downstream theorems.

---

### `theorem classNorm_toClassEquiv'_some`
- **Type:** For `P = Point.some x y h` (affine rational point) and `hmem` (XYIdeal ∈ (Ideal R)⁰), the value `(α.classNorm …)(toClassEquiv' (Point.some x y h)).toMul = ClassGroup.mk0 (relNorm0 ⟨XYIdeal, hmem⟩)`
- **What:** Evaluates the `classNorm ∘ κ` side of `Naturality` at a rational point: the result is the `mk0` class of the relative norm of the maximal ideal at `P`.
- **How:** Rewrites via `toClassEquiv'_apply`, `toClass_some`, `mk0_eq_mk_XYIdeal'`, then uses `ClassGroup.relNorm_mk0` to compute the norm on the integral representative.
- **Hypotheses:** `ch`, `hinj`, `hfin`; nonsingularity `h`; `hmem` (XYIdeal is a nonzero divisor).
- **Uses from project:** `WeierstrassCurve.Affine.Point.toClassEquiv'_apply`, `toClass_some`, `mk0_eq_mk_XYIdeal'`, `HasseWeil.ClassGroup.relNorm_mk0`
- **Used by:** `Naturality_of_toClassEquiv'_some_eq_relNorm0`, `Naturality_of_toClassEquiv'_some_eq_comap`
- **Visibility:** public
- **Lines:** 312–332 (proof ≈ 10 lines)
- **Notes:** None.

---

### `theorem comap_XYIdeal_mem_nonZeroDivisors`
- **Type:** Given `hmem : XYIdeal E x (C y) ∈ (Ideal R)⁰`, proves `Ideal.comap ch.toAlgHom.toRingHom (XYIdeal E x (C y)) ∈ (Ideal R)⁰`
- **What:** The contraction of the maximal ideal along `ch` is nonzero; needed as a side condition for the `mk0` class of the comap ideal.
- **How:** Uses `Algebra.IsIntegral.of_finite` (from `hfin`) to establish integrality, then `Ideal.under_ne_bot` to conclude the contraction of a nonzero prime is nonzero.
- **Hypotheses:** `ch`, `hfin`, and `hmem`.
- **Uses from project:** None from this file; uses `Ideal.under_ne_bot`.
- **Used by:** `Naturality_of_toClassEquiv'_some_eq_comap` (to supply `hcomap`)
- **Visibility:** public
- **Lines:** 355–370 (proof ≈ 9 lines)
- **Notes:** None.

---

### `theorem mk0_relNorm0_XYIdeal_eq_mk0_comap`
- **Type:** Under `ch`, `hinj`, `hfin`, `h`, `hmem`, `hcomap`: `ClassGroup.mk0 (relNorm0 ⟨XYIdeal,hmem⟩) = ClassGroup.mk0 ⟨comap ch (XYIdeal), hcomap⟩`
- **What:** At a rational point, the relative norm class of the maximal ideal equals the contraction class (`relNorm = comap` at residue degree `f = 1`), without any `PerfectField` hypothesis.
- **How:** Establishes maximality of `XYIdeal` via `quotientXYIdealEquiv`, then proves `inertiaDeg = 1` via `Ideal.inertiaDeg_under_eq_one_of_algHom_of_residueField_finrank_one` + `finrank_quotient_XYIdeal_eq_one`, and concludes via `ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one`.
- **Hypotheses:** `ch`, `hinj`, `hfin`, nonsingularity `h`, `hmem`, `hcomap`.
- **Uses from project:** `WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv`, `WeierstrassCurve.Affine.Point.finrank_quotient_XYIdeal_eq_one`, `Ideal.inertiaDeg_under_eq_one_of_algHom_of_residueField_finrank_one`, `ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one`
- **Used by:** `Naturality_of_toClassEquiv'_some_eq_comap`, `naturality_of_coordHom`
- **Visibility:** public
- **Lines:** 394–426 (proof ≈ 17 lines)
- **Notes:** `set_option maxHeartbeats 1600000` — comment present ("residue-field finrank bookkeeping + twisted R →[α*] R instance chain need extra room"). Proof > 30 lines (lines 394–426 ≈ 33 lines including sig).

---

### `theorem Naturality_of_toClassEquiv'_some_eq_relNorm0`
- **Type:** Given `hpoint : ∀ x y h hmem, toClassEquiv' (α.toAddMonoidHom (some x y h)) = ofMul (mk0 (relNorm0 ⟨XYIdeal,hmem⟩))`, proves `α.Naturality ch hinj hfin`
- **What:** Reduces the full `Naturality` predicate to the per-affine-point condition `κ(αP) = mk0(relNorm0 𝔪_P)` (the `relNorm0` form); the basepoint case is automatic. This is the cleanest `hnat` reduction to a concrete ideal statement.
- **How:** Cases on `P`; basepoint: `map_zero` + `simp`; affine: proves `hmem` via `XClass_ne_zero` containment, then applies `classNorm_toClassEquiv'_some` + the supplied `hpoint`.
- **Hypotheses:** The per-affine-point `hpoint` hypothesis.
- **Uses from project:** `classNorm_toClassEquiv'_some`, `WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero`
- **Used by:** Not referenced by any other declaration in this file (dead-code candidate within file; may be used by other files).
- **Visibility:** public
- **Lines:** 440–472 (proof ≈ 20 lines)
- **Notes:** Not called by any other declaration in this file.

---

### `theorem Naturality_of_toClassEquiv'_some_eq_comap`
- **Type:** Given `hpoint : ∀ x y h hcomap, toClassEquiv' (α.toAddMonoidHom (some x y h)) = ofMul (mk0 ⟨comap ch (XYIdeal), hcomap⟩)`, proves `α.Naturality ch hinj hfin`
- **What:** Reduces `Naturality` to the `comap`-form per-point agreement (Silverman III.3.4 in `comap` form), PerfectField-free, routing through `mk0_relNorm0_XYIdeal_eq_mk0_comap`.
- **How:** Cases on `P`; basepoint automatic; affine: proves `hmem` via `XClass_ne_zero`, invokes `comap_XYIdeal_mem_nonZeroDivisors`, then rewrites via `classNorm_toClassEquiv'_some` + `mk0_relNorm0_XYIdeal_eq_mk0_comap` and applies `hpoint`.
- **Hypotheses:** The per-affine-point `hpoint` in `comap` form.
- **Uses from project:** `classNorm_toClassEquiv'_some`, `mk0_relNorm0_XYIdeal_eq_mk0_comap`, `comap_XYIdeal_mem_nonZeroDivisors`, `XClass_ne_zero`
- **Used by:** `naturality_of_coordHom`
- **Visibility:** public
- **Lines:** 488–523 (proof ≈ 24 lines)
- **Notes:** None.

---

### `theorem naturality_of_coordHom`
- **Type:** Same signature as `Naturality_of_toClassEquiv'_some_eq_comap`; proves `α.Naturality ch hinj hfin`
- **What:** API alias of `Naturality_of_toClassEquiv'_some_eq_comap` under the name consumed by the Route-C assembly. The unconditional `hnat` discharge: from the `comap`-form point agreement, the full naturality holds.
- **How:** Immediately delegates to `Naturality_of_toClassEquiv'_some_eq_comap`.
- **Hypotheses:** Same as `Naturality_of_toClassEquiv'_some_eq_comap`.
- **Uses from project:** `Naturality_of_toClassEquiv'_some_eq_comap`
- **Used by:** Not referenced by any other declaration in this file (intended for external callers).
- **Visibility:** public
- **Lines:** 544–557 (proof 1 line)
- **Notes:** Alias for external Route-C consumption.

---

### `theorem toAddMonoidHom_comp_picDual`
- **Type:** `α.toAddMonoidHom.comp (α.picDual …) = (mulByInt E (finrank R R)).toAddMonoidHom` under `hnat`
- **What:** The Silverman III.6.1 main target `α ∘ α̂ = [deg α]` (finrank form): the actual point map composed with the Pic⁰ dual is multiplication by the degree.
- **How:** Rewrites via `toAddMonoidHom_eq_picPushforward_iff` (using `hnat`) to replace the point map with `picPushforward`, then applies `picPushforward_comp_picDual`.
- **Hypotheses:** `ch`, `hinj`, `hfin`, `hnat`.
- **Uses from project:** `toAddMonoidHom_eq_picPushforward_iff`, `picPushforward_comp_picDual`
- **Used by:** `picDual_comp_toAddMonoidHom_of_surjective`
- **Visibility:** public
- **Lines:** 565–573 (proof 2 lines)
- **Notes:** None.

---

### `theorem toAddMonoidHom_comp_picDual_degree`
- **Type:** `α.toAddMonoidHom.comp (α.picDual …) = (mulByInt E (α.degree : ℤ)).toAddMonoidHom` under `hnat` and tower witnesses
- **What:** The `α.degree` form of `toAddMonoidHom_comp_picDual`.
- **How:** Same as `toAddMonoidHom_comp_picDual` but additionally rewrites exponent via `picPushforward_comp_picDual_degree`.
- **Hypotheses:** `ch`, `hinj`, `hfin`, `hnat`, tower witnesses `S`, `S'`.
- **Uses from project:** `toAddMonoidHom_eq_picPushforward_iff`, `picPushforward_comp_picDual_degree`
- **Used by:** Not referenced by any other declaration in this file.
- **Visibility:** public
- **Lines:** 580–596 (proof ≈ 4 lines)
- **Notes:** Dead-code candidate within file.

---

### `theorem comp_eq_mulByInt_of_comp_eq_of_surjective`
- **Type:** `(f g : E.Point →+ E.Point) (m : ℤ), Surjective g → f.comp g = (mulByInt E m).toAddMonoidHom → g.comp f = (mulByInt E m).toAddMonoidHom`
- **What:** Abstract Silverman II.2.3 right-cancellation: if `f ∘ g = [m]` and `g` is surjective, then `g ∘ f = [m]`. Used to derive the companion composition order from the forward one.
- **How:** Surjects every `R` to some `g Q`, uses `hfg` at `Q` to get `f(g Q) = m•Q`, then `g.map_zsmul` to get `g(m•Q) = m•(g Q)`.
- **Hypotheses:** Surjectivity of `g`; the forward composition `hfg`.
- **Uses from project:** `mulByInt_apply`
- **Used by:** `picDual_comp_toAddMonoidHom_of_surjective`
- **Visibility:** public
- **Lines:** 638–651 (proof ≈ 12 lines)
- **Notes:** None.

---

### `theorem eq_of_comp_eq_of_surjective`
- **Type:** `(f₁ f₂ g : E.Point →+ E.Point), Surjective g → f₁.comp g = f₂.comp g → f₁ = f₂`
- **What:** Right-cancellation of a surjective map: if `f₁ ∘ g = f₂ ∘ g` and `g` is surjective, then `f₁ = f₂`. Encodes Silverman III.6.1(a) uniqueness move.
- **How:** Surjects every `a` to `b` with `g b = a`, then uses `congrArg` and `simpa` to propagate equality.
- **Hypotheses:** Surjectivity of `g`.
- **Uses from project:** None.
- **Used by:** `picDual_eq_of_comp_toAddMonoidHom_eq`, `picDual_eq_of_comp_toAddMonoidHom_eq_degree`
- **Visibility:** public
- **Lines:** 660–665 (proof ≈ 5 lines)
- **Notes:** None.

---

### `theorem picDual_comp_toAddMonoidHom_of_surjective`
- **Type:** `(α.picDual …).comp α.toAddMonoidHom = (mulByInt E (finrank R R)).toAddMonoidHom` under `hnat` and `hsurj : Surjective (α.picDual …)`
- **What:** Silverman III.6.2(a) companion order `α̂ ∘ α = [deg α]` (finrank form), derived by right-cancelling the surjective `picDual` from the forward order.
- **How:** Applies `comp_eq_mulByInt_of_comp_eq_of_surjective` with `toAddMonoidHom_comp_picDual`.
- **Hypotheses:** `ch`, `hinj`, `hfin`, `hnat`, `hsurj`.
- **Uses from project:** `comp_eq_mulByInt_of_comp_eq_of_surjective`, `toAddMonoidHom_comp_picDual`
- **Used by:** `picDual_comp_toAddMonoidHom_of_surjective_degree`, `picDual_eq_of_comp_toAddMonoidHom_eq`
- **Visibility:** public
- **Lines:** 676–687 (proof 2 lines)
- **Notes:** None.

---

### `theorem picDual_comp_toAddMonoidHom_of_surjective_degree`
- **Type:** `(α.picDual …).comp α.toAddMonoidHom = (mulByInt E (α.degree : ℤ)).toAddMonoidHom` under `hnat`, `hsurj`, and tower witnesses
- **What:** The `α.degree` form of `picDual_comp_toAddMonoidHom_of_surjective`.
- **How:** Rewrites via `picDual_comp_toAddMonoidHom_of_surjective`, then rewrites exponent via `degree_eq_finrank_coordinateRing_of_tower_eq`.
- **Hypotheses:** `ch`, `hinj`, `hfin`, `hnat`, `hsurj`, tower witnesses.
- **Uses from project:** `picDual_comp_toAddMonoidHom_of_surjective`, `Isogeny.degree_eq_finrank_coordinateRing_of_tower_eq`
- **Used by:** `picDual_eq_of_comp_toAddMonoidHom_eq_degree`
- **Visibility:** public
- **Lines:** 694–712 (proof ≈ 4 lines)
- **Notes:** None.

---

### `theorem picDual_eq_of_comp_toAddMonoidHom_eq`
- **Type:** Given `hnat`, `hsurjDual`, `hsurjα`, `hβ : β ∘ α = [finrank R R]`, concludes `α.picDual … = β`
- **What:** Silverman III.6.1(a) dual uniqueness (finrank form): any point map `β` satisfying `β ∘ α = [deg]` with `α` surjective equals the Pic⁰ dual.
- **How:** Applies `eq_of_comp_eq_of_surjective` with `hsurjα` to `(picDual ∘ α = [deg] = β ∘ α)`.
- **Hypotheses:** `hnat`, surjectivity of both `picDual` and `α`, `hβ`.
- **Uses from project:** `eq_of_comp_eq_of_surjective`, `picDual_comp_toAddMonoidHom_of_surjective`
- **Used by:** Not referenced by any other declaration in this file (dead-code candidate; used externally).
- **Visibility:** public
- **Lines:** 738–752 (proof 2 lines)
- **Notes:** Dead-code within file.

---

### `theorem picDual_eq_of_comp_toAddMonoidHom_eq_degree`
- **Type:** Same as `picDual_eq_of_comp_toAddMonoidHom_eq` but with `α.degree` exponent and tower witnesses
- **What:** Dual uniqueness in `α.degree` form.
- **How:** Applies `eq_of_comp_eq_of_surjective` with `picDual_comp_toAddMonoidHom_of_surjective_degree`.
- **Hypotheses:** `hnat`, surjectivities, tower witnesses, `hβ : β ∘ α = [α.degree]`.
- **Uses from project:** `eq_of_comp_eq_of_surjective`, `picDual_comp_toAddMonoidHom_of_surjective_degree`
- **Used by:** `picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq`, `picDual_zsmul_eq_zsmul_of_comp_eq` (via wrapper)
- **Visibility:** public
- **Lines:** 763–783 (proof 2 lines)
- **Notes:** None.

---

### `theorem picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq`
- **Type:** As `picDual_eq_of_comp_toAddMonoidHom_eq_degree` but with an explicit integer `d` and `hdeg : (α.degree : ℤ) = d`, plus `hδ : δ ∘ α = [d]`
- **What:** Non-circular seed form: if `α.degree = d` is independently known and `δ ∘ α = [d]`, then `picDual α = δ`. Avoids routing through the Pic⁰ push-pull degree.
- **How:** Rewrites `hdeg` into `hδ` and applies `picDual_eq_of_comp_toAddMonoidHom_eq_degree`.
- **Hypotheses:** `hnat`, surjectivities, tower witnesses, `hdeg`, `hδ`.
- **Uses from project:** `picDual_eq_of_comp_toAddMonoidHom_eq_degree`
- **Used by:** `picDual_zsmul_eq_zsmul_of_comp_eq`
- **Visibility:** public
- **Lines:** 807–827 (proof 2 lines)
- **Notes:** None.

---

### `theorem picDual_zsmul_eq_zsmul_of_comp_eq`
- **Type:** Given `r ≠ 0`, a `CoordHom` for `α.zsmul r`, naturality, surjectivities, tower witnesses, and `hδ : δ ∘ α.toAddMonoidHom = [deg α]`, proves `(α.zsmul r).picDual … = r • δ`
- **What:** Dual of `r`-scalar: `picDual(r • α) = r • α̂`. Non-circular: uses independently-known `deg(rα) = deg(α) · r²` and `(r • δ) ∘ (r • α) = [r² · deg α]`.
- **How:** Computes `hdeg` via `Isogeny.zsmul_degree` + `mulByInt_degree`; assembles `hcomp` pointwise using `map_zsmul` + `hδα`; applies `picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq`.
- **Hypotheses:** `r ≠ 0`, per-`(r•α)` `CoordHom` data, surjectivities, tower witnesses, `hδ`.
- **Uses from project:** `Isogeny.zsmul_degree`, `mulByInt_degree`, `Isogeny.zsmul_apply`, `picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq`
- **Used by:** `picDual_zsmul_eq_zsmul_of_isDual`
- **Visibility:** public
- **Lines:** 845–884 (proof ≈ 21 lines)
- **Notes:** Proof > 30 lines (845–884: 40 lines including long sig).

---

### `theorem picDual_zsmul_eq_zsmul_of_isDual`
- **Type:** As `picDual_zsmul_eq_zsmul_of_comp_eq` but takes a full `IsDualOf δ_isog α` (isogeny-level) instead of the point-map `hδ`
- **What:** Same as `picDual_zsmul_eq_zsmul_of_comp_eq` but with the dual partner in `IsDualOf` form (`δ_isog.comp α = mulByInt E (α.degree : ℤ)`), concluding `picDual(r • α) = r • δ_isog.toAddMonoidHom`.
- **How:** Calls `picDual_zsmul_eq_zsmul_of_comp_eq` after rewriting `h_isDual` via `Isogeny.comp_toAddMonoidHom`.
- **Hypotheses:** Same as `picDual_zsmul_eq_zsmul_of_comp_eq` but `h_isDual : δ_isog.comp α = mulByInt E (α.degree : ℤ)`.
- **Uses from project:** `picDual_zsmul_eq_zsmul_of_comp_eq`, `Isogeny.comp_toAddMonoidHom`
- **Used by:** Not referenced by any other declaration in this file.
- **Visibility:** public
- **Lines:** 891–912 (proof ≈ 4 lines)
- **Notes:** Dead-code candidate within file; intended for external callers (Route-C).

---

### `theorem picDual_eq_of_trace_relations`
- **Type:** Given `htrace_dual : α.toAddMonoidHom + α.picDual … = [tr]` and `htrace_delta : α.toAddMonoidHom + δ = [tr]`, proves `α.picDual … = δ`
- **What:** Pure point-group cancellation: if both `α̂` and `δ` satisfy the same trace relation `α + · = [tr]`, then `α̂ = δ`. The algebraic step of the Route-C dual-additivity output.
- **How:** Pointwise `DFunLike.congr_fun` on both hypotheses; cancels `α P` by `add_left_cancel`.
- **Hypotheses:** `htrace_dual`, `htrace_delta`.
- **Uses from project:** `mulByInt_apply`
- **Used by:** `picDual_eq_smul_sub_of_sum_trace`
- **Visibility:** public
- **Lines:** 925–938 (proof ≈ 7 lines)
- **Notes:** No degree input; purely algebraic.

---

### `theorem smul_sub_add_smul_sub_eq_mulByInt`
- **Type:** `(r • π - s • id) + (r • V - s • id) = (mulByInt E (r * t - 2 * s)).toAddMonoidHom` given `hsum : π + V = [t]`
- **What:** The candidate trace half: `(rπ - s) + (rV - s) = [rt - 2s]` from the Frobenius trace relation `π + V = [t]`. Non-circular, no degree, pure point-group algebra.
- **How:** Pointwise: substitutes `π P = t•P - V P` from `hsum`, rewrites `r•(t•P - VP)`, then `abel`.
- **Hypotheses:** `hsum : π + V = [t]`.
- **Uses from project:** `mulByInt_apply`
- **Used by:** `picDual_eq_smul_sub_of_sum_trace`
- **Visibility:** public
- **Lines:** 949–964 (proof ≈ 15 lines)
- **Notes:** None.

---

### `theorem picDual_eq_smul_sub_of_sum_trace`
- **Type:** Given `hbeta : α.toAddMonoidHom = r•π - s•id`, `hsum : π + V = [t]`, `htrace_dual : α.toAddMonoidHom + α.picDual … = [rt - 2s]`, proves `α.picDual … = r•V - s•id`
- **What:** III.6.2(c) dual-additivity engine: `picDual(rπ - s) = rV - s` under the Frobenius trace `hsum` and the III.8 trace relation for `α` as the single irreducible residual.
- **How:** Applies `picDual_eq_of_trace_relations` with `htrace_dual` and the candidate `smul_sub_add_smul_sub_eq_mulByInt` (after rewriting `hbeta`).
- **Hypotheses:** `ch`, `hinj`, `hfin`, `hbeta`, `hsum`, `htrace_dual`.
- **Uses from project:** `picDual_eq_of_trace_relations`, `smul_sub_add_smul_sub_eq_mulByInt`
- **Used by:** Not referenced by any other declaration in this file (intended for external Route-C callers).
- **Visibility:** public
- **Lines:** 980–991 (proof ≈ 4 lines)
- **Notes:** None.

---

### `theorem picDual_comp_toAddMonoidHom`
- **Type:** `(α.picDual …).comp α.toAddMonoidHom = (mulByInt E (finrank R R)).toAddMonoidHom` under `hnat` and `hother : classMap(classNorm c) = c^n`
- **What:** Silverman III.6.2(a) companion `α̂ ∘ α = [deg α]` derived directly from the reverse-order class identity `hother` (the opaque separate ingredient `φ* ∘ φ_* = [deg]`). Alternative route not via surjectivity.
- **How:** Rewrites via `toAddMonoidHom_eq_picPushforward_iff`, then applies `classTransport_comp_eq` with the reverse order `(classNorm, classMap)` and `hother`.
- **Hypotheses:** `hnat`, `hother`.
- **Uses from project:** `toAddMonoidHom_eq_picPushforward_iff`, `classTransport_comp_eq`
- **Used by:** Not referenced by any other declaration in this file.
- **Visibility:** public
- **Lines:** 1004–1017 (proof 2 lines)
- **Notes:** Dead-code candidate within file; provides an alternative (non-surjectivity) route to III.6.2(a) for callers who have `hother`.

---

## Summary

- **Total declarations:** 31 (3 defs, 1 Prop-def, 27 theorems/lemmas)
- **Sorries:** none
- **`set_option maxHeartbeats`:** `mk0_relNorm0_XYIdeal_eq_mk0_comap` at line 372, value 1600000 (comment present)
- **Long proofs (>30 lines):** `mk0_relNorm0_XYIdeal_eq_mk0_comap` (≈33 lines incl. sig), `picDual_zsmul_eq_zsmul_of_comp_eq` (≈40 lines incl. long sig)
- **Unused in file (dead-code candidates):** `picDual_apply`, `Naturality_of_toClassEquiv'_some_eq_relNorm0`, `toAddMonoidHom_comp_picDual_degree`, `naturality_of_coordHom`, `picDual_eq_of_comp_toAddMonoidHom_eq`, `picDual_zsmul_eq_zsmul_of_isDual`, `picDual_eq_smul_sub_of_sum_trace`, `picDual_comp_toAddMonoidHom`
- **Key API (used by 3+ declarations in file):** `classTransport`, `Naturality`, `toAddMonoidHom_eq_picPushforward_iff`, `picPushforward_comp_picDual`, `classTransport_comp_eq`, `eq_of_comp_eq_of_surjective`
