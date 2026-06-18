# Decomposition — The Tate module `T_ℓ(E) = lim_n E[ℓⁿ] ≅ ℤ_ℓ²` and the ℓ-adic representation (Silverman III.7)

Planning-only. Source: Silverman, *The Arithmetic of Elliptic Curves* (2nd ed), §III.7,
PDF pp. 105–109 (= book pp. 87–91). All page refs below are **book** pages.

---

## (a) Source's correct definitions / statements (faithful, with quotes)

### Setup (book p. 87)

> "Let `E/K` be an elliptic curve and let `m ≥ 2` be an integer, prime to `char(K)` if
> `char(K) > 0`. As we have seen, `E[m] ≅ ℤ/mℤ × ℤ/mℤ`, the isomorphism being one between
> abstract groups."

> "each element `σ` of the Galois group `G_{K̄/K}` acts on `E[m]`, since if `[m]P = O`, then
> `[m](Pσ) = ([m]P)σ = Oσ = O`. We thus obtain a representation
> `G_{K̄/K} → Aut(E[m]) ≅ GL₂(ℤ/mℤ)`, where the latter isomorphism involves choosing a basis for
> `E[m]`."

This is the **mod-m representation**; the Tate module fits these together over `m = ℓⁿ`.

### Definition of the Tate module (book p. 87)

> "**Definition.** Let `E` be an elliptic curve and let `ℓ ∈ ℤ` be a prime. The (ℓ-adic) *Tate
> module* of `E` is the group `T_ℓ(E) = lim_n E[ℓⁿ]`, the inverse limit being taken with respect to
> the natural maps `E[ℓⁿ⁺¹] --[ℓ]--> E[ℓⁿ]`."

> "Since each `E[ℓⁿ]` is a `ℤ/ℓⁿℤ`-module, we see that the Tate module has a natural structure as a
> `ℤ_ℓ`-module. Further, since the multiplication-by-`ℓ` maps are surjective, the inverse limit
> topology on `T_ℓ(E)` is equivalent to the `ℓ`-adic topology that it gains by being a `ℤ_ℓ`-module."

Note: the connecting map `E[ℓⁿ⁺¹] → E[ℓⁿ]` is **multiplication by `ℓ`** (`[ℓ]`), and it lands in
`E[ℓⁿ]` because if `ℓⁿ⁺¹·P = 0` then `ℓⁿ·(ℓ·P) = 0`.

### Structure theorem (book p. 88)

> "**Proposition 7.1.** As a `ℤ_ℓ`-module, the Tate module has the following structure:
> (a) `T_ℓ(E) ≅ ℤ_ℓ × ℤ_ℓ`  if `ℓ ≠ char(K)`.
> (b) `T_p(E) ≅ {0} or ℤ_p`  if `p = char(K) > 0`.
> PROOF. This follows immediately from (III.6.4b,c)."

So **the whole structure theorem is `E[ℓⁿ] ≅ (ℤ/ℓⁿ)²` for all `n`, fed through the limit.** III.6.4(b)
is `#E[m] = m²` for `m` prime to `char`; III.6.4(c) is the cyclic-group decomposition giving
`E[m] ≅ ℤ/mℤ × ℤ/mℤ`. The `ℓ ≠ char` case (a) is the only one we target.

### The ℓ-adic representation (book p. 88)

> "The action of `G_{K̄/K}` on each `E[ℓⁿ]` commutes with the multiplication-by-`ℓ` map used to form
> the inverse limit, so `G_{K̄/K}` also acts on `T_ℓ(E)`. … the resulting action on `T_ℓ(E)` is also
> continuous."

> "**Definition.** The *ℓ-adic representation* (of `G_{K̄/K}` associated to `E`) is the homomorphism
> `ρ_ℓ : G_{K̄/K} → Aut(T_ℓ(E))` induced by the action of `G_{K̄/K}` on the `ℓⁿ`-torsion points of
> `E`."

### Remark 7.2 (book p. 88) — the GL₂ form

> "If we choose a `ℤ_ℓ`-basis for `T_ℓ(E)`, we obtain a representation `G_{K̄/K} → GL₂(ℤ_ℓ)`, and
> then the natural inclusion `ℤ_ℓ ⊂ ℚ_ℓ` gives a representation `G_{K̄/K} → GL₂(ℚ_ℓ)`."

### (Out of scope but read) Theorem 7.4 + Cor 7.5 (book pp. 89–91)

> "**Theorem 7.4.** Let `E₁` and `E₂` be elliptic curves and let `ℓ ≠ char(K)` be a prime. Then the
> natural map `Hom(E₁,E₂) ⊗ ℤ_ℓ → Hom(T_ℓ(E₁), T_ℓ(E₂))`, `φ ↦ φ_ℓ`, is injective."
> "**Corollary 7.5.** `Hom(E₁,E₂)` is a free `ℤ`-module of rank at most 4."

The 7.4/7.5 proof uses `M^div` finitely generated + the degree map on `M ⊗ ℝ`. **Explicitly out of
scope for this topic** (it is the hardest analytic part and not needed for the Hasse-bound endgame).

---

## (b) Silverman's proof skeleton

The decomposition spine is short because Prop 7.1 "follows immediately from (III.6.4b,c)":

1. **`E[ℓⁿ] ≅ (ℤ/ℓⁿ)²` for every `n ≥ 1`** (III.6.4b,c at `m = ℓⁿ`). This is the *only* real
   mathematical content. In the project, III.6.4 is already done **at `m = ℓ`** but the engine
   (`mulByInt_isSeparable`, kernel-rationality `kernelDescends_general`, normality
   `h_normal_mulByInt`, descent `hdesc_mulByInt`, capstone
   `card_kernel_eq_degree_of_separable_concrete`) is stated for a **general** `ℤ`, hence instantiates
   at `ℓⁿ` verbatim once `(ℓⁿ : F) ≠ 0` (automatic from `(ℓ:F)≠0` since `ℓⁿ = ℓ·…·ℓ`).
   The module/dimension layer (`TorsionGeometric.lean`) is likewise stated at a prime `ℓ` and must be
   re-run with the **ring** `ZMod (ℓⁿ)` (not a field) — this changes `finrank`→free-rank reasoning
   (see leaf risks).

2. **The inverse system**: connecting maps `[ℓ] : E[ℓⁿ⁺¹] → E[ℓⁿ]` (well-defined: `ℓⁿ·(ℓ·P)=0`),
   plus compatibility with the `ZMod`-module structures (the `ZMod(ℓⁿ⁺¹)`-action descends to a
   `ZMod(ℓⁿ)`-action along `ZMod.castHom`).

3. **`T_ℓ(E) = lim`, `≅ ℤ_ℓ²`**: build the limit object as a `ℤ_ℓ`-submodule of `Π n, E[ℓⁿ]`
   (mathlib has **no** generic module inverse-limit), then prove it `≅ ℤ_ℓ²` by transporting the
   per-`n` isomorphisms `E[ℓⁿ] ≅ (ℤ/ℓⁿ)²` through the limit, landing on `lim (ℤ/ℓⁿ)² = (lim ℤ/ℓⁿ)² =
   ℤ_ℓ²`. The bridge `lim ℤ/ℓⁿ ≅ ℤ_ℓ` is **mathlib's `PadicInt.lift` universal property**
   (`lift`, `lift_spec`, `lift_unique`, `ext_of_toZModPow`).

4. **The ℓ-adic representation**: each `σ ∈ G_{K̄/K}` (a field automorphism of `K̄` over `K`) acts on
   each `E[ℓⁿ]` via `Affine.Point.map σ` (already an `AddMonoidHom`; preserves torsion), commutes
   with the connecting `[ℓ]` maps (`map_zsmul`), hence acts on the limit `ℤ_ℓ`-linearly, giving
   `ρ_ℓ : G_{K̄/K} → Aut_{ℤ_ℓ}(T_ℓ(E))`, and after a basis `→ GL₂(ℤ_ℓ)` (Remark 7.2).

**Honest scoping decision.** Over a *finite* base field `K = 𝔽_q` (the project's Hasse-bound setting,
`F = K̄`), the absolute Galois group `G_{K̄/K}` is topologically generated by Frobenius and is rarely
needed *as a profinite group with its topology* for the Hasse bound — the bound uses the **mod-ℓ**
rep `rhoEll` already built in `Representation.lean`. Therefore this development is best framed as a
**standalone structural module** (`T_ℓ(E) ≅ ℤ_ℓ²` + the abstract action), not wired into
`HasseBound.lean`. Continuity of `ρ_ℓ` (a topological statement) and the GL₂(ℚ_ℓ) form are marked
*optional* below.

---

## (c) Ordered list of LEAVES

Conventions: `W : WeierstrassCurve F`, `[W.toAffine.IsElliptic]`, `[IsAlgClosed F]`, `ℓ : ℕ`,
`[Fact ℓ.Prime]`, `(hℓF : (ℓ : F) ≠ 0)`. Torsion `E[m] = W.toAffine[(m:ℤ)]` (notation from
`HasseWeil/Basic.lean:755`). All "existing project decl" refs are `file:name`.

### Phase 1 — generalize `E[ℓⁿ] ≅ (ℤ/ℓⁿ)²`

**L1. `(ℓ^n : F) ≠ 0`.**
`theorem pow_ne_zero_of_ne_zero (n : ℕ) : ((ℓ^n : ℕ) : F) ≠ 0`.
Discharge: mathlib `pow_ne_zero` + `Nat.cast_pow`; trivial. **LOC ~5.** Source: implicit in
"prime to `char(K)`" (p. 87).

**L2. `#E[ℓⁿ] = ℓ^{2n}` (= III.6.4(b) at `m = ℓⁿ`).**
`theorem card_torsion_ellPow (n : ℕ) : (Nat.card W.toAffine[((ℓ^n : ℕ):ℤ)] : ℤ) = (ℓ^n)^2`.
Discharge: **existing** `TorsionGeometric.card_torsion_ell` is stated for a general `ℓ:ℤ`
(`TorsionCardEll.lean:71`, requires only `(ℓ:F)≠0`, `[IsAlgClosed F]`) — instantiate at
`ℓ := (ℓ^n : ℤ)` using L1. **No new geometry.** **LOC ~10.** Source: Prop 7.1 proof "follows from
III.6.4b" (p. 88).

**L3. `ZMod (ℓⁿ)`-module structure on `E[ℓⁿ]`.**
`scoped instance : Module (ZMod (ℓ^n)) W.toAffine[((ℓ^n:ℕ):ℤ)]`.
Discharge: **mirror** `TorsionGeometric.torsion_ell_zmodModule` (`TorsionModule.lean:68`) via
`AddCommGroup.zmodModule` + a generalized `nsmul_eq_zero_of_mem_torsion_ell`
(`TorsionModule.lean:53`) at exponent `ℓ^n` (note: needs `ℓ^n • P = 0`, which is
`mem_torsionSubgroup` at `(ℓ^n:ℤ)`). **LOC ~15.** Source: "each `E[ℓⁿ]` is a `ℤ/ℓⁿℤ`-module" (p. 87).

**L4. `E[ℓⁿ]` is free of rank 2 over `ZMod (ℓⁿ)`.**
`theorem torsion_ellPow_free : Module.Free (ZMod (ℓ^n)) W.toAffine[((ℓ^n:ℕ):ℤ)] ∧
   Module.finrank (ZMod (ℓ^n)) W.toAffine[((ℓ^n:ℕ):ℤ)] = 2`, or more usefully a basis
`Basis (Fin 2) (ZMod (ℓ^n)) E[ℓⁿ]`.
Discharge: **GENUINELY NEW** but standard. `ZMod (ℓⁿ)` is a *ring*, not a field, so the field route
`TorsionGeometric.finrank_torsion_ell` (`TorsionModule.lean:98`, uses `Module.natCard_eq_pow_finrank`
which needs a *field*) does **not** apply directly. Need the structure theorem for finite modules
over the PIR/local ring `ZMod (ℓⁿ)`: a finite `ZMod(ℓⁿ)`-module killed by `ℓⁿ` with cardinality
`(ℓⁿ)²` and "no `ℓ^{n-1}`-torsion beyond rank 2" is free of rank 2. Cleanest faithful route: prove
`E[ℓⁿ] ≅ (ZMod ℓⁿ)²` directly from `E[ℓ]≅(ZMod ℓ)²` (already have) **+** the fact that mult-by-`ℓ`
`E[ℓⁿ⁺¹] → E[ℓⁿ]` is surjective with kernel `E[ℓ]` (III.6.4(b) consequence), by induction on `n`.
This is exactly Silverman's "writing `E[ℓⁿ]` as a product of cyclic groups" (book p. 87, top: the
`#E[pᵉ]=pᵉ` analogue). **Check mathlib:** `Module.Finite` + `ZMod` PIR structure
(`Mathlib/Data/ZMod/...`, `Mathlib/RingTheory/...`) may give a finitely-generated-module
classification, but there is **no** off-the-shelf "`E[ℓⁿ]≅(ZMod ℓⁿ)²`". **LOC ~120–180** (this is the
real new work for Phase 1; the cardinality `(ℓⁿ)²` alone does *not* pin the module type over a
non-field, unlike the `n=1` field case). Source: Prop 7.1 + p. 87 cyclic-decomposition remark.
**Alternative (lower-risk):** keep only the **abstract-group** iso `E[ℓⁿ] ≃+ (ZMod ℓⁿ)²` (matching
Silverman's "isomorphism between abstract groups", p. 87) and derive freeness as a corollary; this
sidesteps the `ZMod(ℓⁿ)`-linearity bookkeeping.

### Phase 2 — the inverse system

**L5. Connecting map `[ℓ] : E[ℓⁿ⁺¹] → E[ℓⁿ]`.**
`def tateConn (n : ℕ) : W.toAffine[((ℓ^(n+1):ℕ):ℤ)] →+ W.toAffine[((ℓ^n:ℕ):ℤ)]` :=
(restrict of `ℓ • ·`). Well-defined: `P ∈ E[ℓⁿ⁺¹] ⟹ ℓⁿ·(ℓ·P) = ℓⁿ⁺¹·P = 0 ⟹ ℓ·P ∈ E[ℓⁿ]`.
Discharge: **mostly NEW** but mechanical — codRestrict of `zsmulAddGroupHom ℓ` composed with the
subgroup inclusion, exactly like `Representation.torsionRestrictHom` (`Representation.lean:75`).
The membership proof uses `mem_torsionSubgroup` (`Basic.lean:757`) + `smul_smul`/`pow_succ`.
**LOC ~25.** Source: "the natural maps `E[ℓⁿ⁺¹] --[ℓ]--> E[ℓⁿ]`" (p. 87).

**L6. `tateConn` is `ZMod`-semilinear along `ZMod.castHom`.**
`theorem tateConn_castHom_compat (n) (c : ZMod (ℓ^(n+1))) (P) :
   tateConn (n) (c • P) = (ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ^n)) c) • tateConn n P`.
Discharge: **NEW**, short. Both scalar actions reduce to natural-number `•` (the `zmodModule`
action), and `[ℓ]` is an `AddMonoidHom` so commutes with `n • ·`; the `castHom` bookkeeping is
`ZMod.natCast_val`/`ZMod.castHom_apply`. **LOC ~30.** Source: "commutes with the
multiplication-by-`ℓ` map" (p. 88).

**L7. Surjectivity of the connecting maps.**
`theorem tateConn_surjective (n : ℕ) : Function.Surjective (tateConn n)`.
Discharge: **NEW**, follows from L4's "`[ℓ]:E[ℓⁿ⁺¹]→E[ℓⁿ]` surjective" (cardinality count:
`#E[ℓⁿ⁺¹]/#ker = (ℓⁿ⁺¹)²/(ℓ²) ·…`; precisely `#image = #E[ℓⁿ⁺¹]/#(E[ℓⁿ⁺¹]∩E[ℓ]) `). Cleanest via
`[ℓ]` surjective on `E(K̄)` (existing `HasseWeil/EC/IsogenySurjective.lean` /
`PointMapSurjective.lean` — mult-by-`ℓ` is surjective over alg. closed `F`) restricted. **Needed only
for the "ℓ-adic = inverse-limit topology" remark; NOT needed for `≅ ℤ_ℓ²`.** Mark *optional* if the
topology claim is dropped. **LOC ~40** (or 0 if skipped). Source: "the multiplication-by-`ℓ` maps are
surjective" (p. 87).

### Phase 3 — `T_ℓ(E) = lim`, `≅ ℤ_ℓ²`

**L8. The Tate-module object as a submodule of the product.**
`def tateModule : Submodule ℤ_[ℓ] (Π n : ℕ, ...)` — but the per-`n` factors are
`ZMod (ℓⁿ)`-modules with *different* rings, so the carrier is the **dependent**
`{ f : Π n, W.toAffine[((ℓ^n:ℕ):ℤ)] // ∀ n, tateConn n (f (n+1)) = f n }` as an `AddSubgroup` of
`Π n, E[ℓⁿ]`, with a `ℤ_[ℓ]`-module structure built so that `z • f` acts on coordinate `n` by
`(toZModPow n z) • f n` (compatible by L6 + `cast_toZModPow`, `RingHoms.lean:496`).
Discharge: **GENUINELY NEW** (this is the core construction). There is **no** mathlib generic
inverse-limit of modules (confirmed: only category-theory `ModuleCat` limits, not a usable
`Submodule`). Must hand-build: (i) the `AddSubgroup` of compatible sequences; (ii) the `ℤ_[ℓ]`-scalar
action via `PadicInt.toZModPow`; (iii) `Module` axioms (`one_smul` via `toZModPow_one`/`map_one`,
`mul_smul` via `map_mul`, `add_smul`, `smul_add`) using the compatibility `cast_toZModPow`.
**LOC ~150–220.** Source: Definition "`T_ℓ(E) = lim_n E[ℓⁿ]` … natural structure as a `ℤ_ℓ`-module"
(p. 87).

**L9. `lim (ℤ/ℓⁿ) ≅ ℤ_ℓ` via `PadicInt.lift` (the limit-of-`ZMod`-tower fact).**
`def padicIntEquivLimZMod : ℤ_[ℓ] ≃+* { f : Π n, ZMod (ℓ^n) // ∀ n, ZMod.castHom (pow_dvd_pow ℓ
   n.le_succ) _ (f (n+1)) = f n }`.
Discharge: **GENUINELY NEW but fully mechanical from mathlib.** Forward map: `z ↦ ⟨fun n => toZModPow
n z, by simp [cast_toZModPow]⟩` (compatibility = `RingHoms.lean: zmod_cast_comp_toZModPow`/
`cast_toZModPow`). Inverse: `PadicInt.lift` (`RingHoms.lean:653`) applied to the compatible family.
Bijectivity: `lift_spec` (`RingHoms.lean:686`) + `ext_of_toZModPow` (`RingHoms.lean:710`) +
`lift_unique` (`RingHoms.lean:694`). Ring-hom-ness: `lift` is already a `RingHom`. This is the single
most reusable new lemma. **LOC ~90.** Source: "we mimic the inverse limit construction of the ℓ-adic
integers `ℤ_ℓ` from the finite groups `ℤ/ℓⁿℤ`" (p. 87).

**L10. `T_ℓ(E) ≅ ℤ_ℓ²` (Prop 7.1(a)).**
`def tateModuleEquiv : tateModule W ℓ ≃ₗ[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ])`.
Discharge: **NEW assembly.** Transport the per-`n` isos `E[ℓⁿ] ≅ (ZMod ℓⁿ)²` from L4 through the
limit: `lim E[ℓⁿ] ≅ lim (ZMod ℓⁿ)² ≅ (lim ZMod ℓⁿ)² ≅ ℤ_ℓ²` (last step = L9, `Fin 2`-componentwise;
`lim` commutes with finite products). **Requires the per-`n` isos to be compatible with both
connecting systems** (`tateConn` ↔ `ZMod.castHom` on `(ZMod ℓⁿ)²`) — this compatibility is the
delicate part and must be threaded from L4's construction (choose the bases coherently, OR prove
naturality after the fact). **LOC ~120–180.** Source: Prop 7.1(a) (p. 88).

### Phase 4 — the ℓ-adic representation

**L11. Galois action on each `E[ℓⁿ]`.**
For `σ : F ≃ₐ[K] F` (here `F = K̄`; over a finite base, `K` the prime/base field): the point map
`Affine.Point.map σ.toRingHom : E(F) →+ E(F)` preserves `E[ℓⁿ]`.
`def galoisTorsionRestrict (σ) (n) : W.toAffine[((ℓ^n:ℕ):ℤ)] →ₗ[ZMod (ℓ^n)] W.toAffine[...]`.
Discharge: **mostly EXISTING.** `Affine.Point.map` is an `AddMonoidHom` with `map_zsmul`
(`AffinePointMap.lean:127`); torsion-preservation is `Representation.map_mem_torsion_ell`
(`Representation.lean:60`) **generalized to exponent `ℓⁿ`** (same proof). `ZMod(ℓⁿ)`-linearity is
free (`toZModLinearMap`, as in `Representation.torsionRestrict`, `Representation.lean:97`). **NB:**
the project models `K(E)`-translations as `AlgEquiv`, but for a *Galois* action one needs
`Affine.Point.map` along a field automorphism `σ : K̄ ≃ₐ[K] K̄`; the point-map-along-ring-hom API
(`PointMap.lean`, `AffinePointMap.lean`) already supports this. **LOC ~30** (generalize the prime-`ℓ`
version). Source: "`σ` acts on `E[m]`, since if `[m]P=O` then `[m](Pσ)=O`" (p. 87).

**L12. The action commutes with the connecting maps + assembles to `T_ℓ`.**
`theorem galois_comm_tateConn (σ) (n) : tateConn n ∘ galoisTorsionRestrict σ (n+1) =
   galoisTorsionRestrict σ n ∘ tateConn n` (componentwise), hence
`def rhoTate (σ : F ≃ₐ[K] F) : tateModule W ℓ ≃ₗ[ℤ_[ℓ]] tateModule W ℓ`.
Discharge: **NEW.** Commutation is `map_zsmul` for `Affine.Point.map σ` (Galois maps commute with
`[ℓ] = ℓ•·`) — exactly the `hequiv`/`map_zsmul` pattern already used in
`TorsionKernelRational.hdesc_mulByInt` (`TorsionKernelRational.lean:257`). Then `rhoTate σ` acts on
compatible sequences coordinatewise, is `ℤ_[ℓ]`-linear (L6/L8 scalar compat), and is invertible
(`σ⁻¹` gives the inverse). **LOC ~70.** Source: "The action of `G_{K̄/K}` on each `E[ℓⁿ]` commutes
with the multiplication-by-`ℓ` map … so `G_{K̄/K}` also acts on `T_ℓ(E)`" (p. 88).

**L13. `ρ_ℓ` is a group homomorphism `(F ≃ₐ[K] F) → (tateModule ≃ₗ[ℤ_[ℓ]] tateModule)`.**
`def rhoTateHom : (F ≃ₐ[K] F) →* (tateModule W ℓ ≃ₗ[ℤ_[ℓ]] tateModule W ℓ)` (`map_one`, `map_mul`).
Discharge: **NEW**, easy from L12: `Affine.Point.map` is functorial in the ring hom
(`map_map`/`map_id` — used at `AffinePointMap`/`PointMap`), so `rhoTate (σ∘τ) = rhoTate σ ∘ rhoTate
τ` and `rhoTate 1 = id`. **LOC ~40.** Source: Definition of `ρ_ℓ` (p. 88).

**L14 (optional). GL₂(ℤ_ℓ) form (Remark 7.2).**
`def rhoTateGL : (F ≃ₐ[K] F) →* GL (Fin 2) ℤ_[ℓ]` via the basis from L10.
Discharge: **NEW**, transport `rhoTateHom` through `tateModuleEquiv` (L10) into
`(Fin 2 → ℤ_[ℓ]) ≃ₗ[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ])`, then to `GL (Fin 2) ℤ_[ℓ]` via `LinearMap.toMatrix` +
`LinearEquiv.toGL`/`Matrix.GeneralLinearGroup` (`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/`).
**LOC ~50.** Source: Remark 7.2 (p. 88).

**L15 (optional, HARD/marked NEW). Continuity of `ρ_ℓ`.** The statement "the resulting action on
`T_ℓ(E)` is also continuous" (p. 88) requires a profinite/topological-group structure on `G_{K̄/K}`
and the inverse-limit topology on `T_ℓ`. **Recommend dropping** — not needed for the Hasse bound and
is a large topological development (Krull topology on `Aut`, profinite limit topology). Mark as
explicit out-of-scope. **LOC ~300+ if attempted.**

---

## (d) Genuinely-new definitions needed (signatures)

```lean
-- L3: ZMod (ℓ^n)-module structure on the ℓ^n-torsion
noncomputable scoped instance torsion_ellPow_zmodModule (n : ℕ) :
    Module (ZMod (ℓ^n)) W.toAffine[((ℓ^n : ℕ) : ℤ)]

-- L5: the connecting map [ℓ] : E[ℓⁿ⁺¹] → E[ℓⁿ]
noncomputable def tateConn (n : ℕ) :
    W.toAffine[((ℓ^(n+1) : ℕ) : ℤ)] →+ W.toAffine[((ℓ^n : ℕ) : ℤ)]

-- L9: lim ZMod (ℓ^n) ≅ ℤ_ℓ  (the reusable bridge; pure mathlib PadicInt.lift)
def compatZMod (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  { f : Π n : ℕ, ZMod (ℓ^n) //
      ∀ n, ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ^n)) (f (n+1)) = f n }
def padicIntEquivLimZMod (ℓ : ℕ) [Fact ℓ.Prime] : ℤ_[ℓ] ≃+* compatZMod ℓ

-- L8: the Tate module as a ℤ_ℓ-submodule of the product (hand-built inverse limit)
def tateCompat : AddSubgroup (Π n : ℕ, W.toAffine[((ℓ^n : ℕ) : ℤ)]) :=
  { carrier := { f | ∀ n, tateConn W ℓ n (f (n+1)) = f n }, ... }
noncomputable instance : Module ℤ_[ℓ] (tateCompat W ℓ)   -- via PadicInt.toZModPow
def tateModule : Type _ := tateCompat W ℓ                 -- with the ℤ_ℓ-module instance

-- L10: the structure theorem
noncomputable def tateModuleEquiv : tateModule W ℓ ≃ₗ[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ])

-- L11–L13: the ℓ-adic representation (F = K̄, σ : F ≃ₐ[K] F)
noncomputable def galoisTorsionRestrict (σ : F ≃ₐ[K] F) (n : ℕ) :
    W.toAffine[((ℓ^n : ℕ) : ℤ)] →ₗ[ZMod (ℓ^n)] W.toAffine[((ℓ^n : ℕ) : ℤ)]
noncomputable def rhoTate (σ : F ≃ₐ[K] F) : tateModule W ℓ ≃ₗ[ℤ_[ℓ]] tateModule W ℓ
noncomputable def rhoTateHom : (F ≃ₐ[K] F) →* (tateModule W ℓ ≃ₗ[ℤ_[ℓ]] tateModule W ℓ)
```

Note on `K` vs `F`: the project's torsion work fixes `F = K̄` (`[IsAlgClosed F]`). For the Galois
action one needs a *base* field `K` with `F = AlgebraicClosure K` (or `[Algebra K F]` + `[IsGalois K
F]`). The cleanest framing matching the project is: `K` finite, `F := AlgebraicClosure K`, `W :
WeierstrassCurve K`, work with `W.baseChange F`. The `σ : F ≃ₐ[K] F` then acts via the existing
point-map-along-ring-hom API.

---

## (e) Dependency order + dependence on the other two topics

Internal order: **L1 → L2 → L3 → L4** (Phase 1, the only real new math is L4) **→ L5 → L6 (→ L7
optional)** (Phase 2) **→ L9** (independent of L1–L7, pure mathlib `PadicInt`; can be done first/in
parallel) **→ L8 → L10** (Phase 3) **→ L11 → L12 → L13 (→ L14, L15 optional)** (Phase 4).

L9 is a leaf with **no** project dependencies — ideal first parallel target.

**Dependence on the other two topics (Weil pairing `e_ℓ` / Hasse bound; isogeny degree theory):**

- **Strong reuse of the existing `E[ℓ]≅(ℤ/ℓ)²` stack** (`TorsionModule.lean`, `TorsionCardEll.lean`,
  `TorsionKernelRational.lean`, `SeparableKernelTorsor.lean`), which itself rests on
  `mulByInt_isSeparable` and `card_kernel_eq_degree_of_separable_concrete`. This stack is the *same*
  machinery the **Hasse-bound / Weil-pairing** topic uses; the Tate module reuses it at `ℓⁿ` (so it
  inherits whatever axiom status that chain has — currently **axiom-clean** per memory:
  `card_torsion_ell` is clean over `IsAlgClosed F`).
- **No dependence on the Weil pairing `e_ℓ`** for the *structure* theorem (Prop 7.1) — that is purely
  III.6.4. The Weil pairing enters only if one later wants `det ρ_ℓ = χ_cyc` (the
  cyclotomic-character determinant, Silverman III.8 / the pairing's Galois-equivariance), which is
  **out of scope here**.
- **Mild forward link:** the project's `Representation.rhoEll` (mod-ℓ matrix rep) is the `n=1`
  reduction of `rhoTateGL` (L14); they should agree under `toZModPow 1`. Not required, but a natural
  consistency lemma.

---

## (f) Honest risks / hardest parts

1. **L4 (`E[ℓⁿ]≅(ZMod ℓⁿ)²`) is the genuine mathematical risk.** Over the **non-field** ring
   `ZMod (ℓⁿ)`, cardinality `(ℓⁿ)²` does **not** determine the module — e.g. `ZMod(ℓ²)⊕ZMod(ℓ²)`,
   `ZMod(ℓⁿ⁺¹)⊕ZMod(ℓ^{n-1})`, etc. all have the right card for some exponents. The proof **must**
   use the *structure* of `E[ℓⁿ]` as a `[ℓⁿ]`-torsion group with `E[ℓ]` exactly rank 2 and the
   surjective filtration `E[ℓⁿ⁺¹] ↠ E[ℓⁿ]` (kernel `≅ E[ℓ]`). The faithful induction (`E[ℓⁿ]≅(ZMod
   ℓⁿ)²` from `E[ℓ]≅(ZMod ℓ)²` + `[ℓ]`-surjectivity) is exactly Silverman's "product of cyclic
   groups" remark but is **nontrivial to formalize** (choosing coherent generators / lifting bases
   along `[ℓ]`). Mathlib's finite-abelian-group / finite-module-over-PIR classification
   (`Module.Finite`, `ZMod` is a PIR) **may** shortcut it, but there is no ready-made result; budget
   the most time here. **This single leaf may be 30–50% of the total effort.**

2. **No mathlib generic module inverse limit (L8).** Confirmed: mathlib has `PadicInt` as a
   *completion* (not as `lim ZMod`), category-theory `ModuleCat` limits (not a usable `Submodule`),
   and `LinearMap.pi`/`Submodule.pi` but no "inverse limit of a tower of modules" object. So L8 is a
   hand-rolled `AddSubgroup` of `Π n, E[ℓⁿ]` with a bespoke `ℤ_[ℓ]`-`Module` instance whose scalar
   action goes *through* `PadicInt.toZModPow`. The `Module` axiom proofs (esp. `mul_smul`,
   `one_smul`) are fiddly because the action mixes `toZModPow n (z·w) = toZModPow n z · toZModPow n
   w` per coordinate. Mechanical but error-prone (~150–220 LOC).

3. **L9 is low-risk** — mathlib's `PadicInt.lift` / `lift_spec` / `lift_unique` / `ext_of_toZModPow`
   / `zmod_cast_comp_toZModPow` / `cast_toZModPow` give the projective-limit universal property
   *verbatim*; the equiv is a short package. **This is the load-bearing mathlib win** that makes the
   whole topic feasible.

4. **L10 naturality threading.** Getting `lim E[ℓⁿ] ≅ lim (ZMod ℓⁿ)²` requires the per-`n`
   isomorphisms from L4 to be **natural** in the connecting maps (`tateConn ↔ ZMod.castHom`). If L4's
   isos are built ad hoc (independent bases per `n`), naturality fails and L10 stalls. Mitigation:
   build the bases *coherently* during the L4 induction (lift the `E[ℓⁿ]`-basis along `[ℓ]` to
   `E[ℓⁿ⁺¹]`), so the connecting square commutes by construction. This couples L4 and L10 tightly.

5. **Galois framing (Phase 4) is conceptually easy but bureaucratically heavy.** `Affine.Point.map`
   along `σ : K̄ ≃ₐ[K] K̄`, scalar-tower diamonds (`ZMod(ℓⁿ)` action vs `ℤ_[ℓ]` action), and the
   `F = K̄` vs base-`K` instance management (the project's pitfall, cf. `W_smooth` HAdd-synth note in
   memory) will cost more than the math suggests. `rhoTate` invertibility via `σ⁻¹` is clean.

6. **Continuity (L15) and Thm 7.4/Cor 7.5 are out of scope** and should be explicitly excluded;
   attempting them roughly triples the effort (profinite topology; `M^div` finite-generation + degree
   map on `M⊗ℝ`).

**Bottom line.** The topic is **feasible and largely greenfield** (no Tate-module code exists in
project or mathlib). The structure theorem decomposes cleanly into: (i) re-run the existing III.6.4
machinery at `ℓⁿ` (cheap, L1–L3), (ii) the **module classification `E[ℓⁿ]≅(ZMod ℓⁿ)²`** (the hard new
math, L4), (iii) the **hand-built inverse limit** glued to **mathlib's `PadicInt.lift`** (L8–L10, the
engineering core), (iv) the Galois action (L11–L13, routine). Total realistic budget **~700–950 LOC**,
with L4 and L8/L10 carrying the risk.
