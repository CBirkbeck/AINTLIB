module

public import CebotarevDensity.Cyclotomic
public import CebotarevDensity.FixedFieldDensity
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Chebotarev's theorem: abelian case

For an abelian Galois extension `L/K` of number fields and any
`σ ∈ Gal(L/K)`, the Dirichlet density of primes `𝔭` of `𝓞 K` (unramified in
`L`) whose Frobenius equals `σ` is `1 / |Gal(L/K)|`.

The proof reduces to the cyclotomic case by *crossing with cyclotomic
extensions* (Chebotarev's original technique). For `m` coprime to the
discriminant of `L`, the field `L(μ_m)` is Galois over `K` with
`Gal(L(μ_m)/K) ≅ G × H` where `H = Gal(K(μ_m)/K) ⊆ (ℤ/mℤ)^×`. For `τ ∈ H`
with `|G| | ord(τ)`, the subgroup `⟨(σ, τ)⟩` has trivial intersection with
`G × {1}`, so its fixed field `F` satisfies `F(μ_m) = L(μ_m)` — making
`L(μ_m)/F` cyclotomic. The cyclotomic case applied to `L(μ_m)/F` and
`(σ, τ)` gives
`δ_F(primes P with σ_P = (σ, τ)) = 1/(|G| · |H|)`, and the (cyclic)
reduction lifts this through `F/K` to a lower-density bound on the primes
of `K` with Frobenius `σ`. Summing over `τ ∈ H_n = {τ : n | ord(τ)}`,

  δ_inf,K({𝔭 : σ_𝔭 = σ}) ≥ |H_n| / (|G| · |H|).

As `m` varies (chosen via Dirichlet's theorem to satisfy `m ≡ 1 mod n^k` for
large `k`), `|H_n|/|H| → 1`, so `δ_inf ≥ 1/|G|`. Summing over `σ ∈ G` then
forces equality.

## Main results

* `Chebotarev.chebotarev_abelian` — the density of primes
  of `K` unramified in an abelian extension `L/K` with Frobenius equal to
  `σ` is `1/|Gal(L/K)|`.

## References

* Sharifi, *Algebraic Number Theory*, §7.2.2 Step 2 (`docs/algnum.pdf`,
  pp. 143–144).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix
  paragraph 4 (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open NumberField Filter Topology

namespace Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! ### Sub-lemmas for `chebotarev_abelian`

Decomposed per Sharifi 7.2.2 Step 2 (p. 143–144). Source quote
(verbatim, p. 143):

> "Choose m ≥ 1 not dividing the discriminant of L so that H =
> Gal(L(μ_m)/L) is isomorphic to (ℤ/mℤ)^× via the mod m cyclotomic
> character, and Gal(L(μ_m)/K) ≅ G × H. For σ ∈ G and τ ∈ H, let S_σ be
> the set of primes of K unramified in L with Frobenius σ in G, and let
> S_{σ,τ} be the set of primes of K unramified in L(μ_m) with Frobenius
> (σ,τ) ∈ G × H. Then δ_inf(S_σ) = Σ_{τ∈H} δ_inf(S_{σ,τ})."

And (p. 144):
> "Now suppose that |G| divides the order of τ. Then ⟨(σ,τ)⟩ ∩ (G × {1})
> = 1, which implies that L(μ_m) is given by adjoining μ_m to F =
> K(μ_m)^⟨(σ,τ)⟩."
>
> "[…] δ(S_{σ,τ}) exists and equals 1/|G||H|."
>
> "|H_n|/|H| = ∏_{i=1}^r (1 - p_i^{k_i-1}/p_i^{j_i k_i}) ≥ ∏_{i=1}^r
> (1 - 1/p^{(j-1)k_i + 1}) so |H_n|/|H| tends to 1 as j increases."

Five sub-lemmas (mirror Sharifi's structure):
-/

/-- Sharifi 7.2.2 Step 2 sub-lemma (i) — cyclic subgroup trivial meet
(p. 144). Source quote: "if `|G|` divides the order of `τ`, then
`⟨(σ,τ)⟩ ∩ (G × {1}) = 1`". Stated in generalised form: no finiteness on
`G`/`H`, and the hypothesis is the weaker `orderOf σ ∣ orderOf τ` (the project's
`|G| ∣ ord τ` Step-2 usage recovers it via `orderOf σ ∣ Nat.card G`). -/
theorem cyclic_subgroup_meets_G_times_one_trivially
    (G H : Type*) [Group G] [Group H] (σ : G) (τ : H)
    (hn : orderOf σ ∣ orderOf τ) :
    (Subgroup.zpowers (σ, τ)) ⊓
        ((⊤ : Subgroup G).prod (⊥ : Subgroup H)) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, h⟩ hmem
  rw [Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_bot] at hmem
  obtain ⟨⟨k, hk⟩, _, (hh : h = 1)⟩ := hmem
  have h2 : τ ^ k = 1 := by simpa [hh] using congrArg Prod.snd hk
  have hg2 : σ ^ k = 1 := orderOf_dvd_iff_zpow_eq_one.mp
    (hn.natCast.trans (orderOf_dvd_iff_zpow_eq_one.mpr h2))
  rw [Subgroup.mem_bot, Prod.mk_eq_one]
  exact ⟨by simpa [hg2] using (congrArg Prod.fst hk).symm, hh⟩

/-- The Dirichlet density of a finite pairwise-disjoint union of sets, each of the
*same* density `c`, is `|t| • c`. Used to sum the `|H_n|` equal cyclotomic-crossing fibre
densities `1/(|G|·|H|)` in `liminf_density_S_sigma_ge_card_H_n_div_GH`. -/
private theorem hasDirichletDensity_biUnion_const {F : Type*} [Field F] [NumberField F]
    {ι : Type*} (t : Finset ι) (S : ι → Set (Ideal (𝓞 F))) (c : ℝ)
    (hdisj : (t : Set ι).PairwiseDisjoint S)
    (hdens : ∀ i ∈ t, HasDirichletDensity (S i) c) :
    HasDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using hasDirichletDensity_empty (K := F)
  | insert a t ha ih =>
      have hdisj' : (t : Set ι).PairwiseDisjoint S :=
        hdisj.subset (Finset.coe_subset.mpr (Finset.subset_insert a t))
      have hdisjUnion : Disjoint (S a) (⋃ i ∈ t, S i) :=
        Set.disjoint_iUnion₂_right.2 fun i hi ↦
          hdisj (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi) fun h ↦ ha (h ▸ hi)
      have hbase := hdens a (Finset.mem_insert_self a t)
      have hrec := ih hdisj' fun i hi ↦ hdens i (Finset.mem_insert_of_mem hi)
      have hcard : ((insert a t).card : ℝ) • c = c + (t.card : ℝ) • c := by
        rw [Finset.card_insert_of_notMem ha]; push_cast; ring
      rw [Finset.set_biUnion_insert, hcard]
      exact hbase.union_of_disjoint hdisjUnion hrec

/-! ### Cyclotomic-crossing core `exists_cyclotomicCrossing_fibres` (Sharifi 7.2.2 Step 2)

Sharifi 7.2.2 Step 2 cyclotomic-crossing core (p. 144). For `m ≥ 1` and `σ ∈ G`,
there is a family of prime sets `S_{σ,τ}` of `K` indexed by `τ ∈ H_n(m) =
{τ : (ℤ/mℤ)ˣ // |G| ∣ ord τ}`, pairwise disjoint, each contained in the Frobenius
fibre `S_σ`, and each of Dirichlet density exactly `1/(|G|·|H(m)|)` (with
`H(m) = (ℤ/mℤ)ˣ`).
This is the substantive geometric content of the crossing: introduce the compositum
`M = L(μ_m)` (`Gal(M/K) ≅ G × H` via the mod-`m` cyclotomic character, valid since `m`
coprime to `disc L` makes `L` and `K(μ_m)` linearly disjoint over `K`). For each such
`τ`, the subgroup `⟨(σ,τ)⟩` meets `G × {1}` trivially
(`cyclic_subgroup_meets_G_times_one_trivially`), so `M = F(μ_m)` with
`F = K(μ_m)^{⟨(σ,τ)⟩}`, making `M/F` cyclotomic; `chebotarev_cyclotomic` applied to
`M/F` at `(σ,τ)` together with the Step-1 cyclic reduction through `F/K` gives a set
`S_{σ,τ}` of primes of `K` with `Gal(M/K)`-Frobenius `(σ,τ)` of density
`1/(|G|·|H|)`. Such primes have `Gal(L/K)`-Frobenius the `G`-projection `σ`, so
`S_{σ,τ} ⊆ S_σ`; distinct `τ` give disjoint sets.

This existence statement packages the compositum infrastructure (`Gal(L(μ_m)/K) ≅ G × H`
and the density transfer `F/K`); the `liminf` lower bound
`liminf_density_S_sigma_ge_card_H_n_div_GH` is assembled around it.

**Hypotheses.** The crossing is only valid at *admissible* `m`:
* `hcop : ((NumberField.discr L).natAbs).Coprime m` — coprimality of `m` to the
  discriminant of `L` is exactly what makes `L` and `K(μ_m)` linearly disjoint over `K`
  (`[K(μ_m):K] = φ(m)` and `Gal(L(μ_m)/K) ≅ G × (ZMod m)ˣ`): the intersection
  `L ∩ K(μ_m)` is unramified everywhere over `K` — the `K`-side via
  `NumberField.discr_dvd_discr` (a prime ramifying in `K(μ_m)` divides `m`, hence not
  `disc L`) and the `L`-side dually — so it is `K` itself (Minkowski).
* `hm4 : m % 4 ≠ 2` — fed verbatim into the downstream `chebotarev_cyclotomic` application
  (its `B2`-repaired signature carries this hypothesis ruling out the degenerate
  `m ≡ 2 mod 4` cyclotomic field).
As stated with `∀ m ≥ 1` the conclusion is false/unprovable at degenerate `m`; the
consumer `liminf_ratio_ge_inv_card_G` chooses `m` prime with `m ≡ 1 mod 4·|G|^k`, which
secures both hypotheses (`m % 4 = 1`; a prime exceeding `|disc L|` is coprime to it). -/
/-! #### Internal decomposition of `exists_cyclotomicCrossing_fibres`

The crossing's geometric content is isolated in the *tagged-family* master leaf
`exists_crossing_family_tagged` below: it produces the per-`τ` fibre sets `S_{σ,τ}` of `K`
*together with a single global tag* `t : Ideal (𝓞 K) → (ℤ/mℤ)ˣ` recording the
`H`-component of each prime's `Gal(M/K) = G × H`-Frobenius. The tag makes distinct-`τ` fibres
disjoint (a prime has one well-defined `M`-Frobenius), so `exists_cyclotomicCrossing_fibres`
reduces to that master leaf by a generic *distinct-tags ⟹ pairwise-disjoint* argument
(`pairwiseDisjoint_of_tag`), with no further geometry.

The master leaf is in turn intended to be discharged from the following five TRUE
infrastructure leaves (Sharifi 7.2.2 Step 2, p. 144), each independently attackable and
stated against the compositum `M = L(μ_m)` (carrier `CyclotomicField m L` with its
`K`-algebra/scalar-tower structure). They are pinned here as the decomposition targets:

* `cyclotomicField_finrank_eq` (C2a) — `[K(μ_m):K] = φ(m)` from `hcop` (the deep
  ramification/Minkowski input: a prime ramifying in `K(μ_m)` divides `m`, hence is coprime
  to `disc L`, so `K ∩ L = K` and `Gal(K(μ_m)/K) ≅ (ℤ/mℤ)ˣ` has full order `φ(m)`).
* `compositum_charProd_bijective` / `autToPow_L_bijective` (C1) — the `G × H` splitting
  `Gal(M/K) ≅ Gal(L/K) × (ℤ/mℤ)ˣ` via the restriction-pair and the mod-`m` cyclotomic
  character (uses the linear-disjointness degree count C2a / `hcop`).
* `compositum_isCyclotomic_over_fixedField` (C3) — for any `g ∈ Gal(M/K)` the fixed field
  `F = M^⟨g⟩` has `M/F` cyclotomic; applied at `g = (σ,τ)`, where the trivial meet
  `⟨(σ,τ)⟩ ∩ (G × {1}) = 1` (`cyclic_subgroup_meets_G_times_one_trivially`, needs
  `|G| ∣ ord τ`) gives `M = F(μ_m)`. **Gate-fix (2026-06-07):** the Lean encoding of
  `G × {1} = Gal(M/K(μ_m))` is `(IntermediateField.adjoin K {b | b^m=1}).fixingSubgroup`, NOT
  `ker(restrictNormalHom L)` (which is `{1} × H = Gal(M/L)`); see the C3 docstring for the
  necessity/sufficiency argument. The master leaf must supply the corrected gate.
* `frobeniusClass_proj` (C4) — a prime with `Gal(M/K)`-Frobenius `(σ,τ)` has
  `Gal(L/K)`-Frobenius the projection `σ` (restriction-compatibility of `frobeniusClass`,
  the `M/L/K`-tower analogue of `Main.arithFrobAt_restrictScalars_eq`; replicated in
  `Abelian` because `Main` imports `Abelian`).
* `density_lift_through_fixedField_repl` (C5) — the Step-1 cyclic density transfer through
  `F/K`, applied to `M/F` (so `chebotarev_cyclotomic` at `M/F` and `(σ,τ)`, density
  `1/|Gal(M/F)|` of primes of `F`, lifts to density `1/(|G|·|H|)` of primes of `K`). The
  shared lemma `density_lift_through_fixedField` (with its Step-1 dependency block) now lives in
  `CebotarevDensity.FixedFieldDensity`, a common ancestor of both `Abelian` and `Main`, so C5 is
  a one-line application at `L ↦ M`. `hm4` threads into the `chebotarev_cyclotomic` application;
  `hcop` threads into C1/C2a. -/

/-- Generic disjointness from a global tag: if every member of `S i` carries the same tag
`f i` under a single function `t`, and `f` is injective, the family `S` is pairwise disjoint.
Used to derive `exists_cyclotomicCrossing_fibres` from the tagged master leaf
`exists_crossing_family_tagged`. -/
private theorem pairwiseDisjoint_of_tag {α ι κ : Type*} (t : α → κ) (f : ι → κ)
    (hf : Function.Injective f) (S : ι → Set α) (htag : ∀ i, ∀ a ∈ S i, t a = f i) :
    (Set.univ : Set ι).PairwiseDisjoint S := by
  intro i _ j _ hij
  simp only [Function.onFun, Set.disjoint_left]
  intro a hi hj
  exact hij (hf ((htag i a hi).symm.trans (htag j a hj)))

/-! #### Infrastructure leaves for `exists_crossing_family_tagged` (C1–C5)

The five TRUE, independently-attackable leaves the master leaf composes (Sharifi 7.2.2 Step 2,
p. 144), stated against the compositum `M = L(μ_m)`. Recommended carrier: `CyclotomicField m L`
(it carries `[IsCyclotomicExtension {m} L M]`, `[NumberField M]`, `[FiniteDimensional L M]`
automatically; its `K`-algebra/scalar-tower structure comes from `RingHom.comp` /
`IsScalarTower.of_algebraMap_eq`). The leaves below abstract `M` as a hypothesis with the
relevant instance binders so they do not depend on that carrier choice. -/

/-- **C2a-ramif — primes ramifying in a rational cyclotomic field divide `m`.** A prime `p`
dividing the discriminant of an `{m}`-cyclotomic extension `E/ℚ` necessarily divides `m`: for
`p ∤ m` every prime `P` of `𝓞 E` lying over `p` is unramified
(`IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd` gives `e = 1`, lifted to
`Algebra.IsUnramifiedAt` via `isUnramifiedAt_iff_of_isDedekindDomain`), so by
`not_dvd_discr_iff_forall_liesOver` we get `p ∤ discr E`. -/
private theorem prime_dvd_natAbs_discr_cyclotomic_dvd
    (E : Type*) [Field E] [NumberField E] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} ℚ E]
    {p : ℕ} (hp : p.Prime) (hpd : p ∣ (NumberField.discr E).natAbs) : p ∣ m := by
  by_contra hpm
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  refine absurd (Int.ofNat_dvd_left.mpr hpd) ?_
  rw [NumberField.not_dvd_discr_iff_forall_liesOver E (𝓞 E) hpprime]
  intro P hPmax hlo
  haveI := hPmax.isPrime
  haveI := hlo
  have hspanbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hpprime.ne_zero
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspanbot P
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ) (S := 𝓞 E) hPbot, hlo.over.symm]
  rw [Ideal.ramificationIdx_eq_ramificationIdx' _ P hspanbot]
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p E P hpm

/-- **C2a — cyclotomic degree over the base** (the deep ramification/Minkowski leaf). Source
(Sharifi p. 144): "Choose `m` not dividing the discriminant of `L` so that
`H = Gal(L(μ_m)/L) ≅ (ℤ/mℤ)ˣ` … and `Gal(L(μ_m)/K) ≅ G × H`." The full order `φ(m)`
of `H = (ℤ/mℤ)ˣ` is exactly `[K(μ_m):K] = φ(m)`, equivalently irreducibility of the `m`-th
cyclotomic polynomial over `K`; this holds because `m` is coprime to `disc L` (`hcop`): a
prime ramifying in `K(μ_m)` divides `m`, hence does not divide `disc L`, so `K ∩ L` is
unramified everywhere over `K` and equals `K` (Minkowski / `NumberField.discr_dvd_discr`),
giving linear disjointness of `L` and `K(μ_m)`. -/
private theorem cyclotomicField_finrank_eq
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M]
    (hcop : ((NumberField.discr K).natAbs).Coprime m) :
    Module.finrank K M = m.totient := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) K M
    (Set.mem_singleton m) (NeZero.ne m)
  set K₁ : IntermediateField ℚ M := IntermediateField.adjoin ℚ {ζ} with hK₁def
  set K₂ : IntermediateField ℚ M := (IsScalarTower.toAlgHom ℚ K M).fieldRange with hK₂def
  haveI hK₁cyc : IsCyclotomicExtension {m} ℚ K₁ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ)
  haveI : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois (S := {m}) (K := ℚ) (L := K₁)
  have hfinK₁ : Module.finrank ℚ K₁ = m.totient :=
    IsCyclotomicExtension.finrank K₁ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  have hsup : K₁ ⊔ K₂ = ⊤ := by
    have hζalg : IsAlgebraic ℚ ζ := Algebra.IsAlgebraic.isAlgebraic ζ
    have hsubalg : (IsScalarTower.toAlgHom ℚ K M).range ⊔ Algebra.adjoin ℚ {ζ}
        = (⊤ : Subalgebra ℚ M) := by
      have htop : (Algebra.adjoin K {ζ} : Subalgebra K M) = ⊤ :=
        IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ
      rw [← Algebra.Subalgebra.restrictScalars_adjoin (R := ℚ) (S := K) (s := {ζ}), htop,
        Subalgebra.restrictScalars_top]
    apply IntermediateField.toSubalgebra_injective
    rw [hK₁def, hK₂def, IntermediateField.sup_toSubalgebra_of_isAlgebraic_left,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg,
      AlgHom.fieldRange_toSubalgebra, IntermediateField.top_toSubalgebra, sup_comm]
    exact hsubalg
  let eK₂ : K ≃+* K₂ := ((IsScalarTower.toAlgHom ℚ K M : K →+* M)).rangeRestrictFieldEquiv
  have hdiscrK₂ : NumberField.discr K₂ = NumberField.discr K :=
    (NumberField.discr_eq_discr_of_ringEquiv (f := eK₂)).symm
  have hcoprime : IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
    rw [hdiscrK₂, Int.isCoprime_iff_gcd_eq_one, Int.gcd]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    rw [Nat.dvd_gcd_iff] at hpdvd
    obtain ⟨hpa, hpb⟩ := hpdvd
    have hpm : p ∣ m := prime_dvd_natAbs_discr_cyclotomic_dvd K₁ m hp hpa
    have hpgcd : p ∣ Nat.gcd (NumberField.discr K).natAbs m := Nat.dvd_gcd hpb hpm
    rw [hcop] at hpgcd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpgcd)
  have hld : K₁.LinearDisjoint K₂ :=
    NumberField.linearDisjoint_of_isGalois_isCoprime_discr (L := M) K₁ K₂ hcoprime
  have hfr : Module.finrank K₂ M = Module.finrank ℚ K₁ :=
    hld.finrank_right_eq_finrank hsup
  have hrelabel : Module.finrank K M = Module.finrank K₂ M := by
    refine Algebra.finrank_eq_of_equiv_equiv eK₂ (RingEquiv.refl M) ?_
    ext x
    change ((eK₂ x : M)) = (IsScalarTower.toAlgHom ℚ K M : K →+* M) x
    rfl
  rw [hrelabel, hfr, hfinK₁]

/-- **Joint-restriction bijectivity** — the analytic heart of C1, exposed with the explicit
primitive root `ζ` so that callers (C1 and the master leaf) can read off the two components.
The map `Φ = (restrictNormalHom L).prod (autToPow K hζ) : Gal(M/K) →* Gal(L/K) × (ℤ/mℤ)ˣ` is
bijective: injective because an automorphism trivial on `L` and fixing `ζ` is trivial on
`M = L(ζ)`; surjective by the degree count `[M:K] = [L:K]·φ(m) = [L:K]·[M:L]`
(`cyclotomicField_finrank_eq` at base `L`, hence `hcop`). -/
private theorem compositum_charProd_bijective
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (hcop : ((NumberField.discr L).natAbs).Coprime m) (ζ : M) (hζ : IsPrimitiveRoot ζ m) :
    Function.Bijective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K)) := by
  haveI : FiniteDimensional K M := inferInstance
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  set χK : Gal(M/K) →* (ZMod m)ˣ := hζ.autToPow K with hχK
  set Φ : Gal(M/K) →* Gal(L/K) × (ZMod m)ˣ :=
    (AlgEquiv.restrictNormalHom L).prod χK with hΦ
  have hML : Module.finrank L M = m.totient := cyclotomicField_finrank_eq L M m hcop
  have hcardMK : Nat.card Gal(M/K) = Nat.card Gal(L/K) * Nat.card (ZMod m)ˣ := by
    rw [IsGalois.card_aut_eq_finrank K M, IsGalois.card_aut_eq_finrank K L,
      ← Module.finrank_mul_finrank K L M, hML, Nat.card_eq_fintype_card (α := (ZMod m)ˣ),
      ZMod.card_units_eq_totient]
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    rw [hΦ, MonoidHom.prod_apply, Prod.mk_eq_one] at hσ
    obtain ⟨hσL, hσζ⟩ := hσ
    have hζfix : σ ζ = ζ := by
      have hspec := hζ.autToPow_spec K σ
      rw [hχK] at hσζ
      rw [hσζ] at hspec
      rw [← hspec, Units.val_one]
      rcases eq_or_lt_of_le (NeZero.one_le (n := m)) with h1 | h1
      · have hm1 : m = 1 := h1.symm
        subst hm1
        have : ζ = 1 := by simpa using hζ.pow_eq_one
        simp [this]
      · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by lia), pow_one]
    have hLfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
      intro x
      have hcomm := σ.restrictNormal_commutes L x
      have hrn : σ.restrictNormal L = (1 : Gal(L/K)) := hσL
      rw [hrn] at hcomm
      simpa using hcomm.symm
    have htop : Algebra.adjoin L {ζ} = (⊤ : Subalgebra L M) :=
      IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ Algebra.adjoin L {ζ} := htop ▸ Algebra.mem_top
    refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
    · intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; rw [hζfix]; rfl
    · intro r; exact hLfix r
    · intro a b _ _ ha hb; rw [map_add, ha, hb]; rfl
    · intro a b _ _ ha hb; rw [map_mul, ha, hb]; rfl
  exact (Nat.bijective_iff_injective_and_card _).mpr ⟨hΦinj, by rw [hcardMK, Nat.card_prod]⟩

/-- **The cyclotomic character `autToPow L : Gal(M/L) → (ℤ/mℤ)ˣ` is a bijection.** Faithful
(`autToPow_injective`) and surjective by `|Gal(M/L)| = [M:L] = φ(m) = |(ℤ/mℤ)ˣ|`
(`cyclotomicField_finrank_eq` at base `L`). This is the `H ≅ (ℤ/mℤ)ˣ` half of C1's `G × H`
splitting; the master leaf uses its inverse to turn an admissible residue `τ` into the
`Gal(M/L)`-component of the compositum Frobenius. -/
private theorem autToPow_L_bijective
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (hcop : ((NumberField.discr L).natAbs).Coprime m) (ζ : M) (hζ : IsPrimitiveRoot ζ m) :
    Function.Bijective (hζ.autToPow L) := by
  haveI : FiniteDimensional K M := inferInstance
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have hML : Module.finrank L M = m.totient := cyclotomicField_finrank_eq L M m hcop
  have hcardML : Nat.card Gal(M/L) = Nat.card (ZMod m)ˣ := by
    rw [IsGalois.card_aut_eq_finrank L M, hML, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient]
  exact (Nat.bijective_iff_injective_and_card _).mpr ⟨hζ.autToPow_injective L, hcardML⟩

/-- **C3 — the compositum is cyclotomic over the `(σ,τ)`-fixed field** (Sharifi p. 144):
"… `L(μ_m)` is given by adjoining `μ_m` to `F = K(μ_m)^⟨(σ,τ)⟩`", i.e. `M = F(μ_m)`.
Stated for `g ∈ Gal(M/K)` and `F = M^⟨g⟩`: then `M/F` is the `m`-th cyclotomic extension.

**Gate correction (statement-fix, 2026-06-07).** The decomposition originally gated this leaf
by `⟨g⟩ ⊓ ker(restrictNormalHom L) = ⊥`. That is FALSE-as-stated: `ker(restrictNormalHom L)`
is `Gal(M/L) = {1} × H` (the `L`-fixers), whereas Sharifi's `⟨(σ,τ)⟩ ∩ (G × {1}) = 1` is about
`G × {1} = Gal(M/K(μ_m))`, the `μ_m`-fixers. Concretely with `g = (σ,τ)`: the *stated* meet
`⟨g⟩ ⊓ ({1}×H)` is trivial iff `ord τ ∣ ord σ`, which `|G| ∣ ord τ` does NOT give; the
*correct* meet `⟨g⟩ ⊓ (G×{1})` is trivial iff `ord σ ∣ ord τ`, which `ord σ ∣ |G| ∣ ord τ`
DOES give (matching `cyclic_subgroup_meets_G_times_one_trivially`). Moreover `M = F(μ_m)`
needs exactly `⟨g⟩ ⊓ Gal(M/K(μ_m)) = ⊥` (it is necessary and sufficient: `M = F ⊔ K(μ_m)`
⟺ `fixingSubgroup(F ⊔ K(μ_m)) = ⊥` ⟺ `⟨g⟩ ⊓ K(μ_m).fixingSubgroup = ⊥`). The hypothesis is
therefore corrected to `⟨g⟩ ⊓ (adjoin K μ_m).fixingSubgroup = ⊥`, where
`adjoin K {b | b^m = 1} = K(μ_m)` is the cyclotomic subfield (its fixing subgroup is
`Gal(M/K(μ_m)) = G × {1}`). The master-leaf assembly (`exists_crossing_family_tagged`) must
supply this corrected gate at `g = (σ,τ)`: from `|G| ∣ ord τ` via
`cyclic_subgroup_meets_G_times_one_trivially` transported across the `Gal(M/K) ≅ G × H`
splitting (C1) so that `G × {1}` is identified with `(adjoin K μ_m).fixingSubgroup`.

Proof: a primitive root `ζ ∈ M` exists (from `[IsCyclotomicExtension {m} L M]`);
`adjoin K {ζ} = adjoin K {b | b^m=1} = K(μ_m)`; the corrected meet gives `F ⊔ K(μ_m) = ⊤`
(`fixingSubgroup_sup` + `fixingSubgroup_fixedField` + the Galois correspondence
`fixedField_fixingSubgroup`); hence `adjoin F {ζ} = ⊤` over `F` (`restrictScalars_adjoin_eq_sup`),
and `adjoin F {ζ}` is `{m}`-cyclotomic over `F`
(`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`), transported to `M` along
`adjoin F {ζ} = ⊤ ≃ₐ M` (`IsCyclotomicExtension.equiv`, `IntermediateField.topEquiv`).
`[IsCyclotomicExtension {m} L M]` guarantees `μ_m ⊆ M` so the adjunction makes sense. -/
private theorem compositum_isCyclotomic_over_fixedField
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (g : Gal(M/K))
    (_hmeet : Subgroup.zpowers g ⊓
      (IntermediateField.adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥) :
    letI := (IntermediateField.fixedField (Subgroup.zpowers g)).isScalarTower_mid'
    IsCyclotomicExtension {m} ↥(IntermediateField.fixedField (Subgroup.zpowers g)) M := by
  set F : IntermediateField K M := IntermediateField.fixedField (Subgroup.zpowers g)
  set Kμ : IntermediateField K M := IntermediateField.adjoin K {b : M | b ^ m = 1}
  obtain ⟨ζ, hζ⟩ : ∃ r : M, IsPrimitiveRoot r m :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M (Set.mem_singleton m) (NeZero.ne m)
  have hadjζ : IntermediateField.adjoin K {ζ} = Kμ :=
    le_antisymm
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
        (IntermediateField.subset_adjoin K _ hζ.pow_eq_one)))
      (IntermediateField.adjoin_le_iff.mpr fun x hx ↦ by
        obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one (Set.mem_setOf_eq ▸ hx)
        exact pow_mem (IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)) i)
  have hsup : (F ⊔ Kμ).fixingSubgroup = ⊥ := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField, _hmeet]
  have htop : F ⊔ Kμ = ⊤ := by
    have := congrArg IntermediateField.fixedField hsup
    rwa [IsGalois.fixedField_fixingSubgroup, IntermediateField.fixedField_bot] at this
  have htopF : IntermediateField.adjoin (↥F) {ζ} = ⊤ := by
    apply IntermediateField.restrictScalars_injective K
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, hadjζ, htop]
    rfl
  haveI : Algebra.IsIntegral ↥F M := Algebra.IsIntegral.of_finite ↥F M
  haveI hcyc : IsCyclotomicExtension {m} ↥F (IntermediateField.adjoin (↥F) {ζ}) :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := ↥F) hζ
  rw [htopF] at hcyc
  exact IsCyclotomicExtension.equiv (S := {m}) (A := ↥F) (f := IntermediateField.topEquiv)

/-- **Action intertwining for the downward normal restriction** (replica of
`CyclotomicNormResidue.smul_algebraMap_eq`, adapted to the abstract tower `K ⊆ L ⊆ M` with
`M` on top). The embedding `𝓞 L → 𝓞 M` intertwines the action of `σ : Gal(M/K)` with that of
its normal restriction `σ ↾ L : Gal(L/K)`:
`σ • algebraMap (𝓞 L) (𝓞 M) y = algebraMap (𝓞 L) (𝓞 M) (σ↾L • y)`. The CNR original is
`private`, hence unreachable here; replicated `_repl`. -/
private theorem smul_algebraMap_eq_repl
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (σ : Gal(M/K)) (y : 𝓞 L) :
    σ • (algebraMap (𝓞 L) (𝓞 M) y) = algebraMap (𝓞 L) (𝓞 M) ((σ.restrictNormal L) • y) := by
  haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
  have hbridgeM : ∀ (g : M ≃ₐ[K] M) (x : 𝓞 M), ((g • x : 𝓞 M) : M) = g • (x : M) := fun g x ↦
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := M ≃ₐ[K] M) (R := 𝓞 M) (S := M) g x 1).symm
  have hbridgeL : ∀ (g : L ≃ₐ[K] L) (z : 𝓞 L), ((g • z : 𝓞 L) : L) = g • ((z : L)) := fun g z ↦
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := L ≃ₐ[K] L) (R := 𝓞 L) (S := L) g z 1).symm
  have hcoe : ∀ z : 𝓞 L, ((algebraMap (𝓞 L) (𝓞 M) z : 𝓞 M) : M) = algebraMap L M (z : L) :=
    fun z ↦ by
      rw [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 M) M,
        RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 L) L M]
  rw [RingOfIntegers.ext_iff, hbridgeM, hcoe y, hcoe ((σ.restrictNormal L) • y), hbridgeL,
    AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes]

/-- **Downward Frobenius restriction** (replica of
`CyclotomicNormResidue.isArithFrobAt_restrictNormal`
for the tower `K ⊆ L ⊆ M`). If `σ : Gal(M/K)` is an arithmetic Frobenius at a prime `𝔓` of `𝓞 M`,
its normal restriction `σ ↾ L` is an arithmetic Frobenius at `𝔮 = 𝔓 ∩ 𝓞 L`. The defining
congruence descends along `𝓞 L → 𝓞 M` via `smul_algebraMap_eq_repl` and `Ideal.under_under`. -/
private theorem isArithFrobAt_restrictNormal_repl
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (σ : Gal(M/K)) (𝔓 : Ideal (𝓞 M))
    (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    IsArithFrobAt (𝓞 K) (σ.restrictNormal L) (𝔓.under (𝓞 L)) := by
  haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
  have hunder : (𝔓.under (𝓞 L)).under (𝓞 K) = 𝔓.under (𝓞 K) := Ideal.under_under 𝔓
  intro y
  rw [hunder, Ideal.under, Ideal.mem_comap, map_sub, map_pow,
    MulSemiringAction.toAlgHom_apply, ← smul_algebraMap_eq_repl K L M σ y]
  exact hσ (algebraMap (𝓞 L) (𝓞 M) y)

private theorem frobeniusClass_proj_isPrime_aux
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M]
    (σ : Gal(L/K)) (τM : Gal(M/K)) (_hτM : AlgEquiv.restrictNormalHom L τM = σ)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (_hunrM : UnramifiedIn K M 𝔭) (_hunrL : UnramifiedIn K L 𝔭)
    (_hfr : frobeniusClass K M 𝔭 = ConjClasses.mk τM) :
    frobeniusClass K L 𝔭 = ConjClasses.mk σ := by
  obtain ⟨𝔓, h𝔓p, h𝔓lo, -⟩ := exists_prime_liesOver K M 𝔭 (UnramifiedIn.ne_bot K M _hunrM)
  haveI := h𝔓p
  haveI := h𝔓lo
  haveI : Finite (𝓞 M ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
    (ne_bot_of_ramificationIdx_eq_one K M (UnramifiedIn.ramificationIdx_eq_one K M _hunrM 𝔓 h𝔓lo))
  set σM : Gal(M/K) := arithFrobAt (𝓞 K) Gal(M/K) 𝔓
  have hMfrobσM : IsArithFrobAt (𝓞 K) σM 𝔓 := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(M/K) 𝔓
  have hconjM : IsConj σM τM := ConjClasses.mk_eq_mk_iff_isConj.mp
    ((frobeniusClass_eq_mk_of_isArithFrobAt K M 𝔭 _hunrM σM 𝔓 hMfrobσM h𝔓lo).symm.trans _hfr)
  haveI : (𝔓.under (𝓞 L)).IsPrime := Ideal.IsPrime.under (𝓞 L) 𝔓
  haveI : (𝔓.under (𝓞 L)).LiesOver 𝔭 := ⟨((Ideal.under_under 𝔓).trans h𝔓lo.over.symm).symm⟩
  rw [frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 _hunrL (σM.restrictNormal L) (𝔓.under (𝓞 L))
    (isArithFrobAt_restrictNormal_repl K L M σM 𝔓 hMfrobσM) inferInstance]
  refine ConjClasses.mk_eq_mk_iff_isConj.mpr ?_
  have hconjL := MonoidHom.map_isConj (AlgEquiv.restrictNormalHom L) hconjM
  rwa [_hτM] at hconjL

/-- **C4 — Frobenius projects along the compositum tower** `M/L/K`. A prime `𝔭` of `K`
unramified in `M` (hence in `L`) whose `Gal(M/K)`-Frobenius class is `(σ,τ)` — i.e. equal to
`ConjClasses.mk τM` for `τM` restricting to `σ` over `L` — has `Gal(L/K)`-Frobenius class `σ`.
This is the restriction-compatibility of `frobeniusClass` along `K ⊆ L ⊆ M`, the tower
analogue of `Main.arithFrobAt_restrictScalars_eq` (replicated in `Abelian` because `Main`
imports `Abelian`). It is what makes each crossing fibre `S_{σ,τ}` land inside the
`σ`-Frobenius fibre `S_σ`. -/
private theorem frobeniusClass_proj
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M]
    (σ : Gal(L/K)) (τM : Gal(M/K)) (_hτM : AlgEquiv.restrictNormalHom L τM = σ)
    (𝔭 : Ideal (𝓞 K)) (_hunrM : UnramifiedIn K M 𝔭) (_hunrL : UnramifiedIn K L 𝔭)
    (_hfr : frobeniusClass K M 𝔭 = ConjClasses.mk τM) :
    frobeniusClass K L 𝔭 = ConjClasses.mk σ := by
  by_cases hp : 𝔭.IsPrime
  · haveI := hp
    exact frobeniusClass_proj_isPrime_aux K L M σ τM _hτM 𝔭 _hunrM _hunrL _hfr
  · have hMjunk : frobeniusClass K M 𝔭 = ConjClasses.mk 1 := by
      rw [frobeniusClass, dif_neg fun h ↦ hp h.1]
    have hLjunk : frobeniusClass K L 𝔭 = ConjClasses.mk 1 := by
      rw [frobeniusClass, dif_neg fun h ↦ hp h.1]
    have hconj : IsConj (1 : Gal(M/K)) τM :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hMjunk.symm.trans _hfr)
    have hτM1 : τM = 1 := isConj_one_right.mp hconj
    have hσ1 : σ = 1 := by rw [← _hτM, hτM1, map_one]
    rw [hLjunk, hσ1]

/-- **C5 — density transfer through a fixed field** (Sharifi 7.2.2 Step 2 ⇒ Step 1 reuse,
p. 143–144). The Step-1 cyclic density transfer, restated with the top field `M` (the
compositum), so that the crossing can be assembled inside `Abelian`. Given `σM ∈ Gal(M/K)`, the
fixed field `E = M^⟨σM⟩`, a lift `σE` of `σM` to `Gal(M/E)`, and the cyclic-case density
`1/|Gal(M/E)|` of the `σE`-Frobenius fibre of `E`, the transfer yields density `|C|/|Gal(M/K)|`
of the `σM`-Frobenius fibre of `K`. In the crossing, `σM = (σ,τ)`, `E = F`, and
`chebotarev_cyclotomic` (at the cyclotomic `M/F`, valid by `hm4`) supplies the `_hab` input; the
resulting density is `1/(|G|·|H|)`.

**Resolution (relocation, 2026-06-07).** The proven Step-1 reduction
`density_lift_through_fixedField` and its ~18-declaration dependency block were *moved* out of
`Main.lean` into the new module `CebotarevDensity.FixedFieldDensity`, which sits strictly below
both `Main` (which re-imports it) and `Abelian` (the block is `chebotarev_abelian`-independent —
`Main`'s only use of `Abelian` is `chebotarev_abelian`, inside `chebotarev_density`, after all
the Step-1 helpers; so the block carries no `Abelian` dependency and no import cycle is created).
This leaf is now a one-line application of the shared lemma at `L ↦ M`, no longer a replica. -/
private theorem density_lift_through_fixedField_repl
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (σM : Gal(M/K)) (E : IntermediateField K M) (σE : Gal(M/E))
    (_hσE : letI : IsScalarTower K ↥E M := E.isScalarTower_mid'; σE.restrictScalars K = σM)
    (_hEfix : E = IntermediateField.fixedField (Subgroup.zpowers σM))
    (_hab : HasDirichletDensity
        {P : Ideal (𝓞 ↥E) | P.IsPrime ∧ UnramifiedIn ↥E M P ∧
          frobeniusClass ↥E M P = ConjClasses.mk σE}
        ((Nat.card Gal(M/E) : ℝ)⁻¹)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K M 𝔭 ∧
        frobeniusClass K M 𝔭 = ConjClasses.mk σM}
      ((Nat.card (ConjClasses.mk σM).carrier : ℝ) / Nat.card Gal(M/K)) :=
  density_lift_through_fixedField σM E σE _hσE _hEfix _hab

/-- **The compositum `M = L(μ_m)` is Galois over the base `K`.** For an abelian (indeed any)
Galois extension `L/K` of number fields and the `{m}`-cyclotomic extension `M/L`, the tower
`M/K` is Galois: it is separable (number-field base, characteristic zero) and normal because
`M = A ⊔ B` is the compositum of the (normal) image `A` of `L` and the (normal, cyclotomic)
subfield `B = K(μ_m) = adjoin K {ζ}` — both normal over `K`, so their join is normal
(`normal_sup`). Supplies the `[IsGalois K M]` binder demanded by C1/C3/C4/C5 at the carrier
`M = CyclotomicField m L`. -/
private theorem isGalois_compositum_base
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] (M : Type*) [Field M] [NumberField M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [IsCyclotomicExtension {m} L M] : IsGalois K M := by
  obtain ⟨ζ, hζ⟩ : ∃ r : M, IsPrimitiveRoot r m :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M (Set.mem_singleton m) (NeZero.ne m)
  haveI : FiniteDimensional K M := inferInstance
  haveI hsep : Algebra.IsSeparable K M := inferInstance
  set A : IntermediateField K M := (IsScalarTower.toAlgHom K L M).fieldRange with hA
  set B : IntermediateField K M := IntermediateField.adjoin K {ζ} with hB
  haveI hAnormal : Normal K A :=
    Normal.of_algEquiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L M))
  haveI hBcyc : IsCyclotomicExtension {m} K B :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := K)
  haveI hBgal : IsGalois K B := IsCyclotomicExtension.isGalois (S := {m}) (K := K) (L := B)
  haveI hBnormal : Normal K B := hBgal.to_normal
  have hsup : A ⊔ B = ⊤ := by
    have hζalg : IsAlgebraic K ζ := Algebra.IsAlgebraic.isAlgebraic ζ
    have hsubalg : (IsScalarTower.toAlgHom K L M).range ⊔ Algebra.adjoin K {ζ}
        = (⊤ : Subalgebra K M) := by
      have htop : (Algebra.adjoin L {ζ} : Subalgebra L M) = ⊤ :=
        IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ
      rw [← Algebra.Subalgebra.restrictScalars_adjoin (R := K) (S := L) (s := {ζ}), htop,
        Subalgebra.restrictScalars_top]
    apply IntermediateField.toSubalgebra_injective
    rw [hA, hB, IntermediateField.sup_toSubalgebra_of_isAlgebraic_left,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg,
      AlgHom.fieldRange_toSubalgebra, IntermediateField.top_toSubalgebra]
    exact hsubalg
  haveI hnormal : Normal K M := by
    have h := IntermediateField.normal_sup K M A B
    rw [hsup] at h
    exact Normal.of_algEquiv (IntermediateField.topEquiv (F := K) (E := M))
  exact IsGalois.mk

/-- **Unramifiedness descends to an intermediate field.** If a prime `𝔭` of `K` is unramified
in the top field `M` of a tower `K ⊆ L ⊆ M`, it is unramified in `L`: for a maximal prime `𝔮`
of `𝓞 L` over `𝔭`, pick a prime `𝔓` of `𝓞 M` over `𝔮`; then `e(𝔓/𝔭) = 1` (from the `M`-side
hypothesis) factors as `e(𝔮/𝔭)·e(𝔓/𝔮)` (`Ideal.ramificationIdx_algebra_tower`), forcing
`e(𝔮/𝔭) = 1`. Supplies C4's `_hunrL : UnramifiedIn K L 𝔭` input from `UnramifiedIn K M 𝔭`. -/
private theorem unramifiedIn_tower_descend
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K L] [IsGalois K M]
    (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K M 𝔭) : UnramifiedIn K L 𝔭 := by
  haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
  refine ⟨hunr.1, fun 𝔮 h𝔮max h𝔮lo ↦ ?_⟩
  haveI := h𝔮max
  haveI := h𝔮lo
  haveI h𝔮p : 𝔮.IsPrime := h𝔮max.isPrime
  have h𝔮bot : 𝔮 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔮
  obtain ⟨𝔓, _, h𝔓p, h𝔓comap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 M) 𝔮 ⊥ (by simp)
  haveI := h𝔓p
  haveI h𝔓lo𝔮 : 𝔓.LiesOver 𝔮 := ⟨h𝔓comap.symm⟩
  have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔮bot 𝔓
  haveI h𝔓max : 𝔓.IsMaximal := h𝔓p.isMaximal h𝔓bot
  have h𝔮under : Ideal.under (𝓞 L) 𝔓 = 𝔮 := h𝔓lo𝔮.over.symm
  have h𝔭under : Ideal.under (𝓞 K) 𝔮 = 𝔭 := h𝔮lo.over.symm
  haveI h𝔓lo𝔭 : 𝔓.LiesOver 𝔭 := ⟨by rw [← h𝔭under, ← h𝔮under, Ideal.under_under]⟩
  have hunderP : Ideal.under (𝓞 K) 𝔓 = 𝔭 := h𝔓lo𝔭.over.symm
  have hP1 : (Ideal.under (𝓞 K) 𝔓).ramificationIdx 𝔓 = 1 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 K) (S := 𝓞 M) h𝔓bot).mp
      (hunr.2 𝔓 h𝔓max h𝔓lo𝔭)
  rw [hunderP] at hP1
  have htower := Ideal.ramificationIdx_algebra_tower (R := 𝓞 K) (S := 𝓞 L) (T := 𝓞 M)
    (p := 𝔭) (P := 𝔮) (Q := 𝔓) (Ideal.map_ne_bot_of_ne_bot h𝔮bot)
    (Ideal.map_ne_bot_of_ne_bot hunr.1) (by rw [Ideal.map_le_iff_le_comap, h𝔓comap])
  rw [hP1] at htower
  have he𝔮 : 𝔭.ramificationIdx 𝔮 = 1 := Nat.eq_one_of_mul_eq_one_right htower.symm
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 K) (S := 𝓞 L) h𝔮bot, h𝔭under]
  exact he𝔮

/-- **An automorphism fixing a primitive root has trivial cyclotomic character.** If
`g : Gal(M/K)` fixes a primitive `m`-th root `ζ`, then `autToPow K hζ g = 1` (the character
records the power `g(ζ) = ζ^c`, here `c = 1`). No cyclotomic-over-`K` hypothesis is needed —
only `ζ`'s primitivity. Used in the master leaf to identify `K(μ_m).fixingSubgroup` with the
kernel of the cyclotomic character (the `G × {1}` factor of C1's splitting). -/
private theorem autToPow_eq_one_of_fixes
    (K M : Type*) [Field K] [Field M] [Algebra K M] (m : ℕ) [NeZero m]
    (ζ : M) (hζ : IsPrimitiveRoot ζ m) (g : Gal(M/K)) (hg : g ζ = ζ) :
    hζ.autToPow K g = 1 := by
  have hspec := hζ.autToPow_spec K g
  rw [hg] at hspec
  set u : (ZMod m)ˣ := hζ.autToPow K g with hu
  have hmod : (u : ZMod m).val ≡ 1 [MOD m] := by
    have hisu : IsUnit ζ := hζ.isUnit (NeZero.ne m)
    lift ζ to Mˣ using hisu with z hz
    have hzp : IsPrimitiveRoot z m := by rwa [IsPrimitiveRoot.coe_units_iff] at hζ
    have hord : orderOf z = m := (IsPrimitiveRoot.eq_orderOf hzp).symm
    have h' : z ^ (u : ZMod m).val = z ^ (1 : ℕ) := by
      apply Units.ext
      push_cast
      rwa [pow_one]
    rwa [pow_eq_pow_iff_modEq, hord] at h'
  have hu1 : (u : ZMod m) = 1 := by
    have hcast : ((u : ZMod m).val : ZMod m) = (1 : ZMod m) := by
      rw [← Nat.cast_one]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    rwa [ZMod.natCast_val, ZMod.cast_id] at hcast
  exact Units.ext hu1

/-- Concrete realisation of `cyclic_subgroup_meets_G_times_one_trivially` inside `Gal(M/K)`:
for `s` with `|G| ∣ ord τ`, restricting to `σ` over `L` and with cyclotomic character `τ`, the
cyclic subgroup `⟨s⟩` meets the fixing subgroup of `K(μ_m) = adjoin K {b | b ^ m = 1}` (the
`G × {1}` factor) trivially. The defining fact for `compositum_isCyclotomic_over_fixedField`
(C3) at `s = (σ, τ)`. -/
private theorem zpowers_inf_fixingSubgroup_eq_bot_aux
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K L] [IsGalois K M]
    (m : ℕ) [NeZero m] (ζ : M) (hζ : IsPrimitiveRoot ζ m) (σ : Gal(L/K)) (τ : (ZMod m)ˣ)
    (hτ : Nat.card Gal(L/K) ∣ orderOf τ) (s : Gal(M/K))
    (hsrestr : AlgEquiv.restrictNormalHom L s = σ) (hschar : hζ.autToPow K s = τ)
    (hΦbij : Function.Bijective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K))) :
    Subgroup.zpowers s ⊓
        (IntermediateField.adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥ := by
  rw [eq_bot_iff]
  rintro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨⟨k, hk⟩, hgfix⟩ := hg
  simp only at hk
  have hgζ : g ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ g).mp hgfix ζ <|
      IntermediateField.subset_adjoin K _ hζ.pow_eq_one
  have hχg : hζ.autToPow K g = 1 := autToPow_eq_one_of_fixes K M m ζ hζ g hgζ
  have hχgτ : τ ^ k = 1 := by
    rw [← hschar, ← map_zpow, hk]
    exact hχg
  have hGk : (Nat.card Gal(L/K) : ℤ) ∣ k :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hτ) (orderOf_dvd_iff_zpow_eq_one.mpr hχgτ)
  have hσk : σ ^ k = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp
      (dvd_trans (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard σ)) hGk)
  have hrestrg : AlgEquiv.restrictNormalHom L g = 1 := by rw [← hk, map_zpow, hsrestr, hσk]
  rw [Subgroup.mem_bot]
  apply hΦbij.injective
  rw [MonoidHom.prod_apply, MonoidHom.prod_apply, hrestrg, hχg, map_one, map_one]

/-- Per-`τ` density of the crossing fibre (Sharifi 7.2.2 Step 2, p. 144, density `1/(|G|·|H|)`).
For `s ∈ Gal(M/K)` whose cyclic group meets `Gal(M/K(μ_m))` trivially (so `M/F` is cyclotomic at
`F = M^⟨s⟩`), `chebotarev_cyclotomic` at `M/F` and `s`, lifted through `F/K` by
`density_lift_through_fixedField_repl` (C5), gives the `s`-Frobenius fibre of `K` density
`1/(|G|·|H|)` — using `|carrier| = 1` (commutativity) and `|Gal(M/K)| = |G|·φ(m)`. -/
private theorem density_crossing_fibre_aux
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K L] [IsGalois K M]
    [IsMulCommutative Gal(M/K)] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) (s : Gal(M/K))
    (hgate : Subgroup.zpowers s ⊓
      (IntermediateField.adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K M 𝔭 ∧
        frobeniusClass K M 𝔭 = ConjClasses.mk s}
      ((Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹) := by
  set F : IntermediateField K M := IntermediateField.fixedField (Subgroup.zpowers s) with hF
  haveI : IsScalarTower K ↥F M := F.isScalarTower_mid'
  haveI : IsCyclotomicExtension {m} ↥F M :=
    compositum_isCyclotomic_over_fixedField K L M m s hgate
  set σE : Gal(M/↥F) :=
    IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers s) ⟨s, Subgroup.mem_zpowers s⟩
  have hlift := density_lift_through_fixedField_repl K M s F σE
    (by ext x; rfl) rfl (chebotarev_cyclotomic (K := ↥F) (L := M) m hm4 σE)
  have hcarrier : Nat.card (ConjClasses.mk s).carrier = 1 := by
    letI : CommMonoid Gal(M/K) := IsMulCommutative.instCommMonoid
    have hcar : (ConjClasses.mk s).carrier = {s} := by
      ext a
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
        isConj_iff_eq, Set.mem_singleton_iff]
    rw [hcar, Nat.card_coe_set_eq, Set.ncard_singleton]
  have hcardMK : Nat.card Gal(M/K) = Nat.card Gal(L/K) * Nat.card (ZMod m)ˣ := by
    rw [IsGalois.card_aut_eq_finrank K M, IsGalois.card_aut_eq_finrank K L,
      ← Module.finrank_mul_finrank K L M, cyclotomicField_finrank_eq L M m hcop,
      Nat.card_eq_fintype_card (α := (ZMod m)ˣ), ZMod.card_units_eq_totient]
  rw [hcarrier, hcardMK] at hlift
  simpa using hlift

/-- **Cyclotomic-crossing tagged master leaf** (Sharifi 7.2.2 Step 2, p. 144). For admissible
`m` (`hm4 : m % 4 ≠ 2`, `hcop : (disc L).natAbs.Coprime m`) and `σ ∈ G = Gal(L/K)`, there is a
single global tag `t : Ideal (𝓞 K) → (ℤ/mℤ)ˣ` — the `H`-component of the prime's
`Gal(M/K) = G × H`-Frobenius, `M = L(μ_m)` — and a family of prime sets `S_{σ,τ}` indexed by
`τ ∈ H_n = {τ : |G| ∣ ord τ}` such that:
* each `S_{σ,τ}` lies in the `σ`-Frobenius fibre of `K` (`frobeniusClass_proj`, C4);
* every prime of `S_{σ,τ}` has tag exactly `τ` (its `M`-Frobenius `H`-component);
* each `S_{σ,τ}` has Dirichlet density `1/(|G|·|H|)` (`chebotarev_cyclotomic` at `M/F` with
  `F = M^⟨(σ,τ)⟩`, C3, lifted through `F/K` by `density_lift_through_fixedField_repl`, C5).

The global tag makes the distinct-`τ` fibres disjoint (`pairwiseDisjoint_of_tag`), which is the
only extra fact `exists_cyclotomicCrossing_fibres` needs on top of this leaf.

This packages the compositum infrastructure (`compositum_charProd_bijective` /
`autToPow_L_bijective` (C1), `cyclotomicField_finrank_eq` (C2a)) and the per-`τ` density chain
(C3/C4/C5); see the decomposition note above. `hm4`/`hcop` are threaded verbatim into those
leaves. -/
private theorem exists_crossing_family_tagged
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (_hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    ∃ (t : Ideal (𝓞 K) → (ZMod m)ˣ)
      (S : {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} → Set (Ideal (𝓞 K))),
      (∀ τ, S τ ⊆ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ}) ∧
      (∀ τ, ∀ 𝔭 ∈ S τ, t 𝔭 = (τ : (ZMod m)ˣ)) ∧
      (∀ τ, HasDirichletDensity (S τ)
          ((Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹)) := by
  classical
  haveI : NeZero m := ⟨by lia⟩
  let M := CyclotomicField m L
  haveI : IsGalois K M := isGalois_compositum_base K L m M
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  haveI : FiniteDimensional K M := inferInstance
  obtain ⟨ζ, hζ⟩ : ∃ r : M, IsPrimitiveRoot r m :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M (Set.mem_singleton m) (NeZero.ne m)
  set χK : Gal(M/K) →* (ZMod m)ˣ := hζ.autToPow K with hχK
  have hΦbij : Function.Bijective ((AlgEquiv.restrictNormalHom L).prod χK) :=
    compositum_charProd_bijective K L M m hcop ζ hζ
  set equivΦ : Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ :=
    MulEquiv.ofBijective _ hΦbij with hequivΦ
  set e2 : Gal(M/L) ≃* (ZMod m)ˣ :=
    MulEquiv.ofBijective (hζ.autToPow L) (autToPow_L_bijective K L M m hcop ζ hζ) with he2
  haveI : IsMulCommutative Gal(M/L) :=
    .of_comm fun a b ↦ e2.injective (by rw [map_mul, map_mul]; exact mul_comm (e2 a) (e2 b))
  haveI hGcomm : ∀ x y : Gal(L/K), x * y = y * x := fun x y ↦ mul_comm' x y
  haveI : IsMulCommutative Gal(M/K) :=
    .of_comm fun a b ↦ equivΦ.injective (by
      rw [map_mul, map_mul, Prod.mul_def, Prod.mul_def, hGcomm, mul_comm
        ((equivΦ a).2) ((equivΦ b).2)])
  set σM : (ZMod m)ˣ → Gal(M/K) := fun τ ↦ equivΦ.symm (σ, τ) with hσM
  have hσMpair : ∀ τ, (AlgEquiv.restrictNormalHom L (σM τ), χK (σM τ)) = (σ, τ) :=
    fun τ ↦ equivΦ.apply_symm_apply (σ, τ)
  have hσMrestr : ∀ τ, AlgEquiv.restrictNormalHom L (σM τ) = σ :=
    fun τ ↦ congrArg Prod.fst (hσMpair τ)
  have hσMchar : ∀ τ, χK (σM τ) = τ :=
    fun τ ↦ congrArg Prod.snd (hσMpair τ)
  refine ⟨fun 𝔭 ↦ χK (frobeniusClass K M 𝔭).out,
    fun τ ↦ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K M 𝔭 ∧
      frobeniusClass K M 𝔭 = ConjClasses.mk (σM τ)}, ?_, ?_, ?_⟩
  · rintro τ 𝔭 ⟨hp, hunrM, hfr⟩
    have hunrL : UnramifiedIn K L 𝔭 := unramifiedIn_tower_descend K L M 𝔭 hunrM
    exact ⟨hp, hunrL,
      frobeniusClass_proj K L M σ (σM τ) (hσMrestr τ) 𝔭 hunrM hunrL hfr⟩
  · rintro τ 𝔭 ⟨-, -, hfr⟩
    have hconj : IsConj (frobeniusClass K M 𝔭).out (σM (τ : (ZMod m)ˣ)) := by
      rw [hfr]
      exact ConjClasses.mk_eq_mk_iff_isConj.mp (Quotient.out_eq _)
    change χK (frobeniusClass K M 𝔭).out = (τ : (ZMod m)ˣ)
    rw [isConj_iff_eq.mp (χK.map_isConj hconj), hσMchar]
  · rintro ⟨τ, hτ⟩
    exact density_crossing_fibre_aux K L M m hm4 hcop (σM τ)
      (zpowers_inf_fixingSubgroup_eq_bot_aux K L M m ζ hζ σ τ hτ (σM τ) (hσMrestr τ)
        (hσMchar τ) hΦbij)

private theorem exists_cyclotomicCrossing_fibres
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    ∃ S : {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} → Set (Ideal (𝓞 K)),
      (Set.univ : Set {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}).PairwiseDisjoint S ∧
      (∀ τ, S τ ⊆ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ}) ∧
      (∀ τ, HasDirichletDensity (S τ)
          ((Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹)) := by
  obtain ⟨t, S, hsub, htag, hd⟩ := exists_crossing_family_tagged K L σ m hm hm4 hcop
  exact ⟨S, pairwiseDisjoint_of_tag t Subtype.val Subtype.val_injective S htag, hsub, hd⟩

/-- Sharifi 7.2.2 Step 2 — partial **lower bound** on `δ_inf(S_σ)` coming from one
cyclotomic crossing modulus `m`: `|H_n(m)|/(|G|·|H(m)|)` bounds the `liminf` of the
density ratio for `S_σ` in `K`. Source quote (p. 144): "δ_inf(S_σ) ≥ |H_n|/(|G|·|H|)".

The crossing is only valid at *admissible* `m`, so this per-`m` bound carries the same
two hypotheses as `exists_cyclotomicCrossing_fibres`: `hm4 : m % 4 ≠ 2` (feeding the
cyclotomic case) and `hcop : ((NumberField.discr L).natAbs).Coprime m` (the
linear-disjointness via the everywhere-unramified intersection / `discr_dvd_discr`). The
consumer `liminf_ratio_ge_inv_card_G` drives `m` along admissible primes. -/
theorem liminf_density_S_sigma_ge_card_H_n_div_GH
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (_hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    (Nat.card {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} : ℝ)
        / (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ))
      ≤ Filter.liminf
          (fun s : ℝ ↦
            primeIdealZetaSum
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
          (𝓝[>] 1) := by
  classical
  set Sσ : Set (Ideal (𝓞 K)) :=
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ}
    with hSσ
  set c : ℝ := (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹ with hc
  obtain ⟨S, hpd, hsub, hd⟩ := exists_cyclotomicCrossing_fibres K L σ m _hm hm4 hcop
  have : Fintype {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} := Fintype.ofFinite _
  set t : Finset {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} := Finset.univ with ht
  have hpd' : (t : Set {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}).PairwiseDisjoint S := by
    rw [ht, Finset.coe_univ]; exact hpd
  have hUdens : HasDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) :=
    hasDirichletDensity_biUnion_const t S c hpd' fun i _ ↦ hd i
  have hUsub : (⋃ i ∈ t, S i) ⊆ Sσ := Set.iUnion₂_subset fun i _ ↦ hsub i
  have hUlow : HasLowerDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) := hUdens.hasLower
  have hSσlow : HasLowerDirichletDensity Sσ
      (Filter.liminf
        (fun s : ℝ ↦ primeIdealZetaSum Sσ s / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
        (𝓝[>] 1)) := rfl
  have hmono := HasLowerDirichletDensity.mono hUsub hUlow hSσlow
  have htcard : (t.card : ℝ) • c
      = (Nat.card {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} : ℝ)
          / (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ)) := by
    rw [ht, Finset.card_univ, hc, smul_eq_mul, ← Nat.card_eq_fintype_card, div_eq_mul_inv]
  rw [htcard] at hmono
  exact hmono

/-! #### Number-theoretic helpers for `H_n_over_H_tends_to_one`

The proof is a direct CRT-free argument: writing `total k = φ(n^k)`,
`good k = #{τ : n ∣ ord τ}` and `bad k = #{τ : n ∤ ord τ}` in the unit group
`(ZMod (n^k))ˣ`, we bound `bad k / total k → 0` and conclude `good k / total k → 1`.
The key is a *uniform* (cyclicity-free) torsion bound `torsion_card_le`, fed at the
exponent `E = λ(n^k)`. The `p = 2` non-cyclic prime power needs no special handling:
the argument stays at the level of the relatively-negligible "bad" set. -/

/-- Uniform torsion bound in any finite commutative group:
`#{x : xᴹ = 1} · (E / gcd(E, M)) ≤ |G|`, where `E = Monoid.exponent G`. -/
private theorem torsion_card_le (G : Type*) [CommGroup G] [Finite G] (M : ℕ) :
    Nat.card {x : G // x ^ M = 1} * (Monoid.exponent G / Nat.gcd (Monoid.exponent G) M)
      ≤ Nat.card G := by
  classical
  set f : G →* G := powMonoidHom M with hf
  have hker : Nat.card f.ker = Nat.card {x : G // x ^ M = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by rw [MonoidHom.mem_ker]; rfl)
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card G := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    ring
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (Monoid.ExponentExists.of_finite (G := G))
  have hord : orderOf (g ^ M) = Monoid.exponent G / Nat.gcd (Monoid.exponent G) M := by
    rw [orderOf_pow, hg]
  have hle : orderOf (g ^ M) ≤ Nat.card f.range := by
    rw [← Nat.card_zpowers]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion (by
      rw [Subgroup.zpowers_le]; exact ⟨g, rfl⟩)) (Subgroup.inclusion_injective _)
  rw [← hord]
  calc Nat.card {x : G // x ^ M = 1} * orderOf (g ^ M)
      = Nat.card f.ker * orderOf (g ^ M) := by rw [hker]
    _ ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul_left _ hle
    _ = Nat.card G := hcard

/-- The `q`-adic valuation of the "capped" modulus `ordCompl[p] E * p ^ (v - 1)` (which
replaces `E`'s `p`-part by `p ^ (v - 1)`): it is `v - 1` at `q = p` and `v_q(E)` elsewhere. -/
private theorem factorization_ordCompl_mul_pow (E p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (q : ℕ) :
    (ordCompl[p] E * p ^ (v - 1)).factorization q
      = if q = p then v - 1 else E.factorization q := by
  rw [Nat.factorization_mul (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero)]
  simp only [Finsupp.coe_add, Pi.add_apply, hp.factorization_pow, Finsupp.single_apply,
    Nat.factorization_ordCompl]
  by_cases hq : q = p
  · subst hq; rw [Finsupp.erase_same, if_pos rfl, if_pos rfl, zero_add]
  · rw [Finsupp.erase_ne hq, if_neg fun h ↦ hq h.symm, if_neg hq, add_zero]

/-- If `d ∣ E` and the `p`-adic valuation of `d` is `≤ v - 1`, then `d` divides the
"capped" modulus `ordCompl[p] E * p ^ (v - 1)` (which replaces `E`'s `p`-part by
`p ^ (v - 1)`). Used to land a small-order element in an `M`-torsion subgroup. -/
private theorem dvd_capped (E d p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (hd : d ∣ E)
    (hvp : d.factorization p ≤ v - 1) : d ∣ ordCompl[p] E * p ^ (v - 1) := by
  have hdne : d ≠ 0 := fun h ↦ by subst h; exact hE (Nat.eq_zero_of_zero_dvd hd)
  rw [← Nat.factorization_le_iff_dvd hdne
    (mul_ne_zero (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero))]
  intro q
  rw [factorization_ordCompl_mul_pow E p v hp hE q]
  by_cases hq : q = p
  · subst hq; rwa [if_pos rfl]
  · rw [if_neg hq]; exact (Nat.factorization_le_iff_dvd hdne hE).mpr hd q

/-- The capped modulus `ordCompl[p] E * p ^ (v - 1)` divides `E` when `v - 1 ≤ v_p(E)`. -/
private theorem M_dvd_E (E p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (hle : v - 1 ≤ E.factorization p) :
    ordCompl[p] E * p ^ (v - 1) ∣ E := by
  rw [← Nat.factorization_le_iff_dvd
    (mul_ne_zero (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero)) hE]
  intro q
  rw [factorization_ordCompl_mul_pow E p v hp hE q]
  by_cases hq : q = p
  · subst hq; rwa [if_pos rfl]
  · rw [if_neg hq]

/-- Factoring out the complementary `p`-power: `E = (ordCompl[p] E * p ^ (v - 1)) *
p ^ (v_p(E) - (v - 1))`, used to compute `E / M = p ^ (v_p(E) - (v - 1))`. -/
private theorem E_eq_M_mul (E p v : ℕ) (hle : v - 1 ≤ E.factorization p) :
    E = ordCompl[p] E * p ^ (v - 1) * p ^ (E.factorization p - (v - 1)) := by
  rw [mul_assoc, ← pow_add,
    show v - 1 + (E.factorization p - (v - 1)) = E.factorization p by lia,
    mul_comm (ordCompl[p] E), Nat.ordProj_mul_ordCompl_eq_self]

/-- For a prime `p ∣ n`, the Carmichael function satisfies
`p ^ (k · v_p(n) - 2) ∣ λ(n^k)`. -/
private theorem pk_dvd_carmichael (n k p : ℕ) (hp : p.Prime) (hpn : p ∣ n) :
    p ^ (k * n.factorization p - 2) ∣ ArithmeticFunction.carmichael (n ^ k) := by
  set v := n.factorization p
  have hdvd1 : p ^ (k * v) ∣ n ^ k := by
    calc p ^ (k * v) = (p ^ v) ^ k := by rw [← pow_mul, mul_comm]
      _ ∣ n ^ k := pow_dvd_pow_of_dvd (Nat.ordProj_dvd n p) k
  have hdvd2 := ArithmeticFunction.carmichael_dvd hdvd1
  have hdvd3 : p ^ (k * v - 2) ∣ ArithmeticFunction.carmichael (p ^ (k * v)) := by
    by_cases h2 : p = 2
    · subst h2
      by_cases hj2 : k * v = 2
      · rw [hj2]; norm_num
      · rw [ArithmeticFunction.carmichael_two_pow_of_ne_two hj2]
    · rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two (k * v) hp h2]
      rcases Nat.eq_zero_or_pos (k * v) with h0 | hpos
      · rw [h0]; simp
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        rw [hm] at *
        rw [Nat.totient_prime_pow_succ hp]
        exact (pow_dvd_pow p (show m + 1 - 2 ≤ m by lia)).trans (dvd_mul_right (p ^ m) (p - 1))
  exact hdvd3.trans hdvd2

/-- Cardinality monotonicity for the "bad at `p`" set sitting inside an `M`-torsion
subgroup, given each bad element satisfies `xᴹ = 1`. -/
private theorem bad_le_torsion (G : Type*) [Finite G] [Monoid G] (M p v : ℕ)
    (h : ∀ x : G, ¬ p ^ v ∣ orderOf x → x ^ M = 1) :
    Nat.card {x : G // ¬ p ^ v ∣ orderOf x} ≤ Nat.card {x : G // x ^ M = 1} :=
  Nat.card_le_card_of_injective _ (Subtype.impEmbedding _ _ h).injective

/-- If `n ∤ d` (with `n, d ≠ 0`) then some prime power `p ^ v_p(n)` already fails to
divide `d`: the contrapositive of the prime-power criterion `n ∣ d`. -/
private theorem exists_prime_pow_not_dvd (n d : ℕ) (hn : n ≠ 0) (hd : d ≠ 0) (hndvd : ¬ n ∣ d) :
    ∃ p ∈ n.primeFactors, ¬ p ^ (n.factorization p) ∣ d := by
  by_contra! hcon
  apply hndvd
  rw [← Nat.factorization_le_iff_dvd hn hd]
  intro p
  by_cases hp : p ∈ n.primeFactors
  · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact (Nat.Prime.pow_dvd_iff_le_factorization hpp hd).mp (hcon p hp)
  · have hzero : n.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hp
    rw [hzero]; exact Nat.zero_le _

/-- A subtype carved by `P` injects into a finite union of subtypes carved by `Q i`
whenever `P x` forces some `Q i x` with `i ∈ s`; hence its card is `≤ Σ_i #{Q i}`. -/
private theorem card_le_sum_card {G : Type*} [Finite G] {ι : Type*} (s : Finset ι)
    (P : G → Prop) (Q : ι → G → Prop) (h : ∀ x, P x → ∃ i ∈ s, Q i x) :
    Nat.card {x : G // P x} ≤ ∑ i ∈ s, Nat.card {x : G // Q i x} := by
  classical
  have : Fintype G := Fintype.ofFinite G
  simp only [Nat.card_eq_fintype_card]
  calc Fintype.card {x : G // P x}
      = (Finset.univ.filter P).card := by rw [Fintype.card_subtype]
    _ ≤ (s.biUnion (fun i ↦ Finset.univ.filter (Q i))).card := by
        refine Finset.card_le_card (fun x hx ↦ ?_)
        rw [Finset.mem_filter] at hx
        obtain ⟨i, hi, hqi⟩ := h x hx.2
        exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hqi⟩⟩
    _ ≤ ∑ i ∈ s, (Finset.univ.filter (Q i)).card := Finset.card_biUnion_le
    _ = ∑ i ∈ s, Fintype.card {x : G // Q i x} :=
        Finset.sum_congr rfl (fun i _ ↦ by rw [Fintype.card_subtype])

/-- Each per-prime tail `1 / p ^ (k · v - v - 1) → 0` as `k → ∞` (base `p ≥ 2`,
exponent `→ ∞`). -/
private theorem summand_tendsto (p v : ℕ) (hp : 2 ≤ p) (hv : 1 ≤ v) :
    Tendsto (fun k : ℕ ↦ (1 : ℝ) / (p : ℝ) ^ (k * v - v - 1)) atTop (𝓝 0) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hpinv1 : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ hp0]; exact_mod_cast hp.trans_lt' Nat.one_lt_two
  have hbase : Tendsto (fun m : ℕ ↦ ((p : ℝ)⁻¹) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hpinv1
  have hexp : Tendsto (fun k : ℕ ↦ k * v - v - 1) atTop atTop := by
    refine tendsto_atTop_mono (f := fun k : ℕ ↦ k - (v + 1)) (fun k ↦ ?_)
      (tendsto_sub_atTop_nat (v + 1))
    have : k ≤ k * v := Nat.le_mul_of_pos_right k hv; lia
  refine (hbase.comp hexp).congr (fun k ↦ ?_)
  simp [Function.comp_apply, one_div, inv_pow]

/-- The "bad" ratio is bounded by the sum of per-prime tails: from a cover
`bad ≤ Σ_p badp` and the per-prime bounds `badp · P p ^ e ≤ total`, conclude
`bad / total ≤ Σ_p 1 / P p ^ e` in `ℝ`. -/
private theorem ratio_bound (bad total : ℕ) (s : Finset ℕ) (badp : ℕ → ℕ) (e : ℕ → ℕ) (P : ℕ → ℕ)
    (htot : 0 < total) (hcover : bad ≤ ∑ p ∈ s, badp p) (hP : ∀ p ∈ s, 0 < P p)
    (hbound : ∀ p ∈ s, badp p * (P p) ^ (e p) ≤ total) :
    (bad : ℝ) / total ≤ ∑ p ∈ s, (1 : ℝ) / (P p : ℝ) ^ (e p) := by
  have htotR : (0 : ℝ) < total := by exact_mod_cast htot
  have hnum : (bad : ℝ) ≤ ∑ p ∈ s, (badp p : ℝ) := by
    calc (bad : ℝ) ≤ ((∑ p ∈ s, badp p : ℕ) : ℝ) := by exact_mod_cast hcover
      _ = ∑ p ∈ s, (badp p : ℝ) := by push_cast; ring
  calc (bad : ℝ) / total
      ≤ (∑ p ∈ s, (badp p : ℝ)) / total := by gcongr
    _ = ∑ p ∈ s, (badp p : ℝ) / total := by rw [Finset.sum_div]
    _ ≤ ∑ p ∈ s, (1 : ℝ) / (P p : ℝ) ^ (e p) := by
        refine Finset.sum_le_sum (fun p hps ↦ ?_)
        have hPp : (0 : ℝ) < (P p : ℝ) ^ (e p) := by have := hP p hps; positivity
        rw [div_le_div_iff₀ htotR hPp, one_mul]
        calc (badp p : ℝ) * (P p : ℝ) ^ (e p) = ((badp p * (P p) ^ (e p) : ℕ) : ℝ) := by
              push_cast; ring
          _ ≤ (total : ℝ) := by exact_mod_cast hbound p hps

/-- Shared core of the per-prime bounds: in a finite commutative group `G` whose exponent
has `p`-adic valuation at least `e + (v - 1)`, the number of `x` with `p ^ v ∤ ord x`, times
`p ^ e`, is at most `|G|`. The small-order elements all land in the `M`-torsion subgroup
for the capped modulus `M = ordCompl[p] E · p ^ (v - 1)`, whose index supplies the `p ^ e`
factor via `torsion_card_le`. -/
private theorem perprime_bound_core (G : Type*) [CommGroup G] [Finite G] (p v e : ℕ)
    (hp : p.Prime) (hv1 : 1 ≤ v) (he : e + (v - 1) ≤ (Monoid.exponent G).factorization p) :
    Nat.card {x : G // ¬ p ^ v ∣ orderOf x} * p ^ e ≤ Nat.card G := by
  classical
  set E := Monoid.exponent G with hE
  have hEne : E ≠ 0 := hE ▸ (Monoid.ExponentExists.of_finite (G := G)).exponent_ne_zero
  set M := ordCompl[p] E * p ^ (v - 1)
  have hMne : M ≠ 0 := mul_ne_zero (Nat.ordCompl_pos p hEne).ne' (pow_ne_zero _ hp.ne_zero)
  have hle1 : v - 1 ≤ E.factorization p := by lia
  have hMdvdE : M ∣ E := M_dvd_E E p v hp hEne hle1
  have hgcd : Nat.gcd E M = M := Nat.gcd_eq_right hMdvdE
  have hEdivM : E / M = p ^ (E.factorization p - (v - 1)) :=
    Nat.div_eq_of_eq_mul_right (Nat.pos_of_ne_zero hMne) (E_eq_M_mul E p v hle1)
  have hbad_sub : Nat.card {x : G // ¬ p ^ v ∣ orderOf x} ≤ Nat.card {x : G // x ^ M = 1} := by
    refine bad_le_torsion G M p v (fun x hx ↦ ?_)
    rw [← orderOf_dvd_iff_pow_eq_one]
    refine dvd_capped E (orderOf x) p v hp hEne ?_ ?_
    · rw [hE]; exact Monoid.order_dvd_exponent x
    · by_contra! hcon
      exact hx ((Nat.Prime.pow_dvd_iff_le_factorization hp (orderOf_pos x).ne').mpr (by lia))
  have hEM : p ^ e ≤ E / M := by
    rw [hEdivM]; exact pow_le_pow_right₀ hp.one_le (by lia)
  calc Nat.card {x : G // ¬ p ^ v ∣ orderOf x} * p ^ e
      ≤ Nat.card {x : G // x ^ M = 1} * p ^ e := Nat.mul_le_mul_right _ hbad_sub
    _ ≤ Nat.card {x : G // x ^ M = 1} * (E / M) := Nat.mul_le_mul_left _ hEM
    _ = Nat.card {x : G // x ^ M = 1} * (E / Nat.gcd E M) := by rw [hgcd]
    _ ≤ Nat.card G := torsion_card_le G M

/-- The number of units of `ZMod (n^k)` with `p ^ v_p(n) ∤ ord τ`, times
`p ^ (k v_p(n) - v_p(n) - 1)`, is at most `φ(n^k)`. -/
private theorem perprime_bound (n k p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hn2 : 2 ≤ n) (hk : 2 ≤ k) :
    Nat.card {τ : (ZMod (n ^ k))ˣ // ¬ p ^ n.factorization p ∣ orderOf τ}
      * p ^ (k * n.factorization p - n.factorization p - 1)
      ≤ Nat.card (ZMod (n ^ k))ˣ := by
  have hnk : NeZero (n ^ k) := ⟨pow_ne_zero k (by lia)⟩
  set v := n.factorization p with hv
  have hv1 : 1 ≤ v := hv ▸ Nat.Prime.factorization_pos_of_dvd hp (by lia) hpn
  have hvpE : k * v - 2 ≤ (Monoid.exponent (ZMod (n ^ k))ˣ).factorization p := by
    refine (Nat.Prime.pow_dvd_iff_le_factorization hp ?_).mp ?_
    · exact (Monoid.ExponentExists.of_finite (G := (ZMod (n ^ k))ˣ)).exponent_ne_zero
    · rw [← ArithmeticFunction.carmichael_eq_exponent' (n ^ k)]
      exact pk_dvd_carmichael n k p hp hpn
  have h2v : 2 * v ≤ k * v := Nat.mul_le_mul_right v hk
  exact perprime_bound_core (ZMod (n ^ k))ˣ p v _ hp hv1 (by lia)

/-- Exponent-keyed per-prime bound — the generalisation of `perprime_bound` from the
specific group `(ZMod (n^k))ˣ` to *any* finite commutative group `G`, keyed on a
divisibility `p ^ a ∣ Monoid.exponent G` rather than on the Carmichael function of `n^k`.
The number of `x : G` with `p ^ v ∤ ord x`, times `p ^ (a - v - 1)`, is at most `|G|`.

Used at the admissible-prime sequence `m ≡ 1 (mod 4·n^k)` of `liminf_ratio_ge_inv_card_G`:
there `G = (ZMod m)ˣ` is cyclic of exponent `m - 1`, and `n^k ∣ m - 1`, so
`p ^ (k·v_p(n)) ∣ m - 1 = exponent`. -/
private theorem perprime_bound_exp (G : Type*) [CommGroup G] [Finite G] (p a v : ℕ)
    (hp : p.Prime) (hv1 : 1 ≤ v) (hav : v ≤ a) (hdvd : p ^ a ∣ Monoid.exponent G) :
    Nat.card {x : G // ¬ p ^ v ∣ orderOf x} * p ^ (a - v - 1) ≤ Nat.card G := by
  have haE : a ≤ (Monoid.exponent G).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp
      (Monoid.ExponentExists.of_finite (G := G)).exponent_ne_zero).mp hdvd
  exact perprime_bound_core G p v _ hp hv1 (by lia)

/-- Single-group form of the `H_n` ratio lower bound — the generalisation of (the per-`k`
step inside) `H_n_over_H_tends_to_one` to *any* finite commutative group `G` whose
exponent is divisible by `p ^ (k·v_p(n))` for every prime `p ∣ n`. Then
`|{τ : n ∣ ord τ}| / |G| ≥ 1 - Σ_{p ∣ n} 1/p^(k·v_p(n) - v_p(n) - 1)`. Used at the
admissible-prime sequence (`G = (ZMod m)ˣ`, exponent `m - 1`, `n^k ∣ m - 1`) to drive
the ratio to `1` by `k → ∞`. Built from `card_le_sum_card`, `exists_prime_pow_not_dvd`,
`ratio_bound` and the exponent-keyed `perprime_bound_exp`. -/
private theorem H_n_ratio_ge (G : Type*) [CommGroup G] [Finite G] (n k : ℕ) (hn2 : 2 ≤ n)
    (hk : 1 ≤ k)
    (hexp : ∀ p ∈ n.primeFactors, p ^ (k * n.factorization p) ∣ Monoid.exponent G) :
    1 - (∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1))
      ≤ (Nat.card {τ : G // n ∣ orderOf τ} : ℝ) / Nat.card G := by
  classical
  set total : ℕ := Nat.card G with htotal
  set good : ℕ := Nat.card {τ : G // n ∣ orderOf τ} with hgood
  set bad : ℕ := Nat.card {τ : G // ¬ n ∣ orderOf τ} with hbad
  have htotpos : 0 < total := Nat.card_pos
  have hgb : good + bad = total := by
    have : Fintype G := Fintype.ofFinite G
    rw [hgood, hbad, htotal]
    simp only [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl]
    have hle : Fintype.card {τ : G // n ∣ orderOf τ} ≤ Fintype.card G := Fintype.card_subtype_le _
    lia
  have hbadratio : (bad : ℝ) / total
      ≤ ∑ p ∈ n.primeFactors,
          (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1) := by
    refine ratio_bound bad total n.primeFactors
      (fun p ↦ Nat.card {τ : G // ¬ p ^ n.factorization p ∣ orderOf τ})
      (fun p ↦ k * n.factorization p - n.factorization p - 1) (fun p ↦ p)
      htotpos ?_ ?_ ?_
    · rw [hbad]
      refine card_le_sum_card n.primeFactors (fun τ ↦ ¬ n ∣ orderOf τ)
        (fun p τ ↦ ¬ p ^ n.factorization p ∣ orderOf τ) (fun τ hτ ↦ ?_)
      exact exists_prime_pow_not_dvd n (orderOf τ) (by lia) (orderOf_pos τ).ne' hτ
    · exact fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos
    · intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hv1 : 1 ≤ n.factorization p := Nat.Prime.factorization_pos_of_dvd hpp (by lia) hpn
      have hav : n.factorization p ≤ k * n.factorization p := Nat.le_mul_of_pos_left _ hk
      exact perprime_bound_exp G p (k * n.factorization p) (n.factorization p) hpp hv1 hav
        (hexp p hp)
  have htk : (total : ℝ) ≠ 0 := by exact_mod_cast htotpos.ne'
  have heq : (good : ℝ) / total = 1 - (bad : ℝ) / total := by
    have hgbk : (good : ℝ) + (bad : ℝ) = (total : ℝ) := by exact_mod_cast hgb
    field_simp
    linarith [hgbk]
  rw [heq]
  linarith [hbadratio]

/-- Sharifi 7.2.2 Step 2 sub-lemma (v) — `|H_n|/|H| → 1` as `m ≡ 1 mod
n^k` for `k → ∞`. Verbatim source quote: "so `|H_n|/|H|` tends to 1 as
`j` increases". -/
theorem H_n_over_H_tends_to_one (n : ℕ) (_hn : 1 ≤ n) :
    Tendsto
      (fun k : ℕ ↦ (Nat.card {τ : (ZMod (n ^ k))ˣ // n ∣ orderOf τ} : ℝ)
        / Nat.card ((ZMod (n ^ k))ˣ))
      Filter.atTop (𝓝 1) := by
  classical
  rcases eq_or_lt_of_le _hn with rfl | hn2'
  · have hconst : ∀ k : ℕ, (Nat.card {τ : (ZMod (1 ^ k))ˣ // (1 : ℕ) ∣ orderOf τ} : ℝ)
        / Nat.card ((ZMod (1 ^ k))ˣ) = 1 := fun k ↦ by
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun x ↦ one_dvd _)),
        div_self (by exact_mod_cast Nat.card_pos.ne')]
    rw [tendsto_congr hconst]; exact tendsto_const_nhds
  · have hn2 : 2 ≤ n := hn2'
    set total : ℕ → ℕ := fun k ↦ Nat.card ((ZMod (n ^ k))ˣ) with htotal
    set good : ℕ → ℕ := fun k ↦ Nat.card {τ : (ZMod (n ^ k))ˣ // n ∣ orderOf τ} with hgood
    set bad : ℕ → ℕ := fun k ↦ Nat.card {τ : (ZMod (n ^ k))ˣ // ¬ n ∣ orderOf τ} with hbad
    have hnk : ∀ k, NeZero (n ^ k) := fun k ↦ ⟨pow_ne_zero k (by lia)⟩
    have htotpos : ∀ k, 0 < total k := fun k ↦ by have := hnk k; exact Nat.card_pos
    have hgb : ∀ k, good k + bad k = total k := fun k ↦ by
      have := hnk k
      rw [hgood, hbad, htotal]
      simp only [Nat.card_eq_fintype_card]
      rw [Fintype.card_subtype_compl]
      have hle : Fintype.card {τ : (ZMod (n ^ k))ˣ // n ∣ orderOf τ}
          ≤ Fintype.card ((ZMod (n ^ k))ˣ) := Fintype.card_subtype_le _
      lia
    set S : ℕ → ℝ := fun k ↦ ∑ p ∈ n.primeFactors,
      (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1) with hSdef
    have hStendsto : Tendsto S atTop (𝓝 0) := by
      rw [hSdef, show (0 : ℝ) = ∑ _p ∈ n.primeFactors, (0 : ℝ) by simp]
      refine tendsto_finsetSum _ (fun p hp ↦ ?_)
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      exact summand_tendsto p (n.factorization p) hpp.two_le
        (Nat.Prime.factorization_pos_of_dvd hpp (by lia) hpdvd)
    have hbadratio : Tendsto (fun k ↦ (bad k : ℝ) / total k) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hStendsto
        (Filter.Eventually.of_forall (fun k ↦ by positivity)) ?_
      filter_upwards [Filter.eventually_ge_atTop 2] with k hk
      refine ratio_bound (bad k) (total k) n.primeFactors
        (fun p ↦ Nat.card {τ : (ZMod (n ^ k))ˣ // ¬ p ^ n.factorization p ∣ orderOf τ})
        (fun p ↦ k * n.factorization p - n.factorization p - 1) (fun p ↦ p)
        (htotpos k) ?_ ?_ ?_
      · rw [hbad]
        refine card_le_sum_card n.primeFactors (fun τ ↦ ¬ n ∣ orderOf τ)
          (fun p τ ↦ ¬ p ^ n.factorization p ∣ orderOf τ) (fun τ hτ ↦ ?_)
        have := hnk k
        exact exists_prime_pow_not_dvd n (orderOf τ) (by lia) (orderOf_pos τ).ne' hτ
      · exact fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos
      · intro p hp
        have := hnk k
        exact perprime_bound n k p (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp) hn2 hk
    have heq : ∀ k, (good k : ℝ) / total k = 1 - (bad k : ℝ) / total k := by
      intro k
      have hgbk : (good k : ℝ) + (bad k : ℝ) = (total k : ℝ) := by exact_mod_cast hgb k
      have htk : (total k : ℝ) ≠ 0 := by exact_mod_cast (htotpos k).ne'
      field_simp
      linarith [hgbk]
    rw [tendsto_congr heq]
    simpa using hbadratio.const_sub (1 : ℝ)

/-- For a sequence of moduli `m k` with `n ^ k` dividing the exponent of `(ZMod (m k))ˣ`,
the ratio `|H_n(m k)|/|H(m k)| → 1` as `k → ∞`: the `n = 1` case is constant `1`, and the
`n ≥ 2` case is squeezed between `1 - Σ_{p ∣ n} p^{-(k·v_p(n) - v_p(n) - 1)} → 1` and `1`. -/
private theorem ratio_card_dvd_orderOf_tendsto_one (n : ℕ) (hn1 : 1 ≤ n) (m : ℕ → ℕ)
    (hmNeZero : ∀ k, NeZero (m k))
    (hdvd : ∀ k, 1 ≤ k → ∀ p ∈ n.primeFactors,
      p ^ (k * n.factorization p) ∣ Monoid.exponent (ZMod (m k))ˣ) :
    Filter.Tendsto (fun k : ℕ ↦ (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
      / Nat.card ((ZMod (m k))ˣ)) Filter.atTop (𝓝 1) := by
  rcases eq_or_lt_of_le hn1 with hn1' | hn2'
  · have hconst : ∀ k, (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
        / Nat.card ((ZMod (m k))ˣ) = 1 := fun k ↦ by
      have := hmNeZero k
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun x ↦ hn1'.symm ▸ one_dvd _)),
        div_self (by exact_mod_cast Nat.card_pos.ne')]
    rw [tendsto_congr hconst]
    exact tendsto_const_nhds
  · have hn2 : 2 ≤ n := hn2'
    set S : ℕ → ℝ := fun k ↦ ∑ p ∈ n.primeFactors,
      (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1) with hSdef
    have hSt : Filter.Tendsto S Filter.atTop (𝓝 0) := by
      rw [hSdef, show (0 : ℝ) = ∑ _p ∈ n.primeFactors, (0 : ℝ) by simp]
      refine tendsto_finsetSum _ (fun p hp ↦ ?_)
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact summand_tendsto p (n.factorization p) hpp.two_le
        (Nat.Prime.factorization_pos_of_dvd hpp (by lia) (Nat.dvd_of_mem_primeFactors hp))
    have hlo : Filter.Tendsto (fun k ↦ 1 - S k) Filter.atTop (𝓝 1) := by
      simpa using hSt.const_sub 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_
      (Filter.Eventually.of_forall (fun k ↦ ?_))
    · filter_upwards [Filter.eventually_ge_atTop 1] with k hk1
      exact H_n_ratio_ge (ZMod (m k))ˣ n k hn2 hk1 (hdvd k hk1)
    · have := hmNeZero k
      rw [div_le_one (by exact_mod_cast (Nat.card_pos : 0 < Nat.card ((ZMod (m k))ˣ)))]
      exact_mod_cast Nat.card_le_card_of_injective
        (Subtype.val : {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} → _) Subtype.val_injective

/-- For each `k` there is a prime `m > d` with `m % 4 ≠ 2` and `n ^ k ∣ m - 1`: an admissible
modulus for the cyclotomic crossing, from Dirichlet's theorem on primes in `1 (mod 4·n^k)`. -/
private theorem exists_admissible_prime (n d : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    ∃ m : ℕ, m.Prime ∧ d < m ∧ m % 4 ≠ 2 ∧ n ^ k ∣ m - 1 := by
  obtain ⟨m, hmgt, hmp, hmeq⟩ := Nat.forall_exists_prime_gt_and_modEq (max d 1)
    (q := 4 * n ^ k) (by positivity) (Nat.coprime_one_left _)
  have hdvd : 4 * n ^ k ∣ m - 1 := (Nat.modEq_iff_dvd' hmp.one_lt.le).mp hmeq.symm
  refine ⟨m, hmp, by omega, ?_, dvd_trans ⟨4, by ring⟩ hdvd⟩
  have := dvd_trans ⟨n ^ k, rfl⟩ hdvd
  omega

/-- Per-`σ` lower bound `δ_inf(S_σ) ≥ 1/|G|`, the limit of the per-`m` bound
`liminf_density_S_sigma_ge_card_H_n_div_GH` as `m → ∞` along a sequence of
*admissible primes* `m_k ≡ 1 (mod 4·n^k)` with `m_k > |disc L|` (Dirichlet's theorem on
primes in arithmetic progression). The lower half of Sharifi 7.2.2 Step 2 (p. 144). -/
theorem liminf_ratio_ge_inv_card_G
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    (Nat.card Gal(L/K) : ℝ)⁻¹
      ≤ Filter.liminf
          (fun s : ℝ ↦
            primeIdealZetaSum
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
          (𝓝[>] 1) := by
  classical
  set n : ℕ := Nat.card Gal(L/K) with hn
  set L_inf : ℝ :=
    Filter.liminf
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) with hLinf
  have hnpos : 0 < n := hn ▸ Nat.card_pos
  have hn1 : 1 ≤ n := hnpos
  set dB : ℕ := (NumberField.discr L).natAbs with hdB
  have hdBpos : 0 < dB := by
    rw [hdB, Int.natAbs_pos]
    exact NumberField.discr_ne_zero L
  choose m hmp hmgt hm4 hmdvd using exists_admissible_prime n dB hn1
  have hm1 : ∀ k, 1 ≤ m k := fun k ↦ (hmp k).one_lt.le
  have hmne : ∀ k, m k ≠ 0 := fun k ↦ (hmp k).pos.ne'
  have hmNeZero : ∀ k, NeZero (m k) := fun k ↦ ⟨hmne k⟩
  have hmcop : ∀ k, dB.Coprime (m k) := fun k ↦ by
    rw [Nat.coprime_comm, (hmp k).coprime_iff_not_dvd]
    exact fun hdvd ↦ absurd (Nat.le_of_dvd hdBpos hdvd) (Nat.not_le.mpr (hmgt k))
  have hexp : ∀ k, Monoid.exponent (ZMod (m k))ˣ = m k - 1 := fun k ↦ by
    haveI : Fact (m k).Prime := ⟨hmp k⟩
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (hmp k)]
  have hbound : ∀ k : ℕ,
      (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
          / Nat.card ((ZMod (m k))ˣ) * (n : ℝ)⁻¹ ≤ L_inf := by
    intro k
    have hbnd := liminf_density_S_sigma_ge_card_H_n_div_GH K L σ (m k) (hm1 k) (hm4 k)
      (hdB ▸ hmcop k)
    rw [← hn, ← hLinf] at hbnd
    refine le_trans (le_of_eq ?_) hbnd
    have hHpos : (0 : ℝ) < Nat.card ((ZMod (m k))ˣ) := by
      have := hmNeZero k
      exact_mod_cast Nat.card_pos
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    field_simp
  have hexpdvd : ∀ k, 1 ≤ k → ∀ p ∈ n.primeFactors,
      p ^ (k * n.factorization p) ∣ Monoid.exponent (ZMod (m k))ˣ := fun k _ p hp ↦ by
    rw [hexp k]
    refine dvd_trans ?_ (hmdvd k)
    calc p ^ (k * n.factorization p) = (p ^ n.factorization p) ^ k := by rw [← pow_mul, mul_comm]
      _ ∣ n ^ k := pow_dvd_pow_of_dvd (Nat.ordProj_dvd n p) k
  have htends : Filter.Tendsto
      (fun k : ℕ ↦ (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
          / Nat.card ((ZMod (m k))ˣ) * (n : ℝ)⁻¹)
      Filter.atTop (𝓝 ((n : ℝ)⁻¹)) := by
    simpa using
      (ratio_card_dvd_orderOf_tendsto_one n hn1 m hmNeZero hexpdvd).mul_const ((n : ℝ)⁻¹)
  exact le_of_tendsto htends (Filter.Eventually.of_forall hbound)

/-- The density ratios of the `|G|` Frobenius-fibres `S_σ` (over
`σ ∈ Gal(L/K)`) sum to the ratio for the unramified primes, which tends
to `1` as `s ↓ 1` since the ramified primes are finite
(`finite_ramifiedIn`, density `0`). Sharifi 7.2.2 Step 2: the `S_σ`
partition the unramified primes. -/
theorem ratioSum_frobeniusFibres_tendsto_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [hAb : IsMulCommutative Gal(L/K)] :
    Filter.Tendsto
      (fun s : ℝ ↦ ∑ σ : Gal(L/K),
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 1) := by
  classical
  set S : Gal(L/K) → Set (Ideal (𝓞 K)) := fun σ ↦
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ}
    with hS
  set R : Set (Ideal (𝓞 K)) :=
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭} with hR
  set D : ℝ → ℝ := primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) with hD
  letI : CommMonoid Gal(L/K) := IsMulCommutative.instCommMonoid
  have hmk_inj : Function.Injective (ConjClasses.mk : Gal(L/K) → ConjClasses Gal(L/K)) :=
    ConjClasses.mk_injective
  have hpd : ((Finset.univ : Finset Gal(L/K)) : Set Gal(L/K)).PairwiseDisjoint S := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun 𝔭 ha hb ↦ hab (hmk_inj ?_)
    rw [hS] at ha hb
    exact ha.2.2.symm.trans hb.2.2
  have hdisjR : Disjoint (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) R := by
    refine Set.disjoint_left.mpr fun 𝔭 hmem hbad ↦ ?_
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨σ, -, hσ⟩ := hmem
    exact hbad.2.2 (hS ▸ hσ).2.1
  have hcover : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      𝔭 ∈ (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) ∪ R := by
    intro 𝔭 hp hne
    by_cases hunr : UnramifiedIn K L 𝔭
    · obtain ⟨σ, hσ⟩ := ConjClasses.mk_surjective (frobeniusClass K L 𝔭)
      exact Or.inl <| Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨Finset.mem_univ σ,
        hS ▸ ⟨hp, hunr, hσ.symm⟩⟩⟩
    · exact Or.inr ⟨hp, hne, hunr⟩
  have hRfin : R.Finite := finite_ramifiedIn K L
  have hR0 : Filter.Tendsto (fun s ↦ primeIdealZetaSum R s / D s) (𝓝[>] 1) (𝓝 0) :=
    hasDirichletDensity_of_finite K hRfin
  have hDpos : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < D s :=
    (primeIdealZetaSum_univ_tendsto_atTop K).eventually_gt_atTop 0
  have hcomp : Filter.Tendsto (fun s ↦ 1 - primeIdealZetaSum R s / D s) (𝓝[>] 1) (𝓝 1) := by
    simpa using hR0.const_sub 1
  refine hcomp.congr' ?_
  filter_upwards [hDpos, self_mem_nhdsWithin] with s hpos hs1
  simp only [Set.mem_Ioi] at hs1
  have hsum : ∑ σ : Gal(L/K), primeIdealZetaSum (S σ) s
      = primeIdealZetaSum (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) s :=
    (primeIdealZetaSum_biUnion_of_pairwiseDisjoint Finset.univ S hpd hs1).symm
  have hadd : primeIdealZetaSum (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) s
      + primeIdealZetaSum R s = D s := by
    rw [← primeIdealZetaSum_union_of_disjoint hdisjR hs1, hD]
    exact primeIdealZetaSum_eq_univ_of_forall_prime_mem hcover s
  rw [← Finset.sum_div, hsum]
  field_simp
  linarith [hadd]

section LiminfSumGlue

/-! Generic real-analysis helpers for the pigeonhole glue below. They live in a
conditionally complete linearly ordered topological additive group; the only
instance we apply them at is `ℝ`. -/

variable {ι α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
  [DenselyOrdered α] [AddLeftMono α] {l : Filter ι} [l.NeBot]

/-- Superadditivity of `liminf` over a `Finset.sum`: the sum of the `liminf`s is
at most the `liminf` of the sum. -/
private lemma sum_liminf_le_liminf_sum {κ : Type*} (g : κ → ι → α) (t : Finset κ)
    (hbelow : ∀ j ∈ t, l.IsBoundedUnder (· ≥ ·) (g j))
    (habove : ∀ j ∈ t, l.IsBoundedUnder (· ≤ ·) (g j)) :
    ∑ j ∈ t, liminf (g j) l ≤ liminf (fun x ↦ ∑ j ∈ t, g j x) l := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hbS : l.IsBoundedUnder (· ≥ ·) (fun x ↦ ∑ j ∈ s, g j x) :=
        Finset.sum_fn s g ▸ Filter.isBoundedUnder_ge_sum s
          (fun j hj ↦ hbelow j (Finset.mem_insert_of_mem hj))
      have haS : l.IsBoundedUnder (· ≤ ·) (fun x ↦ ∑ j ∈ s, g j x) :=
        Finset.sum_fn s g ▸ Filter.isBoundedUnder_le_sum s
          (fun j hj ↦ habove j (Finset.mem_insert_of_mem hj))
      have step : liminf (g a) l + liminf (fun x ↦ ∑ j ∈ s, g j x) l
          ≤ liminf (fun x ↦ g a x + ∑ j ∈ s, g j x) l :=
        le_liminf_add (hbelow a (Finset.mem_insert_self a s))
          (habove a (Finset.mem_insert_self a s)) hbS (IsBoundedUnder.isCoboundedUnder_ge haS)
      calc liminf (g a) l + ∑ j ∈ s, liminf (g j) l
          ≤ liminf (g a) l + liminf (fun x ↦ ∑ j ∈ s, g j x) l := by
            gcongr
            exact ih (fun j hj ↦ hbelow j (Finset.mem_insert_of_mem hj))
              (fun j hj ↦ habove j (Finset.mem_insert_of_mem hj))
        _ ≤ liminf (fun x ↦ g a x + ∑ j ∈ s, g j x) l := step
        _ = liminf (fun x ↦ ∑ j ∈ insert a s, g j x) l := by simp_rw [Finset.sum_insert ha]

end LiminfSumGlue

/-- If a finite sum `∑ gᵢ` is above-bounded and each `gⱼ` is below-bounded, then every
`gᵢ` is above-bounded: write `gᵢ = (∑ gⱼ) - ∑_{j ≠ i} gⱼ`. -/
private theorem isBoundedUnder_le_of_isBoundedUnder_le_sum {β ι : Type*} [Fintype ι] {l : Filter β}
    (g : ι → β → ℝ) (hF : l.IsBoundedUnder (· ≤ ·) (fun s ↦ ∑ i, g i s))
    (hbelow : ∀ i, l.IsBoundedUnder (· ≥ ·) (g i)) (i : ι) :
    l.IsBoundedUnder (· ≤ ·) (g i) := by
  classical
  obtain ⟨a, ha⟩ := hF.eventually_le
  obtain ⟨b, hb⟩ := (Finset.sum_fn _ g ▸
    Filter.isBoundedUnder_ge_sum (Finset.univ.erase i) (fun j _ ↦ hbelow j)).eventually_ge
  refine isBoundedUnder_of_eventually_le (a := a - b) ?_
  filter_upwards [ha, hb] with s hsa hsb
  have := Finset.add_sum_erase Finset.univ (fun j ↦ g j s) (Finset.mem_univ i)
  linarith

/-- Pure real-analysis glue: a finite family `gᵢ` of functions, each with
`liminf gᵢ ≥ 1/N` (where `N` is the family size) and bounded below, whose sum
tends to `1`, must each tend to `1/N`. (The lower bounds and the sum-limit pin
every `gᵢ` to `1/N` by a pigeonhole on `liminf`/`limsup`.)

The below-boundedness hypothesis `hbelow` is genuinely needed: a finite `liminf`
lower bound alone does not force below-boundedness in a conditionally complete
order, so without it the statement is false (one `gᵢ` could dip to `-∞` while
keeping a spurious `liminf` and the sum still converging). At the only call site
(`chebotarev_abelian`) each `gᵢ` is a ratio of nonnegative Dirichlet sums, hence
`0 ≤ gᵢ`, so `hbelow` is immediate. -/
theorem tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one {ι : Type*} [Fintype ι]
    {γ : Type*} {l : Filter γ} [l.NeBot] (g : ι → γ → ℝ)
    (hlo : ∀ i, (Fintype.card ι : ℝ)⁻¹ ≤ Filter.liminf (g i) l)
    (hbelow : ∀ i, Filter.IsBoundedUnder (· ≥ ·) l (g i))
    (hsum : Filter.Tendsto (fun s ↦ ∑ i, g i s) l (𝓝 (1 : ℝ))) (i₀ : ι) :
    Filter.Tendsto (g i₀) l (𝓝 (Fintype.card ι : ℝ)⁻¹) := by
  classical
  set N : ℕ := Fintype.card ι with hN
  set F : γ → ℝ := fun s ↦ ∑ i, g i s with hF
  have hFle : l.IsBoundedUnder (· ≤ ·) F := hsum.isBoundedUnder_le
  have hFlimsup : limsup F l = 1 := hsum.limsup_eq
  have hgle : ∀ i, l.IsBoundedUnder (· ≤ ·) (g i) :=
    isBoundedUnder_le_of_isBoundedUnder_le_sum g hFle hbelow
  haveI : Nonempty ι := ⟨i₀⟩
  have hNpos : 0 < N := Fintype.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set t : Finset ι := Finset.univ.erase i₀ with ht
  have hrestge : l.IsBoundedUnder (· ≥ ·) (fun s ↦ ∑ j ∈ t, g j s) :=
    Finset.sum_fn t g ▸ Filter.isBoundedUnder_ge_sum t (fun j _ ↦ hbelow j)
  have hrestle : l.IsBoundedUnder (· ≤ ·) (fun s ↦ ∑ j ∈ t, g j s) :=
    Finset.sum_fn t g ▸ Filter.isBoundedUnder_le_sum t (fun j _ ↦ hgle j)
  have hcard : t.card = N - 1 := Finset.card_erase_of_mem (Finset.mem_univ i₀)
  have hliminf_rest : ((N : ℝ) - 1) / N ≤ liminf (fun s ↦ ∑ j ∈ t, g j s) l := by
    have hsuper : ∑ j ∈ t, liminf (g j) l ≤ liminf (fun s ↦ ∑ j ∈ t, g j s) l :=
      sum_liminf_le_liminf_sum g t (fun j _ ↦ hbelow j) (fun j _ ↦ hgle j)
    have hlb : ∑ j ∈ t, ((N : ℝ))⁻¹ ≤ ∑ j ∈ t, liminf (g j) l :=
      Finset.sum_le_sum (fun j _ ↦ hlo j)
    have hconst : ∑ _j ∈ t, ((N : ℝ))⁻¹ = (t.card : ℝ) * (N : ℝ)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst, hcard] at hlb
    have hcast : ((N : ℝ) - 1) / N = ((N - 1 : ℕ) : ℝ) * (N : ℝ)⁻¹ := by
      have hsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        have : (1 : ℕ) ≤ N := hNpos
        push_cast [Nat.cast_sub this]
        ring
      rw [hsub]
      ring
    rw [hcast]
    exact le_trans hlb hsuper
  have hFeq : (fun s ↦ g i₀ s + ∑ j ∈ t, g j s) = F := by
    funext s
    rw [hF]
    exact Finset.add_sum_erase Finset.univ (fun j ↦ g j s) (Finset.mem_univ i₀)
  have hadd : limsup (g i₀) l + liminf (fun s ↦ ∑ j ∈ t, g j s) l
      ≤ limsup (fun s ↦ g i₀ s + ∑ j ∈ t, g j s) l :=
    le_limsup_add (hgle i₀) (IsBoundedUnder.isCoboundedUnder_le (hbelow i₀)) hrestle hrestge
  rw [hFeq, hFlimsup] at hadd
  have hlimsup_le : limsup (g i₀) l ≤ (N : ℝ)⁻¹ := by
    have hrest_le : liminf (fun s ↦ ∑ j ∈ t, g j s) l ≤ 1 - limsup (g i₀) l := by linarith
    have h1 : limsup (g i₀) l ≤ 1 - ((N : ℝ) - 1) / N := by
      linarith [le_trans hliminf_rest hrest_le]
    have h2 : 1 - ((N : ℝ) - 1) / N = (N : ℝ)⁻¹ := by
      field_simp
      ring
    rwa [h2] at h1
  exact tendsto_of_le_liminf_of_limsup_le (hlo i₀) hlimsup_le (hgle i₀) (hbelow i₀)

private theorem isBoundedUnder_ge_ratio_zetaSum (T : Set (Ideal (𝓞 K))) :
    Filter.IsBoundedUnder (· ≥ ·) (𝓝[>] (1 : ℝ))
      (fun s ↦ primeIdealZetaSum T s / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s) :=
  have hnn : ∀ (S : Set (Ideal (𝓞 K))) (s : ℝ), 0 ≤ primeIdealZetaSum S s := fun S s ↦
    primeIdealZetaSum_def S s ▸ tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  isBoundedUnder_of_eventually_ge (a := 0)
    (Filter.Eventually.of_forall fun s ↦ div_nonneg (hnn _ s) (hnn _ s))

/-- **Chebotarev's theorem, abelian case** (Sharifi 7.2.2 Step 2).

For an abelian Galois extension `L/K` of number fields and any
`σ ∈ Gal(L/K)`, the Dirichlet density of primes `𝔭` of `𝓞 K` unramified in
`L` whose Frobenius equals `σ` is `1 / |Gal(L/K)|`.

**Composition**: the `|G|` fibres `S_σ` each have `liminf ≥ 1/|G|`
(`liminf_ratio_ge_inv_card_G`) and their density ratios sum to `1`
(`ratioSum_frobeniusFibres_tendsto_one`); the pigeonhole glue
`tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` forces each to the
limit `1/|G|`. -/
theorem chebotarev_abelian
    [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) := by
  simp only [HasDirichletDensity, Nat.card_eq_fintype_card]
  refine tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one
    (fun τ s ↦
      primeIdealZetaSum
          {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
            frobeniusClass K L 𝔭 = ConjClasses.mk τ} s
        / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
    (fun τ ↦ ?_) (fun τ ↦ isBoundedUnder_ge_ratio_zetaSum K _)
    (ratioSum_frobeniusFibres_tendsto_one K L) σ
  simpa only [Nat.card_eq_fintype_card] using liminf_ratio_ge_inv_card_G K L τ

end Chebotarev
