import HasseWeil.Pic0.PicDual
import HasseWeil.DegreeQuadraticForm
import HasseWeil.GapSpines

/-!
# Route C assembly: the Pic⁰ dual machinery ⟹ `deg(rπ − s) = N` ⟹ `qf_nonneg` (generic)

This file **assembles** the Hasse-bound *Leaf 1* (the III.6.3 qf-nonneg generic case;
the legacy `qf_nonneg_skeleton` chain was retired 2026-06-11) along the
**Pic⁰ dual route** (Silverman III.6.1/III.6.2/III.6.3), *witness-parametric* on a precisely-named
list of residual hypotheses.  It is a self-contained chain

  `[named residuals] ⟹ picDual(rπ − s) = rV − s ⟹ IsDualOf (rV−s) (rπ−s) ⟹ deg(rπ−s) = N`
  `⟹ qf_nonneg(generic (r,s))`,

each link either proved here from the shipped API, or carried as an explicit named hypothesis (the
residual).  **No `sorry`, no `axiom`, no fake/vacuous content** — the residuals are genuine
witness-parametric inputs that make the chain explicit and `#print axioms`-clean.

## What this route *is* (and how it differs from the shipped Wall-A route)

The shipped generic-case identity `HasseWeil.genuineIsogSmulSub_degree_eq_signed_via_walls`
(`GapSpines.lean`) produces the composition equality `(rV−s) ∘ (rπ−s) = [N]` from the **Wall-A**
V-side genuine construction (`Verschiebung/Genuine.lean` → BRIDGE-003).  This file instead routes
the *same* Wall-C extraction through the **Pic⁰ dual** `α̂ = κ⁻¹ ∘ classMap ∘ κ` of
`PicDual.lean`: it identifies `picDual(rπ−s)` with `rV−s` via the III.6.1(a) dual *uniqueness*
mechanism (`picDual_eq_of_comp_toAddMonoidHom_eq`), upgrades the resulting point-map dual relation
to a **full-isogeny** `IsDualOf` via the genuine-isogeny extensionality `genuine_isogeny_ext`
(GapSpines, the "Wall-B killer"), and feeds that into the shipped Wall-C signed-degree extractor
`signed_degree_of_genuine_dual_pair` (`DegreeQuadraticForm.lean`).  The two routes share Wall C and
the genuineness machinery; they differ in *how the dual composition is obtained* (Pic⁰ vs Wall-A).

## Silverman ground truth (verified vs the in-repo PDF, offset +18)

* III.6.2(a) (PDF p.101): `φ̂φ = φφ̂ = [deg φ]`.
* III.6.2(c): dual additivity `(φ + ψ)^ = φ̂ + ψ̂`.
* III.6.3: `deg` is a positive-definite quadratic form, `deg(rπ − s) = r²q − rs·t + s² = N`.
* V.1.1: Hasse via Cauchy–Schwarz on this quadratic form.

## The residual list (each a statable Lean signature)

The assembled `qf_nonneg_generic_via_picDual` closes modulo exactly:

* **`hnat`** — Silverman III.3.4 naturality of `κ` for `β = rπ−s` (`Isogeny.Naturality`); the
  `relNorm 𝔭 = 𝔭.under` general-base / localisation-tower residual.  *(Deep.)*
* **`hsurjDual`, `hsurjβ`** — surjectivity of `picDual β` and of `β.toAddMonoidHom` on points
  (Silverman III.4.10a, automatic over `K̄`).  *(Deep.)*
* **`hβ_dual_hom`** — the dual-additivity output `picDual β = r·V − s` at the point-map level (the
  shipped `dual_add_of_trace_witnesses` reduces it to the Frobenius/`[n]` pieces).  *(Routine given
  the dual-of-Frobenius identification.)*
* **`hgenβ`, `hgenβdual`, `hgenN`** — genuineness witnesses (`IsGenuineWith`) for `β`, `β_dual`,
  `[N]` with the *same geometric action* (the comorphism-upgrade of `picDual`).  *(`[N]` is shipped
  axiom-clean via `mulByInt_isGenuineWith`; `β`, `β_dual` are the genuine-comorphism residual.)*
* **`hVieta`** — the point-map Vieta `(rV−s) ∘ (rπ−s) = [N]` (shipped
  `genuine_dual_comp_toAddMonoidHom_eq_mulByInt`, reduced to `IsDualOf V π` + `π+V=[t]`).
  *(Routine.)*
* **`hN_ne`** — `N ≠ 0` (char-divisible-edge bookkeeping; `qf_nonneg` handles `N = 0` directly).
  *(Routine.)*

`deg(rπ−s) ≥ 0` and `0 < deg(rπ−s)` are **discharged here** unconditionally
(`Int.natCast_nonneg`, `isogeny_degree_pos`).
-/

open WeierstrassCurve

namespace HasseWeil.Pic0.RouteC

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

/-! ### Phase 1 — the point-map dual relation `picDual(rπ − s) = rV − s`

The Pic⁰ dual of `β := rπ − s` is `rV − s` *as a point endomorphism*.  We obtain it from the
shipped III.6.1(a) **dual uniqueness** `Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq`: the dual is
the unique point map `δ` with `δ ∘ β = [deg β]`, and `r·V − s` (= `β_dual.toAddMonoidHom`) is such a
`δ` by the point-map Vieta `(rV−s) ∘ (rπ−s) = [N] = [deg β]` (the shipped
`genuine_dual_comp_toAddMonoidHom_eq_mulByInt`, since `deg(rπ−s) = N` is exactly what Wall C will
conclude — but at the *point-map* level the Vieta gives `β_dual ∘ β = [N]` unconditionally).

To keep this a clean witness-parametric link we phrase it on a general `β` with a `CoordHom`,
taking the III.3.4 naturality and the two surjectivities as named residual hypotheses, and the
dual-defining composite as the hypothesis `hβ_comp` (which a caller supplies from the Vieta). -/

omit [Fintype K] [Fintype W.toAffine.Point] in
/-- **Pic⁰ dual = the prescribed point map (III.6.1(a) uniqueness), `finrank` exponent.**

For an endomorphism `β` of `E` with a coordinate-ring restriction `ch`, and a point endomorphism
`δ := β_dual.toAddMonoidHom` satisfying the dual-defining relation `δ ∘ β = [finrank R R]`, the
Pic⁰ dual `picDual β` equals `δ`.  This is a thin specialisation of the shipped
`Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq` (III.6.1(a)), exposed in the Route-C namespace so
the downstream assembly reads `picDual β = (rV − s)`.

Residuals (named hypotheses): `hnat` (III.3.4 naturality), `hsurjDual`/`hsurjβ` (the two point-map
surjectivities, automatic over `K̄`). -/
theorem picDual_eq_pointMap
    {β : Isogeny W.toAffine W.toAffine} (ch : β.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hnat : β.Naturality ch hinj hfin)
    (hsurjDual : Function.Surjective (β.picDual ch hinj hfin))
    (hsurjβ : Function.Surjective β.toAddMonoidHom)
    {δ : W.toAffine.Point →+ W.toAffine.Point}
    (hβ_comp : δ.comp β.toAddMonoidHom =
      (mulByInt W.toAffine (letI := ch.toAlgebra;
        ((@Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
          ch.toAlgebra.toModule : ℕ) : ℤ))).toAddMonoidHom) :
    β.picDual ch hinj hfin = δ :=
  Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq ch hinj hfin hnat hsurjDual hsurjβ hβ_comp

/-! ### Phase 2 — upgrade the Pic⁰ point-map dual to a full-isogeny `IsDualOf`, then Wall C

The Pic⁰ dual lives at the **point-map** level (`picDual β : E.Point →+ E.Point`).  To feed Wall C
(`signed_degree_of_genuine_dual_pair`, which consumes a *full-isogeny* `IsDualOf β_dual β`) we
upgrade the two point-map composition halves to full-isogeny equalities.  Both halves are
`α̂ ∘ α = α ∘ α̂ = [deg]` (Silverman III.6.2(a)), available at the point-map level from the shipped
`picDual_comp_toAddMonoidHom_of_surjective` (`α̂ ∘ α`) and `toAddMonoidHom_comp_picDual`
(`α ∘ α̂`).  The comorphism upgrade is the genuine-isogeny extensionality `genuine_isogeny_ext`
(the GapSpines "Wall-B killer"): two isogenies that are **genuine with the same geometric action**
and have equal point maps are equal.

We package the upgrade abstractly: given a genuine `β_dual` whose point map is the Pic⁰ dual of
`β` and whose composites with `β` are genuine with the `[N]`-action, we obtain the full
`IsDualOf β_dual β` and the composition equality `β_dual.comp β = [N]`, hence `deg β = N` by
Wall C. -/

/-- **Full-isogeny dual composition from a genuine point-map identity (comorphism upgrade).**

If `β_dual.comp β` and `[M]` are **genuine with the same geometric action** (`hgenLeft`,
`hgenRight`) and agree as point maps (`hhom`), then they are *equal as isogenies*:
`β_dual.comp β = mulByInt W M`.  This is the `genuine_isogeny_ext` upgrade specialised to the
composition `β_dual ∘ β` vs the scalar `[M]` — the step that lifts the Pic⁰ **point-map** dual
relation to the **full-isogeny** level Wall C needs.

The point-map identity `hhom` is exactly the shipped picDual composite (`α̂ ∘ α = [deg]`,
`picDual_comp_toAddMonoidHom_of_surjective`); the genuineness witnesses `hgenLeft`/`hgenRight` are
the genuine-comorphism residual (for `[M]` it is the shipped `mulByInt_isGenuineWith`). -/
theorem comp_eq_mulByInt_of_genuine
    {β β_dual : Isogeny W.toAffine W.toAffine} (M : ℤ)
    {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hgenLeft : IsGenuineWith W (β_dual.comp β) g)
    (hgenRight : IsGenuineWith W (mulByInt W.toAffine M) g)
    (hhom : (β_dual.comp β).toAddMonoidHom = (mulByInt W.toAffine M).toAddMonoidHom) :
    β_dual.comp β = mulByInt W.toAffine M :=
  genuine_isogeny_ext W hgenLeft hgenRight hhom

/-- **`IsDualOf β_dual β` from the Pic⁰ two-sided point-map relation (comorphism upgrade).**

Silverman III.6.2(a) gives `β̂ ∘ β = β ∘ β̂ = [deg β]` for the Pic⁰ dual `β̂ = picDual β`.  When
`β_dual` is a genuine isogeny whose **point map is `picDual β`** (`hdual_hom`), the two point-map
composites upgrade (via `comp_eq_mulByInt_of_genuine`) to the *full-isogeny* identities
`β_dual.comp β = [deg β]` and `β.comp β_dual = [deg β]`, i.e. `IsDualOf β_dual β`.

The two point-map composites are the shipped III.6.2(a) facts at the `[deg β]` (= `degree`)
exponent:
* `β_dual.toAddMonoidHom.comp β.toAddMonoidHom = [deg β]` — from
  `picDual_comp_toAddMonoidHom_of_surjective_degree` rewritten by `hdual_hom`;
* `β.toAddMonoidHom.comp β_dual.toAddMonoidHom = [deg β]` — from
  `toAddMonoidHom_comp_picDual_degree` rewritten by `hdual_hom`.

Residuals (named): the picDual data `ch`/`hnat`/`hsurjDual` (the `α̂ ∘ α` half right-cancels the
surjective `α̂`, so only `picDual`-surjectivity is needed here), the fraction-field tower witness
`(S, S')` for the `finrank ↔ degree` bridge, the genuineness witnesses for both composites
(`hgenL₁/hgenL₂` with the common action `g` and `[deg β]`-genuineness via `mulByInt_isGenuineWith`),
and `hdual_hom` (= `β_dual.toAddMonoidHom = picDual β`, the dual-additivity output `rV − s`). -/
theorem isDualOf_of_picDual
    {β β_dual : Isogeny W.toAffine W.toAffine} (ch : β.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hnat : β.Naturality ch hinj hfin)
    (hsurjDual : Function.Surjective (β.picDual ch hinj hfin))
    (hdual_hom : β_dual.toAddMonoidHom = β.picDual ch hinj hfin)
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ = β.degree)
    {g₁ g₂ : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hgenL₁ : IsGenuineWith W (β_dual.comp β) g₁)
    (hgenR₁ : IsGenuineWith W (mulByInt W.toAffine (β.degree : ℤ)) g₁)
    (hgenL₂ : IsGenuineWith W (β.comp β_dual) g₂)
    (hgenR₂ : IsGenuineWith W (mulByInt W.toAffine (β.degree : ℤ)) g₂) :
    IsDualOf W.toAffine β_dual β := by
  -- Point-map half 1: `β_dual ∘ β = [deg β]` (III.6.2(a), `α̂ ∘ α`).
  have hhom₁ : (β_dual.comp β).toAddMonoidHom =
      (mulByInt W.toAffine (β.degree : ℤ)).toAddMonoidHom := by
    rw [Isogeny.comp_toAddMonoidHom, hdual_hom]
    exact Isogeny.picDual_comp_toAddMonoidHom_of_surjective_degree ch hinj hfin hnat hsurjDual
      S S' hSR hS'FF
  -- Point-map half 2: `β ∘ β_dual = [deg β]` (III.6.2(a)/III.6.1, `α ∘ α̂`).
  have hhom₂ : (β.comp β_dual).toAddMonoidHom =
      (mulByInt W.toAffine (β.degree : ℤ)).toAddMonoidHom := by
    rw [Isogeny.comp_toAddMonoidHom, hdual_hom]
    exact Isogeny.toAddMonoidHom_comp_picDual_degree ch hinj hfin hnat S S' hSR hS'FF
  -- Comorphism upgrade of both halves; `[deg β]` is genuine via `mulByInt_isGenuineWith`.
  exact ⟨comp_eq_mulByInt_of_genuine W (β.degree : ℤ) hgenL₁ hgenR₁ hhom₁,
    comp_eq_mulByInt_of_genuine W (β.degree : ℤ) hgenL₂ hgenR₂ hhom₂⟩

/-! ### Phase 2 (cont.) — `deg(rπ − s) = N` via Wall C, on the genuine `rπ − s` family

Specialise to `β := genuineIsogSmulSub W r s = rπ − s`.  The two inputs Wall C
(`signed_degree_of_genuine_dual_pair`) consumes are now both **produced from the Pic⁰ machinery**:

* `IsDualOf β_dual β` — from `isDualOf_of_picDual` (Phase 2);
* `β_dual.comp β = [N]` — the full-isogeny Vieta, obtained by the comorphism upgrade
  `comp_eq_mulByInt_of_genuine` of the shipped *point-map* Vieta
  `genuine_dual_comp_toAddMonoidHom_eq_mulByInt` (which itself reduces to `IsDualOf V π` + the
  sum-trace `π + V = [t]`).

`0 < deg β` is discharged here unconditionally (`genuineIsogSmulSub_degree_pos`). -/

/-- **Route C: `deg(rπ − s) = N` from the Pic⁰ dual chain (Wall C extraction).**

For the genuine `β := rπ − s` (`genuineIsogSmulSub W r s`), the SIGNED III.6.3 degree identity

  `deg(rπ − s) = q·r² − t·r·s + s²`   (`= N`)

is produced by feeding into Wall C (`signed_degree_of_genuine_dual_pair`):
* the full-isogeny dual `IsDualOf β_dual β` supplied by `h_isDual` (Phase-2 `isDualOf_of_picDual`
  output, carried here as a named hypothesis so this theorem is route-agnostic about *how* the
  Pic⁰ `IsDualOf` was assembled);
* the full-isogeny Vieta `β_dual.comp β = [N]`, upgraded from the **shipped point-map Vieta**
  `genuine_dual_comp_toAddMonoidHom_eq_mulByInt` by the comorphism step
  `comp_eq_mulByInt_of_genuine` and the composition-genuineness witnesses `hgenComp`/`hgenN`.

Residuals (named): `V` + `h_isDual_V_pi` (`IsDualOf V π`) + `h_sum_trace` (`π + V = [t]`) +
`h_beta_dual_hom` (`β_dual = r·V − s` at the point level — the dual-additivity output) feed the
point-map Vieta; `hgenComp`/`hgenN` are the composition-genuineness (comorphism upgrade); `h_isDual`
is the Pic⁰ full-isogeny dual; `hN_ne` is `N ≠ 0`. -/
theorem degree_eq_N
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (hN_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0)
    {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hgenComp : IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)) g)
    (hgenN : IsGenuineWith W
      (mulByInt W.toAffine ((Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)) g)
    (h_isDual : IsDualOf W.toAffine β_dual (genuineIsogSmulSub W r s hr hs hrK hsK)) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  -- Full-isogeny Vieta `β_dual ∘ (rπ−s) = [N]`: comorphism upgrade of the shipped point-map Vieta.
  have h_comp_eq : β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK) =
      mulByInt W.toAffine ((Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2) :=
    comp_eq_mulByInt_of_genuine W _ hgenComp hgenN
      (genuine_dual_comp_toAddMonoidHom_eq_mulByInt W hq r s hr hs hrK hsK V β_dual
        h_isDual_V_pi h_sum_trace h_beta_dual_hom)
  -- Wall C: `[deg β] = β_dual ∘ β = [N]` ⟹ `deg β = N` (mulByInt injectivity).
  exact signed_degree_of_genuine_dual_pair
    (genuineIsogSmulSub W r s hr hs hrK hsK) β_dual _ hN_ne h_isDual
    (genuineIsogSmulSub_degree_pos W r s hr hs hrK hsK) h_comp_eq

/-! ### Phase 3 — `qf_nonneg` (generic case) and the fully-wired Route-C assembly

`deg(rπ − s) = N` with `deg ≥ 0` (a degree is a `ℕ`) gives `0 ≤ N` for the generic `(r, s)`.
We expose this directly, and then the **fully-wired** top-level theorem in which `degree_eq_N`'s
abstract `h_isDual` hypothesis is *itself produced* by the Phase-2 `isDualOf_of_picDual`, so the
top-level residual list is exactly the Pic⁰ data — `ch`, `hnat`, `hsurjDual`, the `finrank ↔
degree` tower `(S, S')`, `hdual_hom` (`β_dual = picDual β`), and the four genuineness witnesses
(two for the `IsDualOf` halves, two for the Vieta composite) — plus the Vieta point-map inputs
(`V`, `h_isDual_V_pi`, `h_sum_trace`, `h_beta_dual_hom`) and `hN_ne`. -/

omit [Fintype W.toAffine.Point] in
/-- **Route C: `qf_nonneg` at a single generic `(r, s)` from `deg(rπ − s) = N`.**

Once `deg(rπ − s) = N` (e.g. from `degree_eq_N`), non-negativity `0 ≤ N` of the quadratic-form
value is immediate, since `deg(rπ − s)` is a natural number cast to `ℤ`.  This is the Leaf-1
conclusion `qf_nonneg` for the generic case, packaged as a function of the degree identity. -/
theorem qf_nonneg_of_degree_eq_N
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (h_deg : ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2) :
    0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  rw [← h_deg]
  exact Int.natCast_nonneg _

/-- **Route C, FULLY WIRED: `deg(rπ − s) = N` with the Pic⁰ `IsDualOf` assembled in-line.**

The end-to-end Pic⁰-dual route to the SIGNED III.6.3 degree identity `deg(rπ − s) = N`, with the
`IsDualOf β_dual (rπ − s)` hypothesis of `degree_eq_N` **discharged internally** by the Phase-2
`isDualOf_of_picDual` (the Pic⁰ two-sided dual relation, comorphism-upgraded).  The full residual
list is now exactly the named hypotheses below — see the file header for the deep-vs-routine split.

`β` is the genuine `rπ − s`; `β_dual` is its (genuine) Pic⁰ dual whose point map is `picDual β`
(`hdual_hom`) and which on points is `r·V − s` (`h_beta_dual_hom`) — these two descriptions are
the *same* point map (both equal the Silverman dual), so a caller supplies a single `β_dual`
satisfying both.

Chain: `isDualOf_of_picDual` (Pic⁰ `IsDualOf`) → `degree_eq_N` (Wall C). -/
theorem degree_eq_N_via_picDual
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    -- Vieta (point-map) inputs:
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (hN_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0)
    -- Pic⁰ dual data for `β = rπ − s`:
    (ch : (genuineIsogSmulSub W r s hr hs hrK hsK).CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hnat : (genuineIsogSmulSub W r s hr hs hrK hsK).Naturality ch hinj hfin)
    (hsurjDual :
      Function.Surjective ((genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin))
    (hdual_hom :
      β_dual.toAddMonoidHom = (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin)
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ =
      (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    -- Genuineness (comorphism upgrade) witnesses:
    {g₁ g₂ gComp : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hgenL₁ : IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)) g₁)
    (hgenR₁ : IsGenuineWith W
      (mulByInt W.toAffine ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ)) g₁)
    (hgenL₂ : IsGenuineWith W ((genuineIsogSmulSub W r s hr hs hrK hsK).comp β_dual) g₂)
    (hgenR₂ : IsGenuineWith W
      (mulByInt W.toAffine ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ)) g₂)
    (hgenComp : IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)) gComp)
    (hgenN : IsGenuineWith W
      (mulByInt W.toAffine ((Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)) gComp) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  -- Phase 2: assemble the full-isogeny `IsDualOf β_dual (rπ − s)` from the Pic⁰ relation.
  have h_isDual : IsDualOf W.toAffine β_dual (genuineIsogSmulSub W r s hr hs hrK hsK) :=
    isDualOf_of_picDual W ch hinj hfin hnat hsurjDual hdual_hom S S' hSR hS'FF
      hgenL₁ hgenR₁ hgenL₂ hgenR₂
  -- Phase 2 (cont.) + Wall C: extract the SIGNED degree.
  exact degree_eq_N W hq r s hr hs hrK hsK V β_dual h_isDual_V_pi h_sum_trace h_beta_dual_hom
    hN_ne hgenComp hgenN h_isDual

/-- **Route C, TOP-LEVEL: `qf_nonneg` at a generic `(r, s)` via the Pic⁰ dual chain.**

The Leaf-1 conclusion `0 ≤ q·r² − t·r·s + s²` for a *generic* `(r, s)` (both `r, s` nonzero in
both `ℤ` and `K`), assembled entirely along the **Pic⁰ dual route**:

  `degree_eq_N_via_picDual` (Pic⁰ `IsDualOf` + Vieta + Wall C ⟹ `deg(rπ−s) = N`)
  → `qf_nonneg_of_degree_eq_N` (`deg ≥ 0` ⟹ `0 ≤ N`).

This is the Route-C analogue of the generic branch of the (retired) legacy chain
`degree_quadratic_exists_skeleton_nonzero` / `genuineIsogSmulSub_degree_eq_signed`.
It closes that branch modulo exactly the named residuals
of `degree_eq_N_via_picDual` (the Pic⁰ data + genuineness + Vieta inputs + `hN_ne`); the edge cases
`r = 0`, `s = 0`, char-divisible are handled separately by the shipped edge lemmas and are *not*
part of Route C. -/
theorem qf_nonneg_generic_via_picDual
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (hN_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0)
    (ch : (genuineIsogSmulSub W r s hr hs hrK hsK).CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hnat : (genuineIsogSmulSub W r s hr hs hrK hsK).Naturality ch hinj hfin)
    (hsurjDual :
      Function.Surjective ((genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin))
    (hdual_hom :
      β_dual.toAddMonoidHom = (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin)
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ =
      (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    {g₁ g₂ gComp : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hgenL₁ : IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)) g₁)
    (hgenR₁ : IsGenuineWith W
      (mulByInt W.toAffine ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ)) g₁)
    (hgenL₂ : IsGenuineWith W ((genuineIsogSmulSub W r s hr hs hrK hsK).comp β_dual) g₂)
    (hgenR₂ : IsGenuineWith W
      (mulByInt W.toAffine ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ)) g₂)
    (hgenComp : IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)) gComp)
    (hgenN : IsGenuineWith W
      (mulByInt W.toAffine ((Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)) gComp) :
    0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 :=
  qf_nonneg_of_degree_eq_N W hq r s hr hs hrK hsK
    (degree_eq_N_via_picDual W hq r s hr hs hrK hsK V β_dual h_isDual_V_pi h_sum_trace
      h_beta_dual_hom hN_ne ch hinj hfin hnat hsurjDual hdual_hom S S' hSR hS'FF
      hgenL₁ hgenR₁ hgenL₂ hgenR₂ hgenComp hgenN)

/-! ### Phase 4 — discharging the ROUTINE genuineness residuals (`mulByInt_isGenuineWith`)

`degree_eq_N_via_picDual` takes **six** `IsGenuineWith` witnesses, paired into three
`(left, right)` couples that the comorphism-upgrade `comp_eq_mulByInt_of_genuine` consumes:

* `(hgenL₁, hgenR₁)` for the half `β_dual ∘ β` vs `[deg β]`;
* `(hgenL₂, hgenR₂)` for the half `β ∘ β_dual` vs `[deg β]`;
* `(hgenComp, hgenN)` for the Vieta composite `β_dual ∘ β` vs `[N]`.

In every couple the *right* member is genuineness of a **scalar** `[M]` (`[deg β]` or `[N]`), which
is shipped **axiom-clean** by `mulByInt_isGenuineWith W M (M ≠ 0)` with geometric action
`zsmulPointHom W M`.  Fixing the shared action `gᵢ := zsmulPointHom W M` *discharges* the three
right members; the three *left* members then become exactly the V-side genuine-comorphism residual
(`β_dual ∘ β`, `β ∘ β_dual` are genuine **with the `[M]`-action** — the deep Wall-B input, supplied
by the shipped `genuineIsogSmulSub_comp_isGenuineWith_mulByInt` route from V-side functorial data).

`[deg β] ≠ 0` is `genuineIsogSmulSub_degree_pos`; `[N] ≠ 0` is `hN_ne`. -/

/-- **Route C, REDUCED: `deg(rπ − s) = N`, with the ROUTINE genuineness residuals discharged.**

This is `degree_eq_N_via_picDual` with its three *scalar-side* genuineness witnesses `hgenR₁`,
`hgenR₂`, `hgenN` **discharged internally** from the shipped axiom-clean `mulByInt_isGenuineWith`
(`[deg β]`-side via `genuineIsogSmulSub_degree_pos`, `[N]`-side via `hN_ne`), with the three shared
geometric actions pinned to `zsmulPointHom W (·)`.  The remaining hypotheses are exactly the
**deep** residuals plus the per-isogeny `CoordHom` data and `hN_ne`:

* **Deep (universal `hnat`, instance-diamond):** `hnat` (III.3.4 naturality of `κ`).
* **Deep (over `K̄`):** `hsurjDual` (surjectivity of `picDual β`).
* **Deep (genuine-comorphism, V-side):** `hgenL₁`, `hgenL₂`, `hgenComp` — `β_dual ∘ β`, `β ∘ β_dual`
  genuine **with the `[deg β]`/`[N]` action** (the Wall-B comorphism upgrade for the V-side
  `β_dual = r·V − s`).
* **Deep Vieta bundle (point-map level):** `V`, `h_isDual_V_pi`, `h_sum_trace`, `h_beta_dual_hom`.
  Of these `h_isDual_V_pi : IsDualOf V π` is *itself* dischargeable in isolation from the shipped
  `verschiebung_dual_exists W hq`; but it is **coupled** to the *named* `V` that the genuinely-deep
  `h_sum_trace` (the III.8 trace identity `π + V = [t]`) and `h_beta_dual_hom` (`β_dual = r·V − s`)
  refer to.  Removing it would force `∀`-quantifying those deep facts over every dual `V` — heavier,
  not a real reduction — so it is **folded** into the deep Vieta bundle (documented, no `sorry`).
* **Per-isogeny `CoordHom` data:** `ch`, `hinj`, `hfin`, the `finrank ↔ degree` tower `(S, S')` with
  `hSR`/`hS'FF`, and `hdual_hom` (`β_dual = picDual β`).
* **Bookkeeping:** `hN_ne` (`N ≠ 0`; `qf_nonneg` handles `N = 0` directly).

`#print axioms`-clean: witness-parametric on the deep residuals + `CoordHom` data + `hN_ne`. -/
theorem degree_eq_N_via_picDual_reduced
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    -- Deep Vieta bundle (point-map level; `h_isDual_V_pi` folded — see docstring):
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (hN_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0)
    -- Per-isogeny `CoordHom` data for `β = rπ − s`:
    (ch : (genuineIsogSmulSub W r s hr hs hrK hsK).CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hnat : (genuineIsogSmulSub W r s hr hs hrK hsK).Naturality ch hinj hfin)
    (hsurjDual :
      Function.Surjective ((genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin))
    (hdual_hom :
      β_dual.toAddMonoidHom = (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin)
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ =
      (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    -- Deep genuine-comorphism residuals (V-side), with the action PINNED to `zsmulPointHom`:
    (hgenL₁ : IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK))
      (zsmulPointHom W ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ)))
    (hgenL₂ : IsGenuineWith W ((genuineIsogSmulSub W r s hr hs hrK hsK).comp β_dual)
      (zsmulPointHom W ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ)))
    (hgenComp : IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK))
      (zsmulPointHom W ((Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2))) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  -- `[deg β] ≠ 0` (shipped) ⟹ discharge the two `[deg β]`-side genuineness witnesses.
  have hdeg_ne : ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) ≠ 0 := by
    exact_mod_cast (genuineIsogSmulSub_degree_pos W r s hr hs hrK hsK).ne'
  -- Discharge `hgenR₁`, `hgenR₂` from `mulByInt_isGenuineWith` at `[deg β]`,
  -- and `hgenN` at `[N]` (using `hN_ne`); each pins the action `zsmulPointHom W (·)`.
  exact degree_eq_N_via_picDual W hq r s hr hs hrK hsK V β_dual h_isDual_V_pi h_sum_trace
    h_beta_dual_hom hN_ne ch hinj hfin hnat hsurjDual hdual_hom S S' hSR hS'FF
    hgenL₁ (mulByInt_isGenuineWith W _ hdeg_ne)
    hgenL₂ (mulByInt_isGenuineWith W _ hdeg_ne)
    hgenComp (mulByInt_isGenuineWith W _ hN_ne)

/-- **Route C, REDUCED TOP-LEVEL: `qf_nonneg` at a generic `(r, s)`, routine residuals discharged.**

The Leaf-1 conclusion `0 ≤ q·r² − t·r·s + s²` for a generic `(r, s)`, assembled along the **Pic⁰
dual route** with the three scalar-side genuineness residuals discharged (see
`degree_eq_N_via_picDual_reduced`).  The residual list is now exactly the **deep** Pic⁰ residuals
(`hnat`, `hsurjDual`, the V-side genuine-comorphism `hgenL₁`/`hgenL₂`/`hgenComp`, the deep Vieta
bundle `V`/`h_isDual_V_pi`/`h_sum_trace`/`h_beta_dual_hom`), the per-isogeny `CoordHom` data
(`ch`/`hinj`/`hfin`/`(S, S')`/`hdual_hom`), and the bookkeeping `hN_ne`.

`#print axioms`-clean.  Chain: `degree_eq_N_via_picDual_reduced` → `qf_nonneg_of_degree_eq_N`. -/
theorem qf_nonneg_generic_via_picDual_reduced
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (hN_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0)
    (ch : (genuineIsogSmulSub W r s hr hs hrK hsK).CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hnat : (genuineIsogSmulSub W r s hr hs hrK hsK).Naturality ch hinj hfin)
    (hsurjDual :
      Function.Surjective ((genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin))
    (hdual_hom :
      β_dual.toAddMonoidHom = (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin)
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ =
      (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    (hgenL₁ : IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK))
      (zsmulPointHom W ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ)))
    (hgenL₂ : IsGenuineWith W ((genuineIsogSmulSub W r s hr hs hrK hsK).comp β_dual)
      (zsmulPointHom W ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ)))
    (hgenComp : IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK))
      (zsmulPointHom W ((Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2))) :
    0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 :=
  qf_nonneg_of_degree_eq_N W hq r s hr hs hrK hsK
    (degree_eq_N_via_picDual_reduced W hq r s hr hs hrK hsK V β_dual h_isDual_V_pi h_sum_trace
      h_beta_dual_hom hN_ne ch hinj hfin hnat hsurjDual hdual_hom S S' hSR hS'FF
      hgenL₁ hgenL₂ hgenComp)

end HasseWeil.Pic0.RouteC
