/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.GammaH
import ModularCurves.Moduli.LevelSpaces

/-!
# STREAM-YFULL: the Y(N) representability route (T-E9)

The route of record for `gammaFullNaive_representable` (`Moduli/Representability.lean`,
T-E9 milestone): for `N ≥ 3` with `N` invertible in `R`, the naive full-level problem
`[Γ(N)]` is rigid and representable, and the representing base is smooth and affine over
`Spec R`.

**ROUTE DECISION (this stream's Phase-1e verdict; full analysis in
`.mathlib-quality/decomposition-yfull-route.md`): via the amended, ⇐-affine T-E5 = KM
SCHOLIE 4.7.0**, i.e. KM's own proof of Cor 4.7.2 — *"This results from 4.7.1 above,
thanks to the rigidity 2.7.2 and the relative representability 3.7.1 of naive level N
structures"* (KM p. 117) — and NOT via a direct T-E7-style Tate-normal-form construction.
This file supplies the two `P`-specific inputs the KM engine consumes and the assembly:

1. **Relative representability + affineness over `(Ell)`** (KM 3.6.0/3.7.1; Loeffler
   Prop 3.8.2): the presentation is the PROVEN closed full-level locus `levelSpaceΓ`
   (`Moduli/LevelSpaces.lean`, KM's divisor-equality register) sitting inside
   `E[N] ×_S E[N]` — finite affine over `S` outright, étale once it is clopen. The
   Weil-pairing OPEN locus of Loeffler 3.8.2 is **not** load-bearing here: it is one of
   two discharge routes for the single clopen leaf `isOpenImmersion_levelSpaceΓι`
   ([YF-CLOPEN]; the other is KM 3.7.1's étale-local constancy), so T-C1 is *not* on this
   stream's critical path.
2. **Rigidity** (KM 2.7.2(1); Loeffler Prop 3.8.3 for `H = {1}`): reduction of the
   moduli-problem statement to the linchpin `aut_trivial_of_fullLevel`
   (`Moduli/Groupoid.lean`, GME 2.6.4 register), which is one gate from done
   (CHARTER-P3B3 milestone 2). The locally-noetherian hypothesis mismatch is isolated in
   the single leaf `gammaFullNaive_rigid` ([YF-NOETH]).
3. **The engine call**: `representable_iff` ⇐ (`Moduli/EllCategory.lean`, T-E5, KM
   SCHOLIE 4.7.0 verbatim after the B2 amendment) — its `sorry` is CHARTER-FP4's
   milestone (T-E5c route (a) + T-E15 + T-E14 + recollement T-E5f). **Cited, never
   rebuilt here.**
4. **The geometric conjuncts** (KM 4.7.1/4.7.2 "smooth affine curve"): a transport
   principle (all representing objects are canonically isomorphic) reduces them to the
   engine's constructed object, whose smooth-affineness is the KM 4.7.1 computation —
   gated on the engine's construction ([YF-GEOM]) plus the étale presentation of this
   file and the étale-descent-of-smoothness helper `smooth_of_etale_surjective`.

The final assembly `gammaFullNaive_representable_assembly` has **exactly** the statement
shape of the held `gammaFullNaive_representable`, so discharging T-E9 from this stream is
a one-line `exact` once the owning worker wires it.

Sources: [KM] SCHOLIE 4.7.0 (p. 111), engine p. 112, Cor 4.7.1 (p. 116), Cor 4.7.2
(p. 117), Cor 2.7.2 (p. 85), Thm 3.7.1 (p. 104), First Main Theorem 5.1.1 (p. 129)
(PDF = print + 11); [Loe] Fact 3.8.1, Prop 3.8.2, Prop 3.8.3 (§3.8, p. 19). Verbatim
quotes per leaf: `.mathlib-quality/decomposition-yfull-route.md`.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace YFull

variable (R : CommRingCat.{u})

/-! ### Invertibility and killing dictionaries -/

/-- **([YF-NINV])** `N` invertible in `R` is `N` invertible on every `R`-scheme: the
structure morphism's global-sections ring map carries the unit `N : Rˣ` to `Γ(X, ⊤)`.
Source: implicit throughout KM 3.7/4.7 ("`S` a `ℤ[1/N]`-scheme"); [Loe] §3.8 base
`Ell/ℤ[1/N]`. Attack: `Scheme.ΓSpecIso R` + `Scheme.Hom.appTop f` + `IsUnit.map` +
`map_natCast`. -/
theorem nIsInvertible_over_spec {N : ℕ} {X : Scheme.{u}} (f : X ⟶ Spec R)
    (h : IsUnit (N : R)) : NIsInvertible X N := by
  show IsUnit ((N : ℕ) : Γ(X, ⊤))
  have h1 : IsUnit ((N : ℕ) : Γ(Spec R, ⊤)) := by
    have h2 := h.map (Scheme.ΓSpecIso R).inv.hom
    rwa [map_natCast] at h2
  have h3 := h1.map f.appTop.hom
  rwa [map_natCast] at h3

/-- **([YF-KILL])** The raw killing equation of the torsion pullback (`P ≫ [N] = 0`,
the `levelSpaceΓ_spec` register) is the group-theoretic killing of the associated
section of the base-changed curve (the `IsNaiveFullLevel`/`IsFullLevel` register).
Source: KM 1.4/2.3 dictionary between `E[N]`-points and `N`-killed points; the two
registers are tied by `point_smul_eq_comp_mulBy` + `Point.asSection_zsmul`. -/
theorem point_killed_iff {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]
    {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    P.1 ≫ E.mulByHom N = g ≫ E.zero ↔
      (N : ℤ) • EllipticCurve.Point.asSection E g P = 0 := by
  rw [EllipticCurve.smul_eq_zero_iff_comp_mulByHom]
  -- `(E.baseChange g).E` is defeq to `pullback E.π g` only at default transparency, so
  -- everything below is term-mode `Eq.trans`/`congrArg` (the `asSection_zsmul` idiom).
  have hmf := EllipticCurve.mulByHom_baseChange_fst E g N
  have hms := EllipticCurve.mulByHom_baseChange_snd E g N
  have hsf := EllipticCurve.Point.asSection_val_fst E g P
  have hss := EllipticCurve.Point.asSection_val_snd E g P
  have hzf : (E.baseChange g).zero ≫ pullback.fst E.π g = g ≫ E.zero :=
    pullback.lift_fst _ _ _
  have hzs : (E.baseChange g).zero ≫ pullback.snd E.π g = 𝟙 T :=
    pullback.lift_snd _ _ _
  have lf : ((EllipticCurve.Point.asSection E g P).1 ≫ (E.baseChange g).mulByHom N) ≫
      pullback.fst E.π g = P.1 ≫ E.mulByHom N :=
    (Category.assoc _ _ _).trans <|
      (congrArg ((EllipticCurve.Point.asSection E g P).1 ≫ ·) hmf).trans <|
        (Category.assoc _ _ _).symm.trans <| congrArg (· ≫ E.mulByHom N) hsf
  have ls : ((EllipticCurve.Point.asSection E g P).1 ≫ (E.baseChange g).mulByHom N) ≫
      pullback.snd E.π g = 𝟙 T :=
    (Category.assoc _ _ _).trans <|
      (congrArg ((EllipticCurve.Point.asSection E g P).1 ≫ ·) hms).trans hss
  have rf : (𝟙 T ≫ (E.baseChange g).zero) ≫ pullback.fst E.π g = g ≫ E.zero :=
    (congrArg (· ≫ pullback.fst E.π g) (Category.id_comp _)).trans hzf
  have rs : (𝟙 T ≫ (E.baseChange g).zero) ≫ pullback.snd E.π g = 𝟙 T :=
    (congrArg (· ≫ pullback.snd E.π g) (Category.id_comp _)).trans hzs
  constructor
  · intro hk
    apply pullback.hom_ext
    · exact lf.trans (hk.trans rf.symm)
    · exact ls.trans rs.symm
  · intro hk
    exact lf.symm.trans ((congrArg (· ≫ pullback.fst E.π g) hk).trans rf)

/-! ### The relative presentation: `levelSpaceΓ` as the Γ(N)-scheme of `E/S`

KM 3.6.0 (p. 102): *"Each of these functors is represented by a finite S-scheme"*;
KM 3.7.1 (p. 104): over `ℤ[1/N]`, *"Each is represented by a finite etale S-scheme"*;
[Loe] Prop 3.8.2: *"PH is relatively representable and étale over Ell/ℤ[1/N]"*. -/

section Presentation

variable {R}
variable (X : EllObj R) (N : ℕ) [NeZero N]

/-- The Γ(N)-scheme of `X.curve/X.base`: the full-level locus `U_{Γ(N)}` inside
`E[N] ×_S E[N]` (T-D18/T-W8, PROVEN closed-subscheme presentation). This single scheme
carries both halves of [Loe] 3.8.2's presentation — KM's closed divisor-equality
condition cuts it out; Loeffler's Weil-pairing non-vanishing exhibits it as open. -/
noncomputable def fullLevelSpace : Scheme.{u} :=
  levelSpaceΓ X.curve N

/-- The structure morphism of the Γ(N)-scheme over the base of `X`: include into
`E[N] ×_S E[N]`, project to the first factor, then to `S`. -/
noncomputable def fullLevelSpaceStruct : fullLevelSpace X N ⟶ X.base :=
  levelSpaceΓι X.curve N ≫
    pullback.fst (X.curve.torsionπ N) (X.curve.torsionπ N) ≫ X.curve.torsionπ N

/-- **([YF-AFF], KM 4.7.0's standing hypothesis for `[Γ(N)]`)** The Γ(N)-presentation is
an affine morphism: closed immersion (affine) into `E[N] ×_S E[N]`, which is finite
(hence affine) over `S` by `torsionπ_isFinite` (PROVEN) and base-change/composition
stability. Provable now — no gates. -/
theorem isAffineHom_fullLevelSpaceStruct : IsAffineHom (fullLevelSpaceStruct X N) := by
  sorry

/-- **([YF-FIN] = the finiteness half of KM 3.6.0 / 5.1.1 for `[Γ(N)]`)** The
Γ(N)-presentation is finite over the base: KM 3.6.0 (p. 102) *"Each of these functors is
represented by a finite S-scheme"*; KM 5.1.1 (p. 129) *"Each is finite and flat over
(Ell)"* (the Γ(N) case, `N` invertible). Closed immersion ≫ finite ≫ finite. Provable
now — no gates. -/
theorem isFinite_fullLevelSpaceStruct : IsFinite (fullLevelSpaceStruct X N) := by
  sorry

end Presentation

/-- **([YF-CLOPEN] — the one genuinely new geometric leaf of this stream)** For `N`
invertible on `S`, the closed full-level locus is ALSO open in `E[N] ×_S E[N]`: the
inclusion is an open immersion. Two discharge routes, either sufficient:
(α) [Loe] Prop 3.8.2 (verbatim): *"it is an open subscheme of `E[N] ×_S E[N]` given by
non-vanishing of Weil pairings"* — consumes the `weilPairing` interface (T-C1 /
CHARTER-P2 phase 2);
(β) KM 3.7.1 (p. 104–105): étale-locally on `S`, `E[N] ≅ (ℤ/N)²` is constant
(*"reduce to the case when E[N] is the constant group-scheme (ℤ/NZ)²"*), the locus is a
union of connected components of the constant scheme (indexed by the bases of `(ℤ/N)²`),
hence clopen; clopen-ness descends along the étale cover — consumes `torsionπ_etale`
(BB-DIFF, CHARTER-P3B3) + étale-local trivialization of `E[N]` (T-B6 family).
GATE: [YF-CLOPEN] — T-C1 or the CHARTER-P3B3 étale toolkit; not buildable from the
current sorry-free layer alone. -/
theorem isOpenImmersion_levelSpaceΓι {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ)
    [NeZero N] (hinv : NIsInvertible S N) :
    IsOpenImmersion (levelSpaceΓι E N) := by
  sorry

/-- **([YF-ETALE] = the étale half of KM 3.7.1 / [Loe] 3.8.2 for `[Γ(N)]`)** For `N`
invertible in `R`, the Γ(N)-presentation is étale over the base: open immersion
([YF-CLOPEN]) ≫ pullback of finite étale ≫ finite étale, with `E[N] → S` étale from
`torsionπ_etale` (GATE: BB-DIFF `mulByHom_formallyUnramified`, CHARTER-P3B3 items 1–2).
KM 3.7.1 (verbatim, p. 104): *"Each is represented by a finite etale S-scheme."* -/
theorem etale_fullLevelSpaceStruct (X : EllObj R) (N : ℕ) [NeZero N]
    (hinv : IsUnit (N : R)) : Etale (fullLevelSpaceStruct X N) := by
  sorry

/-! ### The points dictionary: factorizations through `U_{Γ(N)}` are level structures -/

/-- **([YF-EQV-D], the Drinfeld points dictionary; KM 3.1 + T-D18)** Factorizations of
`g : T ⟶ X.base` through the Γ(N)-presentation biject with Drinfeld full level-`N`
structures on the base-changed curve, PINNED to the tautological correspondence: the
factorization classifying the torsion-point pair `(P, Q)` (via `levelSpaceΓ_spec`'s
`pullback.lift` of the two `pointToTorsion`s) maps to the pair of associated sections.
Ingredients (all PROVEN): `levelSpaceΓ_spec`, mono-ness of the closed immersion
`levelSpaceΓι`, the pullback point dictionary `Point.baseChangeEquiv`/`Point.asSection`,
`point_killed_iff` ([YF-KILL]). No gates. -/
theorem exists_pointsEquiv_drinfeld (X : EllObj R) (N : ℕ) [NeZero N]
    {T : Scheme.{u}} (g : T ⟶ X.base) :
    ∃ e : { h : T ⟶ fullLevelSpace X N // h ≫ fullLevelSpaceStruct X N = g } ≃
        (gammaFullDrinfeldProblem R N).obj (Opposite.op (X.pullbackAlong g)),
      ∀ (P Q : X.curve.Point g)
        (hP : P.1 ≫ X.curve.mulByHom N = g ≫ X.curve.zero)
        (hQ : Q.1 ≫ X.curve.mulByHom N = g ≫ X.curve.zero)
        (h : { h : T ⟶ fullLevelSpace X N // h ≫ fullLevelSpaceStruct X N = g }),
        h.1 ≫ levelSpaceΓι X.curve N =
          pullback.lift (X.curve.pointToTorsion P hP) (X.curve.pointToTorsion Q hQ)
            (by simp) →
        (e h).1 = (EllipticCurve.Point.asSection X.curve g P,
          EllipticCurve.Point.asSection X.curve g Q) := by
  sorry

/-- **([YF-EQV-N], the naive points dictionary; KM 3.7 / 1.4.4 register change)** The
Drinfeld dictionary composed with the T-D8 bridge (`isFullLevel_iff_naive`, GATE:
`fullLevel_divisor_iff_naive_gen` = T-D8-bridge box, CHARTER-P3B3 item 4) lands in the
NAIVE problem — the level-`N` avatar of KM 3.7.1's *"the situation when N is
invertible"*. Real wiring: `Equiv.subtypeEquivRight` along the bridge. -/
theorem exists_pointsEquiv_naive (X : EllObj R) (N : ℕ) [NeZero N]
    (hinv : IsUnit (N : R)) {T : Scheme.{u}} (g : T ⟶ X.base) :
    ∃ e : { h : T ⟶ fullLevelSpace X N // h ≫ fullLevelSpaceStruct X N = g } ≃
        (gammaFullNaiveProblem R N).obj (Opposite.op (X.pullbackAlong g)),
      ∀ (P Q : X.curve.Point g)
        (hP : P.1 ≫ X.curve.mulByHom N = g ≫ X.curve.zero)
        (hQ : Q.1 ≫ X.curve.mulByHom N = g ≫ X.curve.zero)
        (h : { h : T ⟶ fullLevelSpace X N // h ≫ fullLevelSpaceStruct X N = g }),
        h.1 ≫ levelSpaceΓι X.curve N =
          pullback.lift (X.curve.pointToTorsion P hP) (X.curve.pointToTorsion Q hQ)
            (by simp) →
        (e h).1 = (EllipticCurve.Point.asSection X.curve g P,
          EllipticCurve.Point.asSection X.curve g Q) := by
  obtain ⟨e₀, hpin⟩ := exists_pointsEquiv_drinfeld R X N g
  refine ⟨e₀.trans (Equiv.subtypeEquivRight fun PQ =>
    (X.pullbackAlong g).curve.isFullLevel_iff_naive N
      (nIsInvertible_over_spec R ((X.pullbackAlong g).structMap) hinv) PQ.1 PQ.2), ?_⟩
  intro P Q hP hQ h hlift
  exact hpin P Q hP hQ h hlift

/-- **([YF-NAT], the representing family with its naturality; the `AffineOverEll`
datum)** There is a single family of point-dictionaries, one per `g : T ⟶ X.base`,
commuting with restriction along every `k : T' ⟶ T` — the naturality clause of
`ModuliProblem.AffineOverEll` verbatim. Discharge: choose the PINNED equivalences of
[YF-EQV-N]; the pin determines each equivalence uniquely (the classifying morphism into
`E[N] ×_S E[N]` is determined by its two torsion-point legs, and `levelSpaceΓι` is a
monomorphism), and the pinned family is natural because both sides restrict points by
composition (`Point.restrict` vs `EllHom.pullSection` along `pullbackAlongMap`, tied by
`pullSection`'s defining `IsPullback.lift` equations). Source: [Loe] 3.7.1(3)'s
functor-of-points phrasing; KM 4.2. No gates beyond [YF-EQV-N]'s. -/
theorem exists_pointsEquiv_family (X : EllObj R) (N : ℕ) [NeZero N]
    (hinv : IsUnit (N : R)) :
    ∃ eqv : ∀ {T : Scheme.{u}} (g : T ⟶ X.base),
        { h : T ⟶ fullLevelSpace X N // h ≫ fullLevelSpaceStruct X N = g } ≃
          (gammaFullNaiveProblem R N).obj (Opposite.op (X.pullbackAlong g)),
      ∀ {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
        (h : { h : T ⟶ fullLevelSpace X N // h ≫ fullLevelSpaceStruct X N = g }),
        eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
          (gammaFullNaiveProblem R N).map (X.pullbackAlongMap g k).op (eqv g h) := by
  sorry

/-! ### The two engine inputs: `AffineOverEll` and `Rigid` -/

/-- **(T-E9 input 1 = KM 5.1.1 relative half for `[Γ(N)]` + KM 4.7.0's affineness;
[Loe] Prop 3.8.2)** The naive full-level problem is affine over `(Ell)`: relatively
representable by affine morphisms. Assembly of the presentation ([YF-AFF]) and the
natural family ([YF-NAT]). -/
theorem gammaFullNaive_affineOverEll (N : ℕ) [NeZero N] (hinv : IsUnit (N : R)) :
    (gammaFullNaiveProblem R N).AffineOverEll := by
  intro X
  obtain ⟨eqv, hnat⟩ := exists_pointsEquiv_family R X N hinv
  exact ⟨fullLevelSpace X N, fullLevelSpaceStruct X N,
    isAffineHom_fullLevelSpaceStruct X N, ⟨@eqv, @hnat⟩⟩

/-- **(KM First Main Theorem 5.1.1, the `[Γ(N)]` relative-representability clause —
p. 129: "Each of the four moduli problems … is relatively representable over (Ell)")**
Immediate from affineness over `(Ell)`. -/
theorem gammaFullNaive_relativelyRepresentable (N : ℕ) [NeZero N]
    (hinv : IsUnit (N : R)) : (gammaFullNaiveProblem R N).RelativelyRepresentable :=
  (gammaFullNaive_affineOverEll R N hinv).relativelyRepresentable

/-- **([YF-RIG-NOETH] = KM Cor 2.7.2(1) / [Loe] Prop 3.8.3 at `H = {1}`, per-object
form)** Over a locally noetherian base, no non-identity automorphism of `X` over
`𝟙 X.base` fixes a naive full level-`N` structure, `N ≥ 3` invertible. KM 2.7.2
(verbatim, p. 85): *"Let ε : E → E be an automorphism of an elliptic curve over a
connected base S. Let N ≥ 2 … Suppose that ε induces the identity automorphism of E[N].
(1) If N ≥ 3, then ε = id."* Reduction: a fixed point of `P.map e.hom.op` says the two
level sections are fixed by `e.hom.top` (via `pullSection`'s `IsPullback.lift_fst`
equation and `e.hom.baseHom = 𝟙`); repackage `e` as a pointed iso of `X.curve`
(`HomOver`, over_w from `e.hom.isPullback.w`, zero_w from `e.hom.zero_w`) and apply the
linchpin `aut_trivial_of_fullLevel` (GATE: its own boxes `torsionFixed_of_fixesLevel` +
`aut_endo_eq_one` PIC0-data — CHARTER-P3B3 milestone 2); conclude `e.hom.top = 𝟙`, hence
`e = Iso.refl X` by `EllHom.ext`, contradiction. -/
theorem gammaFullNaive_rigid_of_locallyNoetherian (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) (X : EllObj R) [IsLocallyNoetherian X.base]
    (e : X ≅ X) (hbase : e.hom.baseHom = 𝟙 X.base) (hne : e ≠ Iso.refl X)
    (a : (gammaFullNaiveProblem R N).obj (Opposite.op X)) :
    (gammaFullNaiveProblem R N).map e.hom.op a ≠ a := by
  sorry

/-- **(T-E9 input 2 = the rigid conjunct; KM 2.7.2 / [Loe] 3.8.3)** The naive
full-level problem is rigid for `N ≥ 3` invertible. GATE **[YF-NOETH]**: the linchpin
carries `[IsLocallyNoetherian S]` (from the project's degree machinery) while the moduli
problem quantifies over arbitrary bases; discharge routes: (α) noetherian-free
`End(E/S)` degree theory — KM Ch. 2's own argument needs only a connected base
(KM 2.6.2/2.7.2 verbatim), so the hypothesis is an artifact of the current engine;
(β) spreading out (EGA IV 8.8/11.2, the same machinery as CartierDivisor.lean's
remaining box): automorphism + level structure over affine `S` descend to a noetherian
subring. Until one lands, this leaf consumes [YF-RIG-NOETH] only over locally
noetherian bases. -/
theorem gammaFullNaive_rigid (N : ℕ) [NeZero N] (hN : 3 ≤ N) (hinv : IsUnit (N : R)) :
    (gammaFullNaiveProblem R N).Rigid := by
  sorry

/-! ### The engine call and the geometric conjuncts -/

/-- **(T-E9 representability = KM Cor 4.7.2 via SCHOLIE 4.7.0)** KM (verbatim, p. 117):
*"For N ≥ 3, the naive level N moduli problem of 4.6 is representable, by a smooth
affine curve Y(N) over Z[1/N]."* — this leaf is the representability clause, by the
engine: `representable_iff` ⇐ (T-E5, KM 4.7.0 — GATE: its sorry is the KM engine
`representable_of_rigid_of_torsor` + bootstrap instantiations, CHARTER-FP4) applied to
the two inputs above. Real wiring — compiles today, inherits exactly the cited gates. -/
theorem gammaFullNaive_representable_of_engine (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) : (gammaFullNaiveProblem R N).Representable :=
  ((gammaFullNaiveProblem R N).representable_iff
    (gammaFullNaive_affineOverEll R N hinv)).mpr
    ⟨gammaFullNaive_relativelyRepresentable R N hinv, gammaFullNaive_rigid R N hN hinv⟩

/-- **([YF-TRANS], smooth-affineness transports across representing objects)** Any two
objects representing the same moduli problem are canonically isomorphic in `Ell/R`
(Yoneda: `Functor.RepresentableBy.uniqueUpToIso`), the isomorphism's `baseHom` is an
isomorphism of schemes compatible with the structure morphisms (`EllHom.base_w`), and
`Smooth`/`IsAffineHom` respect isomorphisms — so if ONE representing object has smooth
affine base over `Spec R`, ALL do. Provable now (pure category theory + mathlib
`MorphismProperty` iso-stability). -/
theorem smooth_affine_of_representableBy {P : ModuliProblem R} {X₀ : EllObj R}
    (r₀ : P.RepresentableBy X₀) (hs : Smooth X₀.structMap)
    (ha : IsAffineHom X₀.structMap) (X : EllObj R)
    (hX : Nonempty (P.RepresentableBy X)) :
    Smooth X.structMap ∧ IsAffineHom X.structMap := by
  sorry

/-- **([YF-QSM], étale descent of smoothness — the KM 4.7.1 quotient step's geometry)**
If `π` is étale and surjective and `π ≫ f` is smooth, then `f` is smooth ("smooth is
étale-local on the source", Stacks 02K5/036U; KM applies it implicitly on p. 116–117:
`𝕸(𝒫) ⊗ ℤ[1/2] = 𝕸(𝒫, Legendre)/G` with the projection a finite étale `G`-torsor and
the total space a smooth curve). Self-contained ForMathlib-flavored helper for
[YF-GEOM]'s discharge. -/
theorem smooth_of_etale_surjective {X Y Z : Scheme.{u}} (π : X ⟶ Y) (f : Y ⟶ Z)
    [Etale π] (hπ : Function.Surjective π.base) (h : Smooth (π ≫ f)) : Smooth f := by
  sorry

/-- **([YF-GEOM] = KM Cor 4.7.1's geometric computation)** SOME representing object of
`[Γ(N)]` has smooth affine base over `Spec R`. KM 4.7.1 (verbatim, p. 116): *"Any
relatively representable moduli problem 𝒫 which is affine and etale over (Ell), and
rigid, is representable by a smooth affine curve over Z."* — its proof inspects the
engine's construction: `𝕸(𝒫) ⊗ ℤ[1/2] = 𝕸(𝒫, Legendre)/(free G)` and
`𝕸(𝒫) ⊗ ℤ[1/3] = 𝕸(𝒫, naive level 3)/(free G)`; each `𝕸(𝒫, δ)` is étale over the
smooth affine `𝕸(δ)` (this file's [YF-ETALE] at the bootstrap object + T-E15a/T-E14
explicit models), and smooth-affineness passes to the free finite quotient (T-Q3 affine
quotient, PROVEN + [YF-QSM]). GATE: the engine's constructed object (CHARTER-FP4;
same construction as `representable_iff`'s ⇐) + T-E15a + T-E14 + BB-DIFF. -/
theorem exists_representing_smooth_affine (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    ∃ X₀ : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X₀) ∧
      Smooth X₀.structMap ∧ IsAffineHom X₀.structMap := by
  sorry

/-! ### Assembly: the T-E9 statement -/

/-- **(T-E9 ASSEMBLY = KM Cor 4.7.2; the bridge into
`ModularCurves.gammaFullNaive_representable`)** For `N ≥ 3` invertible in `R`: `[Γ(N)]`
is rigid and representable, and every representing object has smooth affine base over
`Spec R`. Statement shape is VERBATIM that of the held
`Moduli/Representability.lean:gammaFullNaive_representable`, so the T-E9 milestone
discharges from this stream by `exact YFull.gammaFullNaive_representable_assembly …`
(one line, to be wired by the holder of that file). Real wiring over this file's
leaves. -/
theorem gammaFullNaive_representable_assembly (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    ((gammaFullNaiveProblem R N).Rigid ∧ (gammaFullNaiveProblem R N).Representable) ∧
      ∀ X : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by
  refine ⟨⟨gammaFullNaive_rigid R N hN hinv,
    gammaFullNaive_representable_of_engine R N hN hinv⟩, fun X hX => ?_⟩
  obtain ⟨X₀, ⟨r₀⟩, hs, ha⟩ := exists_representing_smooth_affine R N hN hinv
  exact smooth_affine_of_representableBy R r₀ hs ha X hX

end YFull

end ModularCurves
