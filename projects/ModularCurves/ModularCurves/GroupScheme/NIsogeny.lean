import ModularCurves.GroupScheme.CyclicSubgroup
import ModularCurves.GroupScheme.SubgroupQuotient
import ModularCurves.LevelStructure.Incidence

/-!
# Cyclic `N`-isogenies: KM Chapter 6 (STREAM-NISOG skeleton)

The moduli-facing theory of cyclic `N`-isogenies, exactly as KM Ch. 6 ("CYCLICITY",
print pp. 152–185) develops it: the scheme of generators `G^×` and the Main Theorem on
Cyclic Groups (KM 6.1.1), cyclicity as a closed condition on the base (KM 6.4.1 — ticket
`T-SG3`), the `[N-Isog]` moduli datum and its relative representability (KM 6.5.1, review-Q8
named block), standard cyclic subgroups and their quotients/factorizations (KM 6.7), and the
squarefree degeneration `[Γ₀(N)] = [N-Isog]` (KM 6.8.7). Everything is stated **RR-only**
(relative to a fixed `E : EllipticCurve S`; no global `(Ell)`-moduli), in the project's
divisor register: cyclicity of record is `IsGammaZeroFppf` (T-D10/T-SG2 — the review GATE).

Full decomposition artifact (verbatim KM quotes, per-leaf attacks, gates, DS-candidates):
`.mathlib-quality/decomposition-nisog.md`.

## Named gates used by the sorried leaves (never built here)
* **[T-G3D-INFRA]** — quotients `E/G` by finite locally free subgroup schemes
  (`GroupScheme/SubgroupQuotient.lean` interface; p0's active stream). The two DS-defs
  below (`quotientCurve`, `quotientHom`) are the *elliptic-curve upgrade* of that gate's
  output and are constructed only when the gate lands ([T-G3D-INFRA-CURVE]).
* **[KM-FMT-FLAT]** — KM 5.1.1 First Main Theorem flatness (`[Γ₁(N)]`, `[Γ₀(N)]` flat over
  `ℤ`), powering every KM "reduction to the universal case" + dense-open argument.
* **[KM-62-63-HOMOG]** — the KM 6.2/6.3 homogeneity block (Axiomatic Isomorphism Theorem
  6.2.1 + the formal-group determinant computation 6.3.2–6.3.6 at supersingular points).
* **[T-D10-FPPF]** — fppf-descent machinery (descending divisor identities along
  faithfully flat lfp covers), T-D10's proof layer.
* **[NISOG-GRASS]** — relative Grassmannian of quotients of a locally free sheaf (KM
  6.5.1's ambient projective scheme); absent from mathlib (only `RingTheory/Grassmannian`).
* **[KM-1.11.2]** — KM Ch. 1 surjectivity of induced generator maps for exact sequences of
  "cyclic" groups (consumed by KM 6.7.8).

## Sorry discipline
Every `sorry` below is **theorem-level** except the two DS-registered data defs
`FiniteLocallyFreeSubgroup.quotientCurve` and `FiniteLocallyFreeSubgroup.quotientHom`
(DS-NISOG-1/2 — see the artifact's DATA-SORRY list; consumers may use them only through
their pins, per the plan.md DS rule). All other data (`generatorSpace`,
`standardCyclicDivisor`, `standardCyclicSubgroup`, `imageDivisor`) are *real*
`Classical.choose` definitions off sorried existence theorems, with their specification
pins proved outright from `choose_spec`.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {S : Scheme.{u}}

/-! ### KM 6.4.3 — Mumford's flattening stratification (rank-`n` locus), dichotomy form

KM 6.4.3 (print p. 163, verbatim in the artifact): for `𝓕` coherent on noetherian `S` with
`dim_{k(s)}(𝓕 ⊗ k(s)) ≤ n`, the condition "`𝓕_T` locally free of rank `n`" is represented
by a closed subscheme `W ⊆ S`. We state the scheme-morphism avatar the cyclicity locus
actually consumes: the fibre bound is given in the dichotomy form KM's Lemma 6.4.2 produces
(fibres empty or finite locally free of rank `n`), and the represented condition is "the
pulled-back scheme is finite locally free of rank `n`". The general `≤ n` form is a
ForMathlib refinement recorded in the artifact ([NISOG-L12]). -/

-- ATTACK: (1) `n = 0`: the locus is "the fibre is empty", i.e. the complement of the image
-- — closed because `f` is finite (hence universally closed); the statement stays true.
-- (2) the bound hypothesis is NOT redundant: for `𝓕 = O_Z`, `Z ⊂ S` closed with generic
-- rank jumping above `n`, no closed `W` represents the rank-`n` condition (KM's own remark
-- that flattening needs the bound); the dichotomy form encodes the bound `≤ n` plus fibres
-- of rank `0` or `n` — exactly what Lemma 6.4.2 delivers for `G^×`. (3) Flatness of the
-- base change is demanded together with the rank equation: over non-reduced `T` the rank
-- function alone does not see flatness (`k[ε]`-fibre of a non-flat module can still have
-- constant fibre rank on points), so the RHS must carry `Flat` — KM's "locally free" says
-- both. Proof route (KM p. 163–164): local presentation `(O_U)^m →α (O_U)^n → 𝓕|U → 0`
-- with `W ∩ U = V(coefficients of α)`; converse by the splitting `β` and Cramer.
/-- **(KM 6.4.3, dichotomy form — the flattening-locus leaf)** Let `f : W ⟶ S` be finite and
locally of finite presentation, whose field-valued fibres are all either empty or finite
locally free of rank `n`. Then there is a closed subscheme `Z ⊆ S`, universal for "the base
change of `f` is finite locally free of rank `n`": `t : T ⟶ S` factors through `Z` iff
`pullback.snd f t` is flat with constant `finrank` equal to `n`. -/
theorem exists_locallyFreeRankLocus {W : Scheme.{u}} (f : W ⟶ S) [IsFinite f]
    [LocallyOfFinitePresentation f] (n : ℕ)
    (hb : ∀ (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ S),
      IsEmpty (pullback f t : Scheme.{u}) ∨
        (Flat (pullback.snd f t) ∧
          ∀ x : Spec (CommRingCat.of k), (pullback.snd f t).finrank x = n)) :
    ∃ Z : S.IdealSheafData, ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S),
      (∃ h : T ⟶ Z.subscheme, h ≫ Z.subschemeι = t) ↔
        (Flat (pullback.snd f t) ∧ ∀ x : T, (pullback.snd f t).finrank x = n) := by
  sorry

namespace EllipticCurve

variable (E : EllipticCurve S)

/-! ## §1 Generators of a subgroup divisor and the scheme of generators `G^×` (KM 6.1)

KM 6.1 (print p. 152, verbatim in the artifact): *"We say that `G` is cyclic if, locally
f.p.p.f. on `S`, `G` admits a generator … The functor on (Sch/S), `T ↦` generators of
`G_T/T`, is representable by a closed subscheme `G^×` of `G`, defined, locally on `S`, by
finitely many equations … a finite `S`-scheme of finite presentation, whose formation
commutes with arbitrary change of base."* -/

/-- **A generator of the subgroup divisor `D` over `t : T ⟶ S`** (KM 6.1 / KM 1.10.5): a
section `P₀` of the base-changed curve, of exact order `N`, whose order divisor
`Σ_{a=1..N} [a P₀]` is `D` pulled back to `T`. This is the payload of `IsGammaZeroFppf`'s
fppf-cover clause, exposed as a standalone predicate so KM 6's generator bookkeeping
(schemes of generators, standard subgroups, backing-up) can quantify over it. -/
def IsDivisorGenerator (N : ℕ) [NeZero N] (D : RelEffCartierDiv E.π) {T : Scheme.{u}}
    (t : T ⟶ S) (P₀ : (E.baseChange t).Section) : Prop :=
  P₀.HasExactOrder (E.baseChange t) N ∧
    (P₀.orderDivisor (E.baseChange t) N).ideal = (D.baseChange t).ideal

/-- `IsGammaZeroFppf` restated through `IsDivisorGenerator`: KM 1.4.1/3.4 cyclicity is
"subgroup + rank `N` + fppf-locally a generator". Definitional. -/
theorem isGammaZeroFppf_iff_generator (N : ℕ) [NeZero N] (D : RelEffCartierDiv E.π) :
    E.IsGammaZeroFppf N D ↔
      D.IsSubgroup E ∧ (∀ s : S, D.degree s = N) ∧
        ∃ (T : Scheme.{u}) (h : T ⟶ S),
          Function.Surjective h.base ∧ Flat h ∧ LocallyOfFinitePresentation h ∧
            ∃ P₀ : (E.baseChange h).Section, E.IsDivisorGenerator N D h P₀ :=
  Iff.rfl

-- ATTACK: (1) the ambient is `D.ideal.subscheme`, NOT `E` — KM's `G^×` is a closed
-- subscheme *of `G`*; parametrising by the (unique, `ι` mono) factorisation `h` of the
-- point through `D` mirrors `exists_exactOrderLocus`'s `pointToTorsion` parametrisation
-- and dodges a "pointToDivisor" def. (2) `hD` is REQUIRED: without `D` a subgroup divisor,
-- the incidence-EQ locus still exists but the stated iff is false — `orderDivisor P₀ = D_T`
-- forces `HasExactOrder` only because equal ideals give equal divisors (`ext`) and
-- `IsSubgroup` transports across that equality from `hD.baseChange`. (3) non-reduced test
-- schemes are covered: the discharge route (`exists_incidenceLocusEQ` on the tautological
-- point over `D` + `orderDivisor_baseChange`) is universal over arbitrary `T ⟶ S`, never
-- through geometric points — the `ℚ̄[ε]` trap recorded at `IsNaiveGammaOne` does not bite.
/-- The tautological `B`-point of `E` on the subgroup divisor `D`, where `B = D.ideal.subscheme`:
its underlying morphism is the closed immersion `D ↪ E` (`D.ideal.subschemeι`), a section of `E.π`
over `B` by construction of the base map `π_B = subschemeι ≫ E.π`.  T-D15 compares its order divisor
against the pulled-back `D`; a `T`-point `P` on `D` (via `h : T ⟶ B`) is exactly this taut point
pulled along `h`. -/
noncomputable def divisorTautPoint (D : RelEffCartierDiv E.π) :
    E.Point (D.ideal.subschemeι ≫ E.π) :=
  ⟨D.ideal.subschemeι, rfl⟩

/-- Restricting the tautological point along a `T`-point `h : T ⟶ D.ideal.subscheme` of the base
recovers the original point `P`, when `h` witnesses `P` lying on `D` (`h ≫ subschemeι = P.1`). -/
theorem divisorTautPoint_restrict (D : RelEffCartierDiv E.π) {T : Scheme.{u}} (t : T ⟶ S)
    (P : E.Point t) (h : T ⟶ D.ideal.subscheme) (hcomp : h ≫ D.ideal.subschemeι = P.1) :
    (Point.restrict E h (E.divisorTautPoint D) : T ⟶ E.E) = (P : T ⟶ E.E) := by
  show h ≫ D.ideal.subschemeι = P.1
  exact hcomp

/-- The `HasExactOrder` half of `IsDivisorGenerator` follows from the order-divisor–ideal equality
when `D` is a subgroup: equal ideals give equal divisors (`RelEffCartierDiv.ext`), and a subgroup
divisor stays a subgroup after base change (`IsSubgroup.baseChange`). This is ATTACK note (2): the
`orderDivisor = D` incidence forces exact order *because* `D` is a subgroup. -/
theorem hasExactOrder_of_orderDivisor_ideal_eq (N : ℕ) [NeZero N] (D : RelEffCartierDiv E.π)
    (hD : D.IsSubgroup E) {T : Scheme.{u}} (t : T ⟶ S) (P : (E.baseChange t).Section)
    (heq : (P.orderDivisor (E.baseChange t) N).ideal = (D.baseChange t).ideal) :
    P.HasExactOrder (E.baseChange t) N := by
  have h : P.orderDivisor (E.baseChange t) N = D.baseChange t := RelEffCartierDiv.ext heq
  have hsub : (D.baseChange t).IsSubgroup (E.baseChange t) :=
    RelEffCartierDiv.IsSubgroup.baseChange E hD t
  rw [← h] at hsub
  exact hsub

/-- **(KM 6.1, the scheme of generators `G^×` — divisor register)** For a rank-`N` subgroup
divisor `D ⊆ E`, there is a closed subscheme `Z ⊆ D` universal for "the point is a
generator of `D`": for a `T`-point `P` of `E` lying on `D` (witnessed by the factorisation
`h`), `h` factors through `Z` iff `P` is a generator of `D_T`. KM: *"representable by a
closed subscheme `G^× ⊆ G`, defined, locally on `S`, by finitely many equations"*.
Discharge route: `RelEffCartierDiv.exists_incidenceLocusEQ` (T-D15, PROVED) applied over
the base `D.ideal.subscheme` to the order divisor of the tautological point vs the pulled
back `D`, plus the `orderDivisor_baseChange`/`IsSubgroup.baseChange` dictionaries. -/
theorem exists_generatorLocus (N : ℕ) [NeZero N] (D : RelEffCartierDiv E.π)
    (hD : D.IsSubgroup E) :
    ∃ Z : D.ideal.subscheme.IdealSheafData,
      ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S) (P : E.Point t)
        (h : T ⟶ D.ideal.subscheme), h ≫ D.ideal.subschemeι = P.1 →
        ((∃ k : T ⟶ Z.subscheme, k ≫ Z.subschemeι = h) ↔
          E.IsDivisorGenerator N D t (Point.asSection E t P)) := by
  obtain ⟨Z, hZ⟩ := RelEffCartierDiv.exists_incidenceLocusEQ
    (E.baseChange (D.ideal.subschemeι ≫ E.π)).smooth
    (Section.orderDivisor (E.baseChange (D.ideal.subschemeι ≫ E.π))
      (Point.asSection E (D.ideal.subschemeι ≫ E.π) (E.divisorTautPoint D)) N)
    (D.baseChange (D.ideal.subschemeι ≫ E.π))
  refine ⟨Z, fun T t P h hcomp => ?_⟩
  refine Iff.trans (hZ h) ?_
  rw [RelEffCartierDiv.isSubdivisor_iff_le, RelEffCartierDiv.isSubdivisor_iff_le,
    ← le_antisymm_iff, RelEffCartierDiv.baseChange_ideal, RelEffCartierDiv.baseChange_ideal]
  -- REMAINING (coherence) — PRECISELY SCOPED via LSP 2026-07-09.  After
  --   `rw [← baseChange_ideal, ← baseChange_ideal, Section.orderDivisor_baseChange]` the goal is
  --     `(orderDivisor ((E.baseChange π_B).baseChange h) (asSection h (pull (asSection π_B taut))) N).ideal
  --        = ((D.baseChange π_B).baseChange h).ideal  ↔  IsDivisorGenerator N D t (asSection E t P)`,
  --   i.e. an `orderDivisor.ideal = D.ideal` equality over the curve `(E.baseChange π_B).baseChange h`
  --   versus one over `E.baseChange t` — the two total spaces are iso (not equal) via
  --   `pullbackLeftPullbackSndIso E.π π_B h`.  Closing it needs the ORDER-DIVISOR-IDEAL NATURALITY engine:
  --     • D side: `baseChange_baseChange_ideal` + `h ≫ π_B = t` (from `hcomp` + `P.1 ≫ E.π = t`).
  --     • OD side: `sectionsDivisor.ideal = ∏ ker` → `IdealSheafData.comap_prod` → `Finset.prod_congr`
  --       → per-factor `exactOrderLocusAux_ker_comap_eq` with the sections matched by
  --       `divisorTautPoint_restrict` — EXACTLY the proven twin `fullLevelLocusAux_P1/P2` pattern.
  --     • then `and_iff_right (hasExactOrder_of_orderDivisor_ideal_eq N D hD t (asSection E t P) ·)`.
  --   BLOCKER: that engine (`exactOrderLocusAux_ker_comap_eq` L1583, `subgroupLocusAux_val` L985 +snd,
  --   `exactOrderLocusAux_val_isClosedImmersion` L1630, and a general `sectionsDivisor_ideal` — the
  --   fullLevel one at L2350 is specialised) is all `private` to Incidence.lean.  CLEAN PATH: expose the
  --   general ones (visibility-only; Incidence.lean is sorry-free/stable) + this ~25-line assembly.  A
  --   cross-file API change worth flagging to the coordinator; not an inline close.
  sorry

/-- **The scheme of generators `D^×`** (KM 6.1's `G^×` = "`ℤ/Nℤ-Gen(G/S)`" of KM 1.10.13):
the total space of the generator locus. Real `Classical.choose` definition — the `sorry`
lives in `exists_generatorLocus`; consumers use `generatorSpace_spec`. -/
noncomputable def generatorSpace (N : ℕ) [NeZero N] (D : RelEffCartierDiv E.π)
    (hD : D.IsSubgroup E) : Scheme.{u} :=
  (E.exists_generatorLocus N D hD).choose.subscheme

/-- The inclusion `D^× ↪ D` (KM's `G^× ⊆ G`). -/
noncomputable def generatorSpaceι (N : ℕ) [NeZero N] (D : RelEffCartierDiv E.π)
    (hD : D.IsSubgroup E) : E.generatorSpace N D hD ⟶ D.ideal.subscheme :=
  (E.exists_generatorLocus N D hD).choose.subschemeι

/-- The structure morphism `D^× ⟶ S` (KM: `G^×` is "a finite `S`-scheme of finite
presentation"; finiteness/flatness of this map is the content of KM 6.1.1(1)). -/
noncomputable def generatorSpaceπ (N : ℕ) [NeZero N] (D : RelEffCartierDiv E.π)
    (hD : D.IsSubgroup E) : E.generatorSpace N D hD ⟶ S :=
  E.generatorSpaceι N D hD ≫ D.ideal.subschemeι ≫ E.π

/-- Specification of `generatorSpace`: factoring through `D^×` is being a generator.
Proved from `choose_spec` (the `sorry` is upstream in `exists_generatorLocus`). -/
theorem generatorSpace_spec (N : ℕ) [NeZero N] (D : RelEffCartierDiv E.π)
    (hD : D.IsSubgroup E) :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S) (P : E.Point t)
      (h : T ⟶ D.ideal.subscheme), h ≫ D.ideal.subschemeι = P.1 →
      ((∃ k : T ⟶ E.generatorSpace N D hD, k ≫ E.generatorSpaceι N D hD = h) ↔
        E.IsDivisorGenerator N D t (Point.asSection E t P)) :=
  (E.exists_generatorLocus N D hD).choose_spec

/-- **(KM 6.1, "formation commutes with arbitrary change of base")** The generator scheme
of the base-changed divisor is the base change of the generator scheme. Dischargeable from
the universal property (`generatorSpace_spec` on both sides + Yoneda); no new gates. -/
theorem generatorSpace_baseChange (N : ℕ) [NeZero N] (D : RelEffCartierDiv E.π)
    (hD : D.IsSubgroup E) {T : Scheme.{u}} (t : T ⟶ S) :
    ∃ e : pullback (E.generatorSpaceπ N D hD) t ≅
        (E.baseChange t).generatorSpace N (D.baseChange t)
          (RelEffCartierDiv.IsSubgroup.baseChange E hD t),
      e.hom ≫ (E.baseChange t).generatorSpaceπ N (D.baseChange t)
          (RelEffCartierDiv.IsSubgroup.baseChange E hD t) =
        pullback.snd (E.generatorSpaceπ N D hD) t := by
  sorry

/-! ## §2 The Main Theorem on Cyclic Groups (KM 6.1.1)

KM 6.1.1 (print pp. 152–153, verbatim in the artifact): *"(1) `G` is cyclic if and only if
its scheme of generators `G^×` is finite locally free over `S`, of rank `φ(N)`. (2) Suppose
that `G/S` is cyclic, and that `P ∈ G(S)` is a generator. Then the Cartier divisor `D` in
`E` defined by `D = Σ_{(a,N)=1, a mod N} [aP]` lies in `G`, and we have an equality of
closed subschemes of `G`: `D = G^×`."* -/

-- ATTACK: (1) `G^× ⟶ S` finite locally free of rank `φ(N) ≥ 1` is fppf: surjectivity is
-- mathlib's `Scheme.Hom.one_le_finrank_iff_surjective` + `Nat.totient_pos`; flat and lfp
-- are the hypotheses. (2) the generator over the cover is the TAUTOLOGICAL point of `D`
-- restricted to `D^×` — its generator property is `generatorSpace_spec` applied to the
-- identity factorisation; the transport of `IsDivisorGenerator` from the tautological base
-- to the cover-presented base change is the same `asSection`-spelling normalisation used by
-- `exists_exactOrderLocus` (in-project precedent, no new gate). (3) `S = ∅`: every rank
-- hypothesis holds vacuously, and `IsGammaZeroFppf` holds with the empty cover — no
-- degenerate failure.
/-- **(KM 6.1.1(1), "if" — the easy direction)** If the scheme of generators `D^×` is
finite locally free over `S` of rank `φ(N)`, then `D` is cyclic: *"it acquires a generator
after the f.p.p.f. base change `G^× → S`"* (KM print p. 153). -/
theorem isGammaZeroFppf_of_generatorSpace_finiteLocallyFree (N : ℕ) [NeZero N]
    (D : RelEffCartierDiv E.π) (hD : D.IsSubgroup E) (hdeg : ∀ s : S, D.degree s = N)
    (hfin : IsFinite (E.generatorSpaceπ N D hD)) (hflat : Flat (E.generatorSpaceπ N D hD))
    (hlfp : LocallyOfFinitePresentation (E.generatorSpaceπ N D hD))
    (hrank : ∀ s : S, (E.generatorSpaceπ N D hD).finrank s = N.totient) :
    E.IsGammaZeroFppf N D := by
  sorry

/-- **(KM 6.1.1(1), "only if" — the hard direction; GATE [KM-62-63-HOMOG])** If `D` is
cyclic then `D^×` is finite locally free over `S` of rank `φ(N)`. KM's proof (print
pp. 153–162) reduces fppf-locally to a generator, to the prime-power case `N = pⁿ` (KM
1.7.3/1.10.15), and then runs the moduli comparison `𝒫₁ → 𝒫₂` through the Axiomatic
Isomorphism Theorem 6.2.1 and the formal-group determinant computation 6.3.2–6.3.6 over
`W(k)[[T]]` at supersingular points. -/
theorem generatorSpace_finiteLocallyFree_of_isGammaZeroFppf (N : ℕ) [NeZero N]
    (D : RelEffCartierDiv E.π) (hD : D.IsSubgroup E) (hG : E.IsGammaZeroFppf N D) :
    IsFinite (E.generatorSpaceπ N D hD) ∧ Flat (E.generatorSpaceπ N D hD) ∧
      LocallyOfFinitePresentation (E.generatorSpaceπ N D hD) ∧
      ∀ s : S, (E.generatorSpaceπ N D hD).finrank s = N.totient := by
  sorry

/-- **The prime-to-`N` order divisor `Σ_{(a,N)=1, a mod N} [aP]`** of KM 6.1.1(2): the
sections divisor over the `φ(N)` residues coprime to `N` (enumerated via
`(ZMod N)ˣ ≃ Fin φ(N)`). This is the divisor KM proves equal to `G^×`. -/
noncomputable def primeOrderDivisor (P : E.Section) (N : ℕ) [NeZero N] :
    RelEffCartierDiv E.π :=
  RelEffCartierDiv.sectionsDivisor E.π fun i : Fin N.totient =>
    (((((Fintype.equivFinOfCardEq (ZMod.card_units_eq_totient N)).symm i :
      (ZMod N)ˣ) : ZMod N).val : ℤ) • P : E.Point (𝟙 S))

/-- The prime-to-`N` order divisor has constant degree `φ(N)` (KM print p. 153: *"the
Cartier divisor `D` is visibly finite locally free over `S`, of degree `φ(N)`"*). -/
theorem primeOrderDivisor_degree (P : E.Section) (N : ℕ) [NeZero N] (s : S) :
    (E.primeOrderDivisor P N).degree s = N.totient :=
  RelEffCartierDiv.sectionsDivisor_degree E.π E.smooth _ s

-- ATTACK: (1) this is KM's `D ⊆ G^×` in functor-of-points form — each `aP₀`, `(a,N) = 1`,
-- is again a generator; KM proves it by reduction to the universal case (`[Γ₁(N)]` flat
-- over `ℤ`) and the tautological section over the divisor `D` — the [KM-FMT-FLAT] gate,
-- irreducibly (over `ℤ[1/N]` it is elementary group theory, and flatness spreads it out).
-- (2) char `p ∣ N` honesty: for `Ker F ⊆ E` supersingular (`N = p`), the only generator is
-- `P₀ = 0` and `a • 0 = 0` for all `(a,p) = 1` — the statement degenerates correctly.
-- (3) the conclusion re-asserts `HasExactOrder` for `a • P₀`: NOT automatic from the ideal
-- equation alone unless `D` is a subgroup — `hD` is load-bearing (transport of `IsSubgroup`
-- across `RelEffCartierDiv.ext`).
/-- **(KM 6.1.1(2), first half: `D ⊆ G^×`; GATE [KM-FMT-FLAT])** Prime-to-`N` multiples of
a generator are generators: if `P₀` generates the rank-`N` subgroup divisor `D` and
`gcd(a, N) = 1`, then `a • P₀` has exact order `N` and generates `D`. -/
theorem isDivisorGenerator_smul (N : ℕ) [NeZero N] {D : RelEffCartierDiv E.π}
    (hD : D.IsSubgroup E) (hdeg : ∀ s : S, D.degree s = N) {P₀ : E.Section}
    (hord : P₀.HasExactOrder E N) (hgen : (P₀.orderDivisor E N).ideal = D.ideal)
    {a : ℤ} (ha : a.gcd N = 1) :
    (a • P₀).HasExactOrder E N ∧ ((a • P₀).orderDivisor E N).ideal = D.ideal := by
  sorry

/-- **(KM 6.1.1(2), second half: `G^× ⊆ D`; GATE [KM-62-63-HOMOG])** Every generator of
`D_T` lies on the prime-to-`N` order divisor of a chosen global generator `P₀`. This is the
half KM proves by the homogeneity argument (6.2/6.3): the closed immersion `D ↪ G^×` of
finite `S`-schemes is an isomorphism. -/
theorem factors_primeOrderDivisor_of_isDivisorGenerator (N : ℕ) [NeZero N]
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) (hdeg : ∀ s : S, D.degree s = N)
    {P₀ : E.Section} (hord : P₀.HasExactOrder E N)
    (hgen : (P₀.orderDivisor E N).ideal = D.ideal) {T : Scheme.{u}} (t : T ⟶ S)
    (Q : E.Point t) (hQ : E.IsDivisorGenerator N D t (Point.asSection E t Q)) :
    ∃ h : T ⟶ (E.primeOrderDivisor P₀ N).ideal.subscheme,
      h ≫ (E.primeOrderDivisor P₀ N).ideal.subschemeι = Q.1 := by
  sorry

/-- **(KM 6.1.1(2), assembled: `D = G^×` as functors of points)** Given a global generator
`P₀` of `D`, a `T`-point of `E` is a generator of `D_T` iff it lies on
`Σ_{(a,N)=1} [aP₀]`. (The scheme-level equality of KM follows by evaluating at the
tautological point — KM's own universal-case move, recorded in the artifact.) -/
theorem isDivisorGenerator_iff_factors_primeOrderDivisor (N : ℕ) [NeZero N]
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) (hdeg : ∀ s : S, D.degree s = N)
    {P₀ : E.Section} (hord : P₀.HasExactOrder E N)
    (hgen : (P₀.orderDivisor E N).ideal = D.ideal) {T : Scheme.{u}} (t : T ⟶ S)
    (Q : E.Point t) :
    E.IsDivisorGenerator N D t (Point.asSection E t Q) ↔
      ∃ h : T ⟶ (E.primeOrderDivisor P₀ N).ideal.subscheme,
        h ≫ (E.primeOrderDivisor P₀ N).ideal.subschemeι = Q.1 := by
  sorry

/-! ## §3 Cyclicity as a closed condition (KM 6.4 — ticket T-SG3)

KM 6.4.1 (print p. 162, verbatim in the artifact): *"there exists a closed subscheme
`W ⊆ S`, defined locally … by finitely many equations, which is universal for the condition
'`G` is cyclic', in the sense that for any morphism `T → S`, the inverse image `G_T/T` is
cyclic if and only if the map `T → S` factors through the closed subscheme `W`."*

KM's mechanism: cyclicity of `G_T` ⇔ `(G^×)_T` finite locally free of rank `φ(N)`
(Theorem 6.1.1 — note this is where both directions of 6.1.1 enter), the fibre dichotomy
Lemma 6.4.2 (a **fibrewise/geometric statement**), and Mumford's flattening stratification
Prop 6.4.3 (a **closed-condition-over-the-base statement**, `exists_locallyFreeRankLocus`
above). -/

-- ATTACK: (1) KM 6.4.2 is stated for arbitrary (not algebraically closed) fields — the
-- dichotomy "`(G_k)^×` empty or of rank exactly `φ(N)`" uses that a non-cyclic `G_k` never
-- becomes cyclic over ANY field extension (its generator scheme has no field-valued points
-- at all); formalising over `Field k` (not `IsAlgClosed`) is therefore faithful and needed
-- by the flattening hypothesis. (2) emptiness is of the honest fibre `pullback`, matching
-- `exists_locallyFreeRankLocus`'s hypothesis — no `IsAffine`/carrier detours. (3) the
-- cyclic-side companion (fibre flf of rank `φ(N)`) is 6.1.1(1)-hard base-changed to `k`,
-- via `generatorSpace_baseChange`; it is NOT a separate axiom — the artifact tracks it
-- inside [NISOG-L13]'s discharge.
/-- **(KM Lemma 6.4.2, empty half — fibrewise)** Over a field-valued point of `S`, if the
pulled-back divisor is not cyclic then the generator scheme has empty fibre: *"If `G_k/k`
is not cyclic, then, `k` being a field, `G_k` never becomes cyclic after any field
extension. Therefore the `k`-scheme `(G_k)^×` has no field-valued points, hence it is the
empty scheme"* (KM print p. 163). -/
theorem generatorSpace_fibre_isEmpty_of_not_isGammaZeroFppf (N : ℕ) [NeZero N]
    (D : RelEffCartierDiv E.π) (hD : D.IsSubgroup E) (k : Type u) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S)
    (hnc : ¬ (E.baseChange t).IsGammaZeroFppf N (D.baseChange t)) :
    IsEmpty (pullback (E.generatorSpaceπ N D hD) t : Scheme.{u}) := by
  sorry

/-- **(KM 6.4.1 = ticket T-SG3: cyclicity is a closed condition)** For a rank-`N` subgroup
divisor `D ⊆ E` there is a closed subscheme `Z ⊆ S` universal for cyclicity: `t : T ⟶ S`
factors through `Z` iff `D_T` is a Γ₀(N)-cyclic (`IsGammaZeroFppf`) subgroup divisor of
`E_T`. Assembly: flattening locus (`exists_locallyFreeRankLocus`) of `generatorSpaceπ`,
fed by the fibre dichotomy (6.4.2) and both directions of 6.1.1. -/
theorem exists_cyclicityLocus (N : ℕ) [NeZero N] (D : RelEffCartierDiv E.π)
    (hD : D.IsSubgroup E) (hdeg : ∀ s : S, D.degree s = N) :
    ∃ Z : S.IdealSheafData, ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S),
      (∃ h : T ⟶ Z.subscheme, h ≫ Z.subschemeι = t) ↔
        (E.baseChange t).IsGammaZeroFppf N (D.baseChange t) := by
  sorry

/-! ## §4 The moduli problem `[N-Isog]` (KM 6.5 — review-Q8 named block)

KM 6.5 (print pp. 164–165, verbatim in the artifact): *"`[N-Isog](E/S)` = the set of
finite locally free commutative `S`-subgroup-schemes `G ⊆ E[N]` which are of rank `N` over
`S`."* Note the containment `G ⊆ E[N]` is automatic for a rank-`N` subgroup scheme of `E`
by Oort–Tate/Deligne (KM 1.4.2 — the registered box `BB-DELIGNE`), proved below. -/

/-- **An `N`-isogeny datum on `E/S`** (KM 6.5): a finite locally free subgroup scheme
`G ⊆ E` of rank `N` — equivalently (KM 1.4.2) a rank-`N` subgroup scheme of `E[N]`, the
kernel of the `N`-isogeny `E ⟶ E/G`. A `GammaZeroStructure` is exactly an `N`-isogeny
datum whose subgroup is cyclic; the forgetful map is `GammaZeroStructure.toNIsogeny`. -/
structure NIsogenyStructure (E : EllipticCurve S) (N : ℕ) [NeZero N] where
  /-- The kernel: a finite locally free subgroup scheme `G ⊆ E`. -/
  subgroup : FiniteLocallyFreeSubgroup E
  /-- `G` has constant rank `N` (KM: "of rank `N` over `S`"). -/
  hasRank : subgroup.HasRank N

namespace NIsogenyStructure

variable {E} {N : ℕ} [NeZero N]

/-- **(KM 1.4.2 / Oort–Tate for `N`-isogeny data)** The kernel of an `N`-isogeny datum is
killed by `N`. Routed through the registered box `BB-DELIGNE`
(`HasRank.smul_eq_zero_of_factors`); no new box. -/
theorem smul_eq_zero (nis : NIsogenyStructure E N) {T : Scheme.{u}} (g : T ⟶ S)
    (P : E.Point g) (hP : P ∈ nis.subgroup.pointSubgroup g) : (N : ℤ) • P = 0 :=
  nis.hasRank.smul_eq_zero_of_factors g P hP

/-- **(KM 6.5's "`G ⊆ E[N]`", point form)** The point subgroup of an `N`-isogeny datum is
contained in that of the `N`-torsion subgroup scheme: KM's *"subgroup-schemes `G ⊆ E[N]`"*
is a consequence of rank `N`, not an extra datum. -/
theorem pointSubgroup_le_torsion (nis : NIsogenyStructure E N) {T : Scheme.{u}}
    (g : T ⟶ S) :
    nis.subgroup.pointSubgroup g ≤ (E.torsionSubgroup N).pointSubgroup g := by
  intro P hP
  rw [E.torsionSubgroup_pointSubgroup, Submodule.mem_toAddSubgroup,
    Submodule.mem_torsionBy_iff]
  exact nis.smul_eq_zero g P hP

end NIsogenyStructure

/-- Every Γ₀(N)-structure is an `N`-isogeny datum (forget cyclicity): the datum-level
closed immersion `[Γ₀(N)] ↪ [N-Isog]` of KM 6.8.7/6.6.1. -/
def GammaZeroStructure.toNIsogeny {N : ℕ} [NeZero N] (Γ : GammaZeroStructure E N) :
    NIsogenyStructure E N :=
  ⟨Γ.subgroup, Γ.hasRank⟩

-- ATTACK: (1) [NISOG-GRASS]: mathlib has no relative Grassmannian scheme (only
-- `RingTheory/Grassmannian`, a module-quotient functor) — KM's ambient "Grassmannian of
-- all rank-`N` quotients of `𝓕`" is a genuine gap-gate; the bi-ideal condition is then a
-- closed condition on the universal quotient. (2) the equivalence is stated per test
-- morphism `t`, matching T-W8's level-space presentations; the base-change NATURALITY of
-- the family `e_t` (the honest "relatively representable" content) is deliberately part of
-- the construction ticket, not this ∃ — recorded in the artifact (same caveat as T-W8).
-- (3) `Nonempty (… ≃ …)` avoids choosing data in a `theorem`; the eventual constructive
-- form will name the classifying scheme and its universal datum (opaque-interface rule).
/-- **(KM 6.5.1, RR-only; GATE [NISOG-GRASS])** The moduli problem `[N-Isog]` is relatively
representable and finite: for `E/S` there is a finite `S`-scheme `W` whose `T`-points over
`t : T ⟶ S` classify `N`-isogeny data on `E ×_S T`. KM: *"a subgroup `G ⊆ E[N]` of the
type being sought is nothing other than a locally free rank-`N` quotient `𝓕 ↠ 𝔥` … such
that the kernel `𝒦 ⊆ 𝓕` is a bi-ideal … Therefore `[N-Isog]` is relatively represented by
a closed subscheme of the Grassmannian of all rank-`N` quotients of `𝓕`"* (print p. 165). -/
theorem exists_nIsogSpace (N : ℕ) [NeZero N] :
    ∃ (W : Scheme.{u}) (w : W ⟶ S), IsFinite w ∧
      ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S),
        Nonempty (NIsogenyStructure (E.baseChange t) N ≃ { h : T ⟶ W // h ≫ w = t }) := by
  sorry

/-! ## §5 Standard cyclic subgroups (KM 6.7.2–6.7.5)

KM 6.7.2 (print p. 167, verbatim in the artifact): *"Let `E/S` be an elliptic curve,
`G ⊆ E/S` a cyclic subgroup over `S` of order `N`. For every divisor `d` of `N`, there is
a 'standard' cyclic subgroup `G_d ⊆ G` of order `d`, which may be described, f.p.p.f.
locally on `S`, in terms of any generator `P` of `G`, as the cyclic subgroup of order `d`
generated by `(N/d)P`."*

KM's Useful Lemma 6.7.3 (equality of two finite flat closed subschemes is a closed
condition on the base) is already in-project **at the divisor level** as
`RelEffCartierDiv.exists_incidenceLocusEQ` (T-D15, PROVED, sorry-free) — every Ch. 6 use of
6.7.3 (in 6.7.2, 6.7.4, 6.7.9, 6.7.11) concerns subschemes of the curve `E` or of a kernel
inside `E`, i.e. divisors, so no new lemma is minted for it. -/

-- ATTACK: (1) `G_d` is NOT the `d`-torsion `G[d]`: in char `p` with `G = Ker Fⁿ ⊆ E[pⁿ]`
-- supersingular and `d = pᵐ`, `G[pᵐ] = Ker F^min(n,2m)` has rank `p^min(n,2m) ≠ pᵐ` for
-- `m < n` — the standard subgroup is the IMAGE of `[N/d]` on `G` (generated by `(N/d)P`),
-- and only fppf-descent defines it globally; this is why existence is a sorried ∃, not a
-- kernel construction. (2) BOTH a raw clause (global generator on `S` itself) and a
-- parametric clause (any generator after any base change) are packaged: the raw clause is
-- what backing-up-style corollaries consume without the `baseChange (𝟙 S)` spelling tax;
-- the parametric clause doubles as the DS-style base-change specification pinning `D_d`.
-- (3) `d = N`: `G_N = G` (generated by `1·P`); `d = 1`: `G_1` is the zero divisor `[0]`,
-- cyclic of order 1 with generator `0` — both are honest instances, no side conditions.
/-- **(KM 6.7.2; GATES [T-D10-FPPF] fppf glue + [KM-FMT-FLAT] for well-definedness)** For a
cyclic rank-`N` subgroup divisor `D` and `d ∣ N`, there is a *standard* cyclic subgroup
divisor `D_d ≤ D` of order `d`, described along any generator `P₀` (over the base or after
any base change) as the order divisor of `(N/d) • P₀`. -/
theorem exists_standardCyclicDivisor {N : ℕ} [NeZero N] {D : RelEffCartierDiv E.π}
    (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d] (hd : d ∣ N) :
    ∃ Dd : RelEffCartierDiv E.π,
      E.IsGammaZeroFppf d Dd ∧
      RelEffCartierDiv.IsSubdivisor Dd D ∧
      (∀ P₀ : E.Section, P₀.HasExactOrder E N → (P₀.orderDivisor E N).ideal = D.ideal →
        ((((N / d : ℕ) : ℤ) • P₀).orderDivisor E d).ideal = Dd.ideal) ∧
      ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S) (P₀ : (E.baseChange t).Section),
        E.IsDivisorGenerator N D t P₀ →
          ((((N / d : ℕ) : ℤ) • P₀).orderDivisor (E.baseChange t) d).ideal =
            (Dd.baseChange t).ideal := by
  sorry

/-- **The standard cyclic subgroup divisor `D_d`** (KM 6.7.2's `G_d`). Real
`Classical.choose` definition; the `sorry` lives in `exists_standardCyclicDivisor`. -/
noncomputable def standardCyclicDivisor {N : ℕ} [NeZero N] {D : RelEffCartierDiv E.π}
    (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d] (hd : d ∣ N) :
    RelEffCartierDiv E.π :=
  (E.exists_standardCyclicDivisor hG hd).choose

/-- `D_d` is cyclic of order `d` (KM 6.7.2). Pin, proved from `choose_spec`. -/
theorem standardCyclicDivisor_isGammaZeroFppf {N : ℕ} [NeZero N]
    {D : RelEffCartierDiv E.π} (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d]
    (hd : d ∣ N) : E.IsGammaZeroFppf d (E.standardCyclicDivisor hG hd) :=
  (E.exists_standardCyclicDivisor hG hd).choose_spec.1

/-- `D_d ≤ D` (KM 6.7.2's `G_d ⊆ G`). Pin, proved from `choose_spec`. -/
theorem standardCyclicDivisor_isSubdivisor {N : ℕ} [NeZero N]
    {D : RelEffCartierDiv E.π} (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d]
    (hd : d ∣ N) : RelEffCartierDiv.IsSubdivisor (E.standardCyclicDivisor hG hd) D :=
  (E.exists_standardCyclicDivisor hG hd).choose_spec.2.1

/-- Along a global generator `P₀` of `D`, the standard subgroup is the order divisor of
`(N/d) • P₀` (KM 6.7.2's description, raw form; also KM 6.7.11(1)'s "`(N/d)P` generates
`Ker π_d`"). Pin, proved from `choose_spec`. -/
theorem standardCyclicDivisor_generator_spec {N : ℕ} [NeZero N]
    {D : RelEffCartierDiv E.π} (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d]
    (hd : d ∣ N) (P₀ : E.Section) (hord : P₀.HasExactOrder E N)
    (hgen : (P₀.orderDivisor E N).ideal = D.ideal) :
    ((((N / d : ℕ) : ℤ) • P₀).orderDivisor E d).ideal =
      (E.standardCyclicDivisor hG hd).ideal :=
  (E.exists_standardCyclicDivisor hG hd).choose_spec.2.2.1 P₀ hord hgen

/-- The base-change/parametric form of the generator description (the DS-style
specification pinning `D_d` after arbitrary base change). Pin, proved from `choose_spec`. -/
theorem standardCyclicDivisor_generator_spec' {N : ℕ} [NeZero N]
    {D : RelEffCartierDiv E.π} (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d]
    (hd : d ∣ N) {T : Scheme.{u}} (t : T ⟶ S) (P₀ : (E.baseChange t).Section)
    (hP₀ : E.IsDivisorGenerator N D t P₀) :
    ((((N / d : ℕ) : ℤ) • P₀).orderDivisor (E.baseChange t) d).ideal =
      ((E.standardCyclicDivisor hG hd).baseChange t).ideal :=
  (E.exists_standardCyclicDivisor hG hd).choose_spec.2.2.2 t P₀ hP₀

/-- **(KM 6.7.2, well-definedness; GATE [T-D10-FPPF])** Any two divisors satisfying the
parametric generator description of `D_d` coincide — KM's `G_d = G_d'` step (two
generators give the same standard subgroup), by fppf descent of the ideal identity from a
generator-admitting cover. -/
theorem standardCyclicDivisor_unique {N : ℕ} [NeZero N] {D : RelEffCartierDiv E.π}
    (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d] (hd : d ∣ N)
    {D₁ D₂ : RelEffCartierDiv E.π}
    (h₁ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S) (P₀ : (E.baseChange t).Section),
      E.IsDivisorGenerator N D t P₀ →
        ((((N / d : ℕ) : ℤ) • P₀).orderDivisor (E.baseChange t) d).ideal =
          (D₁.baseChange t).ideal)
    (h₂ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S) (P₀ : (E.baseChange t).Section),
      E.IsDivisorGenerator N D t P₀ →
        ((((N / d : ℕ) : ℤ) • P₀).orderDivisor (E.baseChange t) d).ideal =
          (D₂.baseChange t).ideal) :
    D₁ = D₂ := by
  sorry

/-- **(KM 6.7.4, transitivity clause, within `E`; GATE [KM-FMT-FLAT])** For `d ∣ d' ∣ N`,
the standard `d`-subgroup of the standard `d'`-subgroup is the standard `d`-subgroup:
*"If `d ∣ d' ∣ N`, then `G_d ⊆ G_{d'}` is the standard cyclic subgroup of `G_{d'}` of
order `d`"*. -/
theorem standardCyclicDivisor_trans {N : ℕ} [NeZero N] {D : RelEffCartierDiv E.π}
    (hG : E.IsGammaZeroFppf N D) {d d' : ℕ} [NeZero d] [NeZero d'] (hdd' : d ∣ d')
    (hd' : d' ∣ N) :
    E.standardCyclicDivisor (E.standardCyclicDivisor_isGammaZeroFppf hG hd') hdd' =
      E.standardCyclicDivisor hG (hdd'.trans hd') := by
  sorry

/-- **The standard cyclic subgroup as a subgroup scheme** (KM 6.7.2's `G_d`, scheme
register): the `T-SG1` packaging of `standardCyclicDivisor` via `ofRelEffCartierDiv`. Its
quotient (through the [T-G3D-INFRA] gate) is the source of the standard factorization. -/
noncomputable def standardCyclicSubgroup {N : ℕ} [NeZero N] {D : RelEffCartierDiv E.π}
    (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d] (hd : d ∣ N) :
    FiniteLocallyFreeSubgroup E :=
  FiniteLocallyFreeSubgroup.ofRelEffCartierDiv (E.standardCyclicDivisor hG hd)
    (E.standardCyclicDivisor_isGammaZeroFppf hG hd).1

-- ATTACK: (1) the identity is the multiset partition `{a mod N} = ⊔_{d ∣ N} {b·(N/d) :
-- (b,d)=1}` (Gauss `Σ_{d∣N} φ(d) = N`), transported through `sectionsDivisor`'s ideal
-- product — a Finset reindexing plus commutativity of ideal products, NO moduli input.
-- (2) `hkill` is REQUIRED (not cyclicity!): the two sides enumerate different integer
-- representatives of the same residues (`{1,…,N}` vs `{b·(N/d) ∈ [0,N)}`), and
-- `a • P₀ = a' • P₀` for `a ≡ a' [N]` needs `N • P₀ = 0`; without it the `a = N` vs
-- `a = 0` terms already differ. (3) `attach`+`letI` supplies the per-divisor `NeZero d`
-- instance — `d ∈ N.divisors` forces `0 < d` (`Nat.pos_of_mem_divisors`).
/-- **(KM 6.7.5, generator-local form)** `G = Σ_{d ∣ N} (G_d)^×` as Cartier divisors: along
a point `P₀` killed by `N`, the order divisor of `P₀` is the product over `d ∣ N` of the
prime-to-`d` order divisors of `(N/d) • P₀`. KM proves the global statement by fppf
localisation to this identity (*"the assertion is obvious; for we have
`G = Σ_{a mod N} [aP]`; `G_d^× = Σ_{(b,d)=1, b mod d} [b(N/d)P]`"*, print p. 170). -/
theorem orderDivisor_ideal_eq_prod_primeOrderDivisor (N : ℕ) [NeZero N] (P₀ : E.Section)
    (hkill : (N : ℤ) • P₀ = 0) :
    (P₀.orderDivisor E N).ideal =
      ∏ d ∈ N.divisors.attach,
        letI : NeZero d.1 := ⟨(Nat.pos_of_mem_divisors d.2).ne'⟩
        (E.primeOrderDivisor ((((N / d.1 : ℕ) : ℤ)) • P₀) d.1).ideal := by
  sorry

end EllipticCurve

/-! ## §6 The `N`-isogeny `E ⟶ E/G` (KM 6.7.6) — the [T-G3D-INFRA]-gated layer

KM 6.7.6 (print p. 170, verbatim in the artifact): *"we will refer to `G' = G mod G_d` as
the standard cyclic `N/d`-quotient of the cyclic group `G`. Given a cyclic `N`-isogeny `π`
with kernel `G`, `E → E″` (`ker = G`), and a divisor `d` of `N`, we will refer to the
factorization `E → E' → E″` (`ker π_d = G_d`, `ker π' = G'`) as the standard factorization
of the cyclic `N`-isogeny `π` into a cyclic `d`-isogeny followed by a cyclic
`N/d`-isogeny."*

The scheme-level quotient `E/G` is [T-G3D-INFRA] (`SubgroupQuotient.lean` — DS-data
`quotient`/`quotientπ` + pins, p0's stream). The two DS-defs below are its **elliptic-curve
upgrade** (`E/G` as an elliptic curve and `π` as the `N`-isogeny into it) — DS-NISOG-1/2 in
the artifact's DATA-SORRY list, construction gated on [T-G3D-INFRA] landing
([T-G3D-INFRA-CURVE]). Consumers use only the pins. -/

namespace EllipticCurve

namespace FiniteLocallyFreeSubgroup

variable {E : EllipticCurve S}

-- ATTACK: (1) the DATA is the curve record, not just a scheme: `E/G` needs zero section,
-- group law, and the local Weierstrass model — none of which the scheme-level gate
-- provides; making it separate DS-data (rather than pretending `quotient` is a curve)
-- keeps the gate honest. (2) NOT gated on `E[N]`-finite-étale: the construction consumes
-- `G`'s own `finite`/`flat`/`lfp` fields, exactly like the scheme-level quotient.
-- (3) the pin `quotientCurve_compat` ties the total space to the gate's `G.quotient` by a
-- (non-evil) isomorphism under `E`, not a scheme equality — the eventual construction may
-- take `E := G.quotient` on the nose, upgrading the pin to `rfl`-strength, but consumers
-- must not rely on that.
/-- **DS-NISOG-1 (GATE [T-G3D-INFRA])** The quotient elliptic curve `E/G` of `E` by a
finite locally free subgroup scheme `G` (KM 6.7.6's target curve `E'`). DS-registered
data; consumers use only the pins (`quotientCurve_compat`, `quotientHom_*`,
`pointMap_*`). -/
noncomputable def quotientCurve (G : FiniteLocallyFreeSubgroup E) : EllipticCurve S :=
  sorry

/-- **DS-NISOG-2 (GATE [T-G3D-INFRA])** The quotient `N`-isogeny `π : E ⟶ E/G` (KM
6.7.6's `π`), as a morphism into the quotient curve's total space. DS-registered data. -/
noncomputable def quotientHom (G : FiniteLocallyFreeSubgroup E) :
    E.E ⟶ G.quotientCurve.E :=
  sorry

/-- **(pin)** The quotient isogeny is a morphism over `S`. -/
theorem quotientHom_over (G : FiniteLocallyFreeSubgroup E) :
    G.quotientHom ≫ G.quotientCurve.π = E.π := by
  sorry

/-- **(pin)** The quotient isogeny collapses `G`-translates — the [T-G3D-INFRA]
invariance condition, tying this layer to the scheme-level gate's vocabulary. -/
theorem quotientHom_isInvariant (G : FiniteLocallyFreeSubgroup E) :
    G.IsInvariant G.quotientHom := by
  sorry

/-- **(pin)** Compatibility with the scheme-level gate: the quotient curve's total space
is the [T-G3D-INFRA] quotient scheme, identified under the two quotient maps. -/
theorem quotientCurve_compat (G : FiniteLocallyFreeSubgroup E) :
    ∃ e : G.quotient ≅ G.quotientCurve.E, G.quotientπ ≫ e.hom = G.quotientHom := by
  sorry

/-- The point-level map `E(T) ⟶ (E/G)(T)` induced by the quotient isogeny (KM's
`P ↦ π(P)`, e.g. the `π_d P` of 6.7.4/6.7.11). Real definition (composition), over-ness
from the pin `quotientHom_over`. -/
noncomputable def pointMap (G : FiniteLocallyFreeSubgroup E) {T : Scheme.{u}}
    {g : T ⟶ S} (x : E.Point g) : G.quotientCurve.Point g :=
  ⟨x.1 ≫ G.quotientHom, by rw [Category.assoc, G.quotientHom_over]; exact x.2⟩

@[simp]
theorem pointMap_coe (G : FiniteLocallyFreeSubgroup E) {T : Scheme.{u}} {g : T ⟶ S}
    (x : E.Point g) : (G.pointMap x).1 = x.1 ≫ G.quotientHom :=
  rfl

/-- **(pin)** `π` is pointed: the zero section maps to the zero section. -/
theorem pointMap_zero (G : FiniteLocallyFreeSubgroup E) {T : Scheme.{u}} (g : T ⟶ S) :
    G.pointMap (0 : E.Point g) = 0 := by
  sorry

/-- **(pin)** `π` is a homomorphism on `T`-points (the isogeny is a group-scheme map). -/
theorem pointMap_add (G : FiniteLocallyFreeSubgroup E) {T : Scheme.{u}} {g : T ⟶ S}
    (x y : E.Point g) : G.pointMap (x + y) = G.pointMap x + G.pointMap y := by
  sorry

/-- **(pin — the kernel specification)** `Ker π = G` (KM 6.7.6: *"a cyclic `N`-isogeny
`π` with kernel `G`"*): a `T`-point of `E` dies in `E/G` iff it lies on `G`. This is the
load-bearing pin for the whole standard-factorization layer. -/
theorem pointMap_eq_zero_iff (G : FiniteLocallyFreeSubgroup E) {T : Scheme.{u}}
    {g : T ⟶ S} (x : E.Point g) :
    G.pointMap x = 0 ↔ x ∈ G.pointSubgroup g := by
  sorry

/-- **(pin)** The quotient isogeny is finite (half of "`π` is an isogeny of degree
`rank G`"). -/
theorem quotientHom_finite (G : FiniteLocallyFreeSubgroup E) :
    IsFinite G.quotientHom := by
  sorry

/-- **(pin)** The quotient isogeny is flat. -/
theorem quotientHom_flat (G : FiniteLocallyFreeSubgroup E) : Flat G.quotientHom := by
  sorry

/-- **(pin)** The degree of the quotient isogeny is the rank of `G` (KM 6.7.6: a cyclic
`N`-isogeny has degree `N`). -/
theorem quotientHom_finrank (G : FiniteLocallyFreeSubgroup E) (y : G.quotientCurve.E) :
    G.quotientHom.finrank y = G.rank (G.quotientCurve.π y) := by
  sorry

end FiniteLocallyFreeSubgroup

variable (E : EllipticCurve S)

/-! ## §7 Standard factorization: quotients of cyclic subgroups (KM 6.7.4, 6.7.8, 6.7.11)

KM 6.7.4 (print p. 169, verbatim in the artifact): *"Let `E/S` be an elliptic curve,
`G ⊆ E[N]` a cyclic subgroup of order `N`, `d` a divisor of `N`, and `G_d ⊆ G` the
standard cyclic subgroup of `G` of order `d`. Then the quotient group `G' = G mod G_d` in
the quotient elliptic curve `E' = E mod G_d` is cyclic of order `N/d`. If `P` is a
generator of `G`, then its image `P'` in `G'` generates `G'`."* -/

-- ATTACK: (1) the image divisor is DATA produced by an ∃ (then `choose`), not a
-- constructed pushforward: divisor images under finite flat maps have no project API, and
-- KM itself characterises `G'` only through generators + closed-locus arguments — the ∃
-- packages exactly KM's characterisation. (2) `NeZero (N/d)` is an explicit instance
-- hypothesis (derivable from `d ∣ N`, `N ≠ 0`, but instance search cannot see `hd`).
-- (3) the generator clause is stated in the raw global form (Section-level, `𝟙 S`), the
-- one 6.7.11/6.7.12-style corollaries consume; the fppf-parametric form follows by
-- applying the theorem after base change and is deliberately omitted from the ∃ to keep
-- the `quotientCurve`-baseChange spelling out of the skeleton (artifact: [NISOG-L18]).
/-- **(KM 6.7.4; GATES [T-G3D-INFRA] + [KM-FMT-FLAT])** The image `G' = G mod G_d` of a
cyclic rank-`N` divisor `D` in the quotient curve `E' = E/G_d` is a cyclic subgroup
divisor of order `N/d`, and the image of any generator of `D` generates it. -/
theorem exists_imageDivisor {N : ℕ} [NeZero N] {D : RelEffCartierDiv E.π}
    (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d] [NeZero (N / d)] (hd : d ∣ N) :
    ∃ D' : RelEffCartierDiv (E.standardCyclicSubgroup hG hd).quotientCurve.π,
      (E.standardCyclicSubgroup hG hd).quotientCurve.IsGammaZeroFppf (N / d) D' ∧
      ∀ P₀ : E.Section, P₀.HasExactOrder E N → (P₀.orderDivisor E N).ideal = D.ideal →
        Section.HasExactOrder (E.standardCyclicSubgroup hG hd).quotientCurve
            ((E.standardCyclicSubgroup hG hd).pointMap P₀) (N / d) ∧
          (Section.orderDivisor (E.standardCyclicSubgroup hG hd).quotientCurve
              ((E.standardCyclicSubgroup hG hd).pointMap P₀) (N / d)).ideal = D'.ideal := by
  sorry

/-- **The standard cyclic quotient divisor `G' = G mod G_d`** (KM 6.7.6's naming), living
on the quotient curve `E/G_d`. Real `Classical.choose` definition off `exists_imageDivisor`. -/
noncomputable def imageDivisor {N : ℕ} [NeZero N] {D : RelEffCartierDiv E.π}
    (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d] [NeZero (N / d)] (hd : d ∣ N) :
    RelEffCartierDiv (E.standardCyclicSubgroup hG hd).quotientCurve.π :=
  (E.exists_imageDivisor hG hd).choose

/-- `G' = G mod G_d` is cyclic of order `N/d` (KM 6.7.4). Pin, proved from `choose_spec`. -/
theorem imageDivisor_isGammaZeroFppf {N : ℕ} [NeZero N] {D : RelEffCartierDiv E.π}
    (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d] [NeZero (N / d)] (hd : d ∣ N) :
    (E.standardCyclicSubgroup hG hd).quotientCurve.IsGammaZeroFppf (N / d)
      (E.imageDivisor hG hd) :=
  (E.exists_imageDivisor hG hd).choose_spec.1

/-- The image of a generator of `D` generates `G' = G mod G_d` (KM 6.7.4's second clause
= KM 6.7.11(1)'s "`π_d P` generates `Ker π'`"). Pin, proved from `choose_spec`. -/
theorem imageDivisor_generator_spec {N : ℕ} [NeZero N] {D : RelEffCartierDiv E.π}
    (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d] [NeZero (N / d)] (hd : d ∣ N)
    (P₀ : E.Section) (hord : P₀.HasExactOrder E N)
    (hgen : (P₀.orderDivisor E N).ideal = D.ideal) :
    Section.HasExactOrder (E.standardCyclicSubgroup hG hd).quotientCurve
        ((E.standardCyclicSubgroup hG hd).pointMap P₀) (N / d) ∧
      (Section.orderDivisor (E.standardCyclicSubgroup hG hd).quotientCurve
          ((E.standardCyclicSubgroup hG hd).pointMap P₀) (N / d)).ideal =
        (E.imageDivisor hG hd).ideal :=
  (E.exists_imageDivisor hG hd).choose_spec.2 P₀ hord hgen

-- ATTACK: (1) forward direction is the pins above (KM: 6.7.11(1) "is part (1) of the
-- preceding theorem"); the CONTENT is the converse, KM's cartesian-diagram argument via
-- the Useful Lemma applied to `Ker π`, `(Ker π)^×` and the fibre product — in-project this
-- is `exists_incidenceLocusEQ` + [KM-FMT-FLAT] universal-case flatness + the dense-open
-- `S ⊗ ℤ[1/N]` check. (2) the same-prime-factors hypothesis is genuinely needed: for
-- `N = p·q`, `d = p ∤ q^∞`, the point `0` generates `Ker π' = G/G_p` of order `q` never
-- forces `0` to generate `G` (KM 6.7.11(2)'s parenthetical is an iff ONLY under the
-- hypothesis). (3) `hPD` (the point lies on `D`) mirrors KM's `P ∈ (Ker π)(S)` — without
-- it the LHS could hold for a point of exact order `N` lying on a different cyclic
-- subgroup with the same image behaviour.
/-- **(KM 6.7.11(2), Backing-up; GATES [T-G3D-INFRA] + [KM-FMT-FLAT])** If `N` and `N/d`
have the same prime factors, then a point `P` of `D` generates `D` **iff** its image
`π_d(P)` generates the standard quotient `G' = G mod G_d`: *"If `N` and `N/d` have the
same prime factors, then `P` generates `Ker π` if and only if `π_d P` generates
`Ker π'`."* -/
theorem generator_iff_pointMap_generator {N : ℕ} [NeZero N] {D : RelEffCartierDiv E.π}
    (hG : E.IsGammaZeroFppf N D) {d : ℕ} [NeZero d] [NeZero (N / d)] (hd : d ∣ N)
    (hsp : ∀ p : ℕ, p.Prime → (p ∣ N ↔ p ∣ N / d)) (P : E.Section)
    (hPD : ∃ h : S ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = P.1) :
    (P.HasExactOrder E N ∧ (P.orderDivisor E N).ideal = D.ideal) ↔
      (Section.HasExactOrder (E.standardCyclicSubgroup hG hd).quotientCurve
          ((E.standardCyclicSubgroup hG hd).pointMap P) (N / d) ∧
        (Section.orderDivisor (E.standardCyclicSubgroup hG hd).quotientCurve
            ((E.standardCyclicSubgroup hG hd).pointMap P) (N / d)).ideal =
          (E.imageDivisor hG hd).ideal) := by
  sorry

-- ATTACK: (1) this is KM 6.7.8's (1) ⟹ (2),(3) at the kernel level, in the
-- `d₂`-invertible special case of the étale hypothesis (KM: *"a condition which is
-- automatic if `d₂` is invertible on `S`"*); the étale-general form waits on BB-DIFF
-- (in-flight) and is recorded as a Phase-2 leaf. (2) KM's proof pivots on (1.11.2)
-- (surjectivity of the induced generator against the exact sequence
-- `0 → Ker π₁ → G → Ker π₂ → 0`) — a Ch. 1 gate, no project analogue yet. (3) rank
-- bookkeeping: `D₁ ≤ D` of degrees `d₁ ∣ d₁d₂` does NOT alone make `D₁` standard — over
-- `ℤ[1/N]`, `(ℤ/d₁d₂)` has a unique subgroup of order `d₁`, and THAT is what the
-- invertibility hypothesis buys; in char `p ∣ d₁` uniqueness fails (e.g. `E[p] ⊃ Ker F`,
-- `μ_p` in the split ordinary case), so `hinv` cannot be dropped from this route.
/-- **(KM 6.7.8, `d₂` invertible; GATES [KM-1.11.2] + [T-D10-FPPF])** If `D` is cyclic of
order `d₁·d₂` with `d₂` invertible on `S`, then any rank-`d₁` subgroup subdivisor
`D₁ ≤ D` is cyclic and equals the standard cyclic subgroup `D_{d₁}` — i.e. a factorization
of a cyclic isogeny whose second factor is étale is automatically cyclic in standard
order. -/
theorem isGammaZeroFppf_subdivisor_of_invertible {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    [NeZero (d₁ * d₂)] {D : RelEffCartierDiv E.π} (hG : E.IsGammaZeroFppf (d₁ * d₂) D)
    (hinv : NIsInvertible S d₂) {D₁ : RelEffCartierDiv E.π} (hD₁ : D₁.IsSubgroup E)
    (hdeg₁ : ∀ s : S, D₁.degree s = d₁) (hle : RelEffCartierDiv.IsSubdivisor D₁ D) :
    E.IsGammaZeroFppf d₁ D₁ ∧ D₁ = E.standardCyclicDivisor hG (dvd_mul_right d₁ d₂) := by
  sorry

/-! ## §8 Squarefree levels and the Γ₀(N) space (KM 6.8.7, 6.6.1-core)

KM 6.8.7 (print p. 183, verbatim in the artifact): *"If `N ≥ 1` is a square-free integer,
then every `N`-isogeny is cyclic, i.e., the closed immersion of moduli problems over (Ell)
`[Γ₀(N)] ↪ [N-Isog]` is an isomorphism."* -/

-- ATTACK: (1) KM's route: "G is cyclic" is a closed condition (6.4.1) + reduction to the
-- universal case flat over `ℤ` [KM-FMT-FLAT] + density of `S ⊗ ℤ[1/N]` + "an abelian group
-- of square-free order is cyclic" (mathlib: `IsCyclic` from squarefree card via
-- `isCyclic_of_squarefree_card`-shaped lemmas — verified present as
-- `IsCyclic.of_squarefree_card`? artifact records the exact name hunt); the closedness
-- input is `exists_cyclicityLocus` above. (2) squarefree is sharp: KM 6.8.8 shows
-- `[pⁿ-Isog]`, `n ≥ 2`, is not even normal — no statement drift toward general `N`.
-- (3) over `S = Spec 𝔽_p` with `p ∣ N`, `N` squarefree still forces cyclicity — e.g.
-- `Ker F ⊆ E[p]` supersingular IS cyclic (generator `0`) — consistent with the fppf
-- record (`IsGammaZero`'s char-`p` adversarial fix banked at T-D10).
/-- **(KM 6.8.7; GATES [KM-FMT-FLAT] + cyclicity locus)** For `N` squarefree, every
rank-`N` subgroup divisor is cyclic: `[Γ₀(N)] = [N-Isog]`. -/
theorem isGammaZeroFppf_of_squarefree {N : ℕ} [NeZero N] (hsq : Squarefree N)
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E)
    (hdeg : ∀ s : S, D.degree s = N) : E.IsGammaZeroFppf N D := by
  sorry

/-- **(KM 6.6.1, RR-core: the Γ₀(N) classifying space over `S`)** There is a finite
`S`-scheme classifying Γ₀(N)-structures (KM: *"`[Γ₀(N)]` is relatively represented by the
closed subscheme of the finite `S`-scheme `[N-Isog]_{E/S}` over which the universal
`N`-isogeny is cyclic"*, print p. 166). Assembly of `exists_nIsogSpace` ([NISOG-GRASS])
and `exists_cyclicityLocus` (T-SG3). Stated against `GammaZeroStructure` — the T-SG2
fppf record — per the review GATE (never the geometric surrogate). The finite-flatness,
degree `N·Π(1+1/p)`, and regularity clauses of KM 6.6.1 are (Ell)-global/FMT content,
boarded separately (artifact §6.6). -/
theorem exists_gammaZeroSpace (N : ℕ) [NeZero N] :
    ∃ (W : Scheme.{u}) (w : W ⟶ S), IsFinite w ∧
      ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S),
        Nonempty (GammaZeroStructure (E.baseChange t) N ≃ { h : T ⟶ W // h ≫ w = t }) := by
  sorry

end EllipticCurve

end ModularCurves
