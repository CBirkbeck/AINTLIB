import ModularCurves.LevelStructure.Basic

/-!
# The category Ell/R and moduli problems (KM Ch. 4; Loeffler §3.7)

Katz–Mazur's stacks-without-saying-so formalism, transcribed from Loeffler Def 3.7.1
(verbatim):

> "Let `Ell/R` be the following category: objects are diagrams `E → S` where `S` is some
> `R`-scheme and `E` is an elliptic curve over `S`; morphisms are squares … where
> `E ≅ E' ×_T S`. A *moduli problem* for elliptic curves over `R` is a contravariant
> functor `P : Ell/R → Set`. We say that `P` is *representable* if it is representable; it
> is *relatively representable* if, for every `E/S ∈ Ob(Ell/R)`, the functor
> `Sch/S → Set, T ↦ P(E ×_S T/T)` is representable."

and Loeffler Def 3.7.3 / Thm 3.7.4 (KM 4.7):

> "`P` is *rigid* if for all `E/S`, `Aut(E/S)` acts on `P(E/S)` without fixed points."
> "(Katz–Mazur) `P` is representable if and only if it is relatively representable and
> rigid."

The stack remark (Loeffler, after 3.7.1): "The category `Ell/R` is `Sch/Y` for a `Y` that
does not exist. … This is the idea of *stacks*" — the stack-facing packaging lives in
`Moduli/Stack.lean`.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/-- An object of `Ell/R`: an `R`-scheme `S` together with an elliptic curve `E/S`.
Source: Loeffler Def 3.7.1; KM 4.1. -/
structure EllObj (R : CommRingCat.{u}) where
  /-- The base `R`-scheme. -/
  base : Scheme.{u}
  /-- The structure morphism to `Spec R`. -/
  structMap : base ⟶ Spec R
  /-- The elliptic curve over the base. -/
  curve : EllipticCurve base

variable {R : CommRingCat.{u}}

/-- A morphism of `Ell/R`: a cartesian square over a morphism of `R`-schemes,
compatible with the zero sections.

On `zero_w` (adversarial adjudication, 2026-07-06): the zero clause is NOT in
Loeffler's display (the ellipsis in the quoted Def 3.7.1 is only the square diagram)
and is NOT automatic — a translation `τ_P` over `𝟙` is a cartesian non-pointed square.
It is nonetheless the sources' intended category: "elliptic curve" is the pair
`(E, 0)`, without it the level-structure functors are not functors (translations
destroy torsion data), and Loeffler's own Thm 3.7.4 would be false (Aut would contain
all translations). Verbatim KM 4.1 reconciliation: PENDING-SOURCE(KM Ch. 4).
Source: Loeffler Def 3.7.1 ("morphisms are squares … where `E ≅ E' ×_T S`"); KM 4.1. -/
structure EllHom (X Y : EllObj R) where
  baseHom : X.base ⟶ Y.base
  base_w : baseHom ≫ Y.structMap = X.structMap
  top : X.curve.E ⟶ Y.curve.E
  /-- The square is cartesian: `E ≅ E' ×_T S`. -/
  isPullback : IsPullback top X.curve.π Y.curve.π baseHom
  /-- Compatibility with the zero sections. -/
  zero_w : X.curve.zero ≫ top = baseHom ≫ Y.curve.zero

attribute [ext] EllHom

instance : Category (EllObj R) where
  Hom := EllHom
  id X :=
    { baseHom := 𝟙 _
      base_w := by simp
      top := 𝟙 _
      isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩
      zero_w := by simp }
  comp f g :=
    { baseHom := f.baseHom ≫ g.baseHom
      base_w := by rw [Category.assoc, g.base_w, f.base_w]
      top := f.top ≫ g.top
      isPullback := f.isPullback.paste_horiz g.isPullback
      zero_w := by rw [← Category.assoc, f.zero_w, Category.assoc, g.zero_w,
        Category.assoc] }
  id_comp := by intros; ext <;> simp
  comp_id := by intros; ext <;> simp
  assoc := by intros; ext <;> simp

/-- A **moduli problem** for elliptic curves over `R`: a contravariant functor
`Ell/R → Set`. Source: Loeffler Def 3.7.1(2); KM 4.2. -/
abbrev ModuliProblem (R : CommRingCat.{u}) := (EllObj R)ᵒᵖ ⥤ Type u

namespace ModuliProblem

/-- The base change of an `Ell/R` object along `g : T ⟶ S` (an `R`-scheme morphism over
the base of `X`). Total space `E ×_S T`. -/
noncomputable def _root_.ModularCurves.EllObj.pullbackAlong (X : EllObj R)
    {T : Scheme.{u}} (g : T ⟶ X.base) : EllObj R where
  base := T
  structMap := g ≫ X.structMap
  curve := X.curve.baseChange g

/-- The canonical comparison morphism `X ×_S T' ⟶ X ×_S T` in `Ell/R` induced by
`k : T' ⟶ T` over `g : T ⟶ X.base` (base-change functoriality). -/
noncomputable def _root_.ModularCurves.EllObj.pullbackAlongMap (X : EllObj R)
    {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T) :
    X.pullbackAlong (k ≫ g) ⟶ X.pullbackAlong g where
  baseHom := k
  base_w := by simp [EllObj.pullbackAlong]
  top := Limits.pullback.map _ _ _ _ (𝟙 _) k (𝟙 _) (by simp) (by simp)
  isPullback := by
    have hbig := IsPullback.of_hasPullback X.curve.π (k ≫ g)
    have hfst : Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
          (by simp) (by simp) ≫ Limits.pullback.fst X.curve.π g =
        Limits.pullback.fst X.curve.π (k ≫ g) := by
      rw [Limits.pullback.lift_fst, Category.comp_id]
    rw [← hfst] at hbig
    refine IsPullback.of_right hbig ?_ (IsPullback.of_hasPullback X.curve.π g)
    show Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
        (by simp) (by simp) ≫ Limits.pullback.snd X.curve.π g =
      Limits.pullback.snd X.curve.π (k ≫ g) ≫ k
    rw [Limits.pullback.lift_snd]
  zero_w := by
    show Limits.pullback.lift ((k ≫ g) ≫ X.curve.zero) (𝟙 T')
        (by rw [Category.assoc, X.curve.zero_π, Category.comp_id, Category.id_comp]) ≫
      Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
        (by simp) (by simp) =
      k ≫ Limits.pullback.lift (g ≫ X.curve.zero) (𝟙 T)
        (by rw [Category.assoc, X.curve.zero_π, Category.comp_id, Category.id_comp])
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc]
      rw [show Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
            (by simp) (by simp) ≫ Limits.pullback.fst X.curve.π g =
          Limits.pullback.fst X.curve.π (k ≫ g) ≫ 𝟙 _ from
        Limits.pullback.lift_fst _ _ _]
      rw [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_fst]
      exact Category.comp_id _
    · simp only [Category.assoc]
      rw [show Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
            (by simp) (by simp) ≫ Limits.pullback.snd X.curve.π g =
          Limits.pullback.snd X.curve.π (k ≫ g) ≫ k from
        Limits.pullback.lift_snd _ _ _]
      rw [Limits.pullback.lift_snd_assoc, Limits.pullback.lift_snd]
      exact (Category.id_comp k).trans (Category.comp_id k).symm

/-- `P` is **representable** if it is a representable presheaf on `Ell/R` — mathlib's
`Functor.IsRepresentable`, under the project's name (kept as an `abbrev` so the two
never diverge). Source: Loeffler Def 3.7.1(3); KM 4.3. -/
abbrev Representable (P : ModuliProblem R) : Prop :=
  P.IsRepresentable

/-- `P` is **relatively representable**: for every `E/S` in `Ell/R`, the functor
`Sch/S → Set`, `T ↦ P(E ×_S T / T)` is representable — stated with its naturality
clause (the representing bijections commute with restriction along `T' ⟶ T`).
Source: Loeffler Def 3.7.1(3); KM 4.2. Full comma-category packaging: ticket `T-E3`. -/
def RelativelyRepresentable (P : ModuliProblem R) : Prop :=
  ∀ X : EllObj R, ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base),
    ∃ eqv : ∀ {T : Scheme.{u}} (g : T ⟶ X.base),
        { h : T ⟶ Z // h ≫ f = g } ≃ P.obj (Opposite.op (X.pullbackAlong g)),
      ∀ {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
        (h : { h : T ⟶ Z // h ≫ f = g }),
        eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
          P.map (X.pullbackAlongMap g k).op (eqv g h)

/-- `P` is **rigid**: for every `E/S`, `Aut(E/S)` (automorphisms over the identity of the
base) acts on `P(E/S)` without fixed points.
Source: Loeffler Def 3.7.3; KM 4.4 ("rigid moduli problems"). -/
def Rigid (P : ModuliProblem R) : Prop :=
  ∀ (X : EllObj R) (e : X ≅ X), e.hom.baseHom = 𝟙 X.base → e ≠ Iso.refl X →
    ∀ a : P.obj (Opposite.op X), P.map e.hom.op a ≠ a

/-- **Noetherian-local rigidity** — the fibre-detection variant of `Rigid` ([T-W7.8],
owner ruling v10.298): fixed-point-freeness demanded only at test objects with locally
noetherian base. This is exactly what the T-W7.7 rigidity engine proves without the
EGA IV §8 spreading-out gate (the `hLN` pin of the `Γ_H` chain), and it is all the
KM 4.7.0 engine ever consumes: its single rigidity call is at `XM.pullbackAlong t`
(`Moduli/QuotientProblem.lean`), and emptiness of the `γ`-fixed locus is detected on
field-valued points, whose bases are locally noetherian
(`simulSchemeAction_free_of_rigidNoeth`). The literal KM 4.4 form `Rigid` stays as the
reference statement; the unrestricted detection bridge `RigidNoeth → Rigid` is EGA IV §8
material, parked as [T-W7.8-L2-PARKED]. -/
def RigidNoeth (P : ModuliProblem R) : Prop :=
  ∀ (X : EllObj R), IsLocallyNoetherian X.base →
    ∀ (e : X ≅ X), e.hom.baseHom = 𝟙 X.base → e ≠ Iso.refl X →
      ∀ a : P.obj (Opposite.op X), P.map e.hom.op a ≠ a

/-- Unrestricted rigidity restricts to noetherian-based test objects. -/
theorem Rigid.rigidNoeth {P : ModuliProblem R} (h : P.Rigid) : P.RigidNoeth :=
  fun X _ => h X

/-- `P` is **affine over `Ell`**: relatively representable *by an affine morphism*. This is
KM's standing hypothesis in SCHOLIE (4.7.0) — "relatively representable **and affine over**
(Ell)" (book p. 111) — and it is what makes the free quotient `𝕸(𝒫, δ)/G` of the engine's
proof exist as a scheme. Source: KM 4.7.0 + 4.2; the same hypothesis reappears as "affine and
étale over (Ell)" in KM 4.7.1/4.7.2 and in [Loe] 3.8.2. -/
def AffineOverEll (P : ModuliProblem R) : Prop :=
  ∀ X : EllObj R, ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base), IsAffineHom f ∧
    ∃ eqv : ∀ {T : Scheme.{u}} (g : T ⟶ X.base),
        { h : T ⟶ Z // h ≫ f = g } ≃ P.obj (Opposite.op (X.pullbackAlong g)),
      ∀ {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
        (h : { h : T ⟶ Z // h ≫ f = g }),
        eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
          P.map (X.pullbackAlongMap g k).op (eqv g h)

/-- Affine-over-`Ell` forgets to relative representability (KM: "relatively representable
*and* affine"). -/
theorem AffineOverEll.relativelyRepresentable {P : ModuliProblem R} (hP : P.AffineOverEll) :
    P.RelativelyRepresentable := fun X => by
  obtain ⟨Z, f, -, eqv, hnat⟩ := hP X
  exact ⟨Z, f, eqv, hnat⟩

/-- **(T-E5a, KM 4.4 / [Loe] Exercise (1))** A representable moduli problem is rigid.

KM p. 111, inside the proof of SCHOLIE (4.7.0): *"As already pointed out above (4.4), any
representable problem is automatically rigid."*

Proof: if `a ∈ P(X)` is fixed by an automorphism `e` of `X` over the identity of the base,
transport `a` to the classifying morphism `u = homEquiv⁻¹ a : X ⟶ X₀`; the fixing says
`e.hom ≫ u = u`, hence `e.hom.top ≫ u.top = u.top`, and `e.hom.top ≫ X.curve.π = X.curve.π`
holds because `e.hom.baseHom = 𝟙`. Since `u`'s square is **cartesian** (this is where the
`Ell`-morphism data is used), `IsPullback.hom_ext` forces `e.hom.top = 𝟙`, so `e = Iso.refl`.
Note the cartesian square of `u` is indispensable: an elliptic curve does have nontrivial
automorphisms over the identity of its base (e.g. `[-1]`), and it is exactly the existence of
`a` — i.e. of `u` — that kills them. -/
theorem rigid_of_representable {P : ModuliProblem R} (hP : P.Representable) : P.Rigid := by
  intro X e hbase hne a
  intro hfix
  refine hne (Iso.ext ?_)
  haveI : P.IsRepresentable := hP
  set repr := Functor.representableBy P with hrepr
  set u : X ⟶ Functor.reprX P := repr.homEquiv.symm a with hu
  have hcomp : repr.homEquiv (e.hom ≫ u) = P.map e.hom.op (repr.homEquiv u) :=
    repr.homEquiv_comp e.hom u
  rw [hu, Equiv.apply_symm_apply] at hcomp
  have heu : e.hom ≫ u = u := by
    refine repr.homEquiv.injective ?_
    rw [hcomp, hfix, hu, Equiv.apply_symm_apply]
  -- the top component is forced to be the identity by the cartesian square of `u`
  have htop : e.hom.top = 𝟙 X.curve.E := by
    refine u.isPullback.hom_ext ?_ ?_
    · exact (congrArg EllHom.top heu).trans (Category.id_comp u.top).symm
    · calc e.hom.top ≫ X.curve.π = X.curve.π ≫ e.hom.baseHom := e.hom.isPullback.w
        _ = X.curve.π := by rw [hbase, Category.comp_id]
        _ = 𝟙 X.curve.E ≫ X.curve.π := (Category.id_comp _).symm
  exact EllHom.ext hbase htop

/-- **(T-E5 = KM SCHOLIE 4.7.0)** A moduli problem which is **affine over `Ell`** is
representable iff it is relatively representable and rigid.

**Source of record** (quote pass, T-E5-KM47, 2026-07-08; full verbatim in
`.mathlib-quality/km47-source-quotes.md`).

*Katz–Mazur, SCHOLIE (4.7.0), book p. 111 (pdf 122)*, verbatim:
> "Let `𝒫` be relatively representable **and affine over** (Ell); then a necessary and
> sufficient condition that `𝒫` be representable is that `𝒫` be rigid."

**Lean ↔ source match.** `ModuliProblem R = (EllObj R)ᵒᵖ ⥤ Type u` is KM's "moduli problem on
(Ell/R)" (Loe Def 3.7.1(2)); `Representable` is KM's "`𝒫` is representable" — the functor on
`Ell/R`, *not* KM's `𝒫̃` on `Sch/R`; `RelativelyRepresentable` is KM 4.2 / Loe 3.7.1(3);
`AffineOverEll` is KM's "affine over (Ell)"; `Rigid` is KM 4.4 / Loe Def 3.7.3 verbatim. With
`hP : P.AffineOverEll` the statement below is **KM's SCHOLIE 4.7.0 verbatim**.

**B2 STATEMENT AMENDMENT (2026-07-08, owner-approved; logged in `b2_log.jsonl`).** The
previous statement — `P.Representable ↔ P.RelativelyRepresentable ∧ P.Rigid` with *no*
affineness, i.e. [Loe] Thm 3.7.4 verbatim — was **not supported by either source's proof**.
KM uses affineness three times: p. 112 (`𝕸(𝒫, δ)` affine over the affine `𝕸(δ)` ⟹ absolutely
affine), p. 113 (*"Because `𝕸(𝒫, δ)` is affine, the quotient `𝕸(𝒫, δ)/G` exists"* — a free
finite-group quotient of a general scheme is only an algebraic space), p. 114 (α_univ descends
*"because `𝒫` is relatively affine"*, SGA I VIII 7.8). Loeffler's own quotient input (Prop
3.6.1) is stated only for **quasiprojective** `X`, so even his sketch tacitly assumes what his
3.7.4 omits.

**DOCUMENTED NON-GOAL (never silently deleted).** The unrestricted form
`∀ P, P.Representable ↔ P.RelativelyRepresentable ∧ P.Rigid` is **not** a target of this
development. Beyond the three uses above, KM's own Appendix (A.4) is the warning label: it
records that `𝒫̃`-representability is strictly weaker than `𝒫`-representability — *"it is not
in general true that `𝒫̃` representable ⟹ `𝒫` rigid"* — and exhibits **Gabber's
counterexample (A.4.1.3)**: over a ring carrying an elliptic curve `E₀`, the problem
`𝒫(E/S) = {∗}` if `E/S ≅ E₀/S` and `∅` otherwise is not rigid (`[-1]` acts trivially) while
`𝒫̃` is representable by `Spec R` itself. Any attempt at the unrestricted statement must first
say which of `𝒫`, `𝒫̃` it means and must exit the category of schemes for the quotient; that
is an algebraic-spaces development, out of scope (no algebraic spaces in mathlib). See
[T-E5-ISOM] for the one direction that *is* unrestricted-but-gated.

**Decomposition** (board): `⇒` = `rigid_of_representable` (T-E5a, **proven above**) together
with `AffineOverEll.relativelyRepresentable` (free from the hypothesis — note that *without*
`hP` this half needs the Isom-scheme of the universal curve, **[T-E5-ISOM]**, gated, not
built). `⇐` = KM's engine of p. 112 (`representable_of_rigid_of_torsor`,
`Moduli/QuotientProblem.lean`, T-Q6e) instantiated twice, at
`(N, δ, G) = (3, naive level 3, GL₂(𝔽₃))` (T-E15, unblocked) and
`(2, Legendre, GL₂(ℤ/2) × {±1})` (T-E14, blocked on [T-E-OMEGA]), then "recollement" over
`ℤ[1/6]` (T-E5f). The engine is **never re-derived here** — only instantiated. -/
theorem representable_iff (P : ModuliProblem R) (hP : P.AffineOverEll) :
    P.Representable ↔ P.RelativelyRepresentable ∧ P.Rigid := by
  refine ⟨fun h => ⟨hP.relativelyRepresentable, rigid_of_representable h⟩, fun h => ?_⟩
  -- ⇐ : KM's engine (p. 112) instantiated at δ = naive level 3 and δ = Legendre, then
  -- glued over ℤ[1/6]. Leaves T-E5c/d/e/f; gated on T-Q6e + T-E14 + T-E15.
  sorry

/-- **KM 4.7 at noetherian-local rigidity** ([T-W7.8] variant interface, owner ruling
v10.298) — `representable_iff` with the rigidity input weakened to `RigidNoeth`.

`⇒` is the restriction of `rigid_of_representable`. `⇐` is the *same* KM p. 112 engine as
`representable_iff`'s: the engine consumes rigidity exactly once, through the freeness of
the `G`-action on `𝕸(𝒫,δ)`, and freeness is emptiness of the `γ`-fixed locus, which is
detected on field-valued points — locally noetherian bases, so `RigidNoeth` already yields
it on the nose (`simulSchemeAction_free_of_rigidNoeth`, `Moduli/QuotientProblem.lean`,
PROVEN). Same gate as `representable_iff`'s `⇐` (T-Q6e + T-E14 + T-E15); tracked as the
same box, discharged by the same instantiation the moment it lands. -/
theorem representable_iff_rigidNoeth (P : ModuliProblem R) (hP : P.AffineOverEll) :
    P.Representable ↔ P.RelativelyRepresentable ∧ P.RigidNoeth := by
  refine ⟨fun h => ⟨hP.relativelyRepresentable, (rigid_of_representable h).rigidNoeth⟩,
    fun h => ?_⟩
  -- ⇐ : the KM engine again, with its freeness input supplied by
  -- `simulSchemeAction_free_of_rigidNoeth` instead of `simulSchemeAction_free_of_rigid`.
  -- Gate: T-Q6e + T-E14 + T-E15 (shared with `representable_iff`).
  sorry

end ModuliProblem

end ModularCurves
