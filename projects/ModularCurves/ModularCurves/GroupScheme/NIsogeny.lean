import ModularCurves.GroupScheme.CyclicSubgroup
import ModularCurves.GroupScheme.DeligneOrder
import ModularCurves.GroupScheme.SubgroupQuotient
import ModularCurves.LevelStructure.Incidence
import ModularCurves.EllipticCurve.GroupLawDescent
import ModularCurves.EllipticCurve.RigiditySpreadingOut
import ModularCurves.ForMathlib.BaseChangeAlongCompat

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

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 5

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
section LocallyFreeRankLocusAux

open scoped TensorProduct

/-- **[L1-a, the local `n`-generator presentation]** A finitely presented module whose
field-fibre dimensions are everywhere `≤ n` admits, near every prime, a presentation by
`n` generators (Nakayama lift of a fibre spanning set + finite-type shrink). This is the
"further localizing on `S`, we may suppose" step of KM p. 163. -/
private theorem locallyFreeRankLocusAux_exists_presentation {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] {n : ℕ}
    (hb : ∀ (K : Type u) (_ : Field K) (_ : Algebra R K), Module.finrank K (K ⊗[R] M) ≤ n)
    (p : PrimeSpectrum R) :
    ∃ g : R, g ∉ p.asIdeal ∧ ∃ (m : ℕ)
      (α : (Fin m → Localization.Away g) →ₗ[Localization.Away g]
        (Fin n → Localization.Away g))
      (π : (Fin n → Localization.Away g) →ₗ[Localization.Away g]
        (Localization.Away g ⊗[R] M)),
      Function.Surjective π ∧ Function.Exact α π := by
  classical
  -- (i) `n` elements of `M` spanning the stalk at `p` (fibre-basis lift + Nakayama)
  obtain ⟨x, hx⟩ : ∃ x : Fin n → M, Subsingleton (LocalizedModule p.asIdeal.primeCompl
      (M ⧸ Submodule.span R (Set.range x))) := by
    -- `n` elements whose images span the residue fibre `κ(p) ⊗ M`
    obtain ⟨x, hxspan⟩ : ∃ x : Fin n → M,
        Submodule.span p.asIdeal.ResidueField
          (Set.range fun i => (1 : p.asIdeal.ResidueField) ⊗ₜ[R] x i) = ⊤ := by
      have hdim : Module.finrank p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[R] M) ≤ n := hb _ inferInstance inferInstance
      -- the simple tensors `1 ⊗ m` span the fibre
      have hspan : ⊤ ≤ Submodule.span p.asIdeal.ResidueField
          (Set.range fun m : M => (1 : p.asIdeal.ResidueField) ⊗ₜ[R] m) := by
        rintro z -
        induction z with
        | zero => exact Submodule.zero_mem _
        | tmul c m =>
          rw [show c ⊗ₜ[R] m = c • ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] m) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
          exact Submodule.smul_mem _ c (Submodule.subset_span ⟨m, rfl⟩)
        | add z₁ z₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
      -- extract a basis of the fibre inside the simple tensors, and choose preimages
      let b := Module.Basis.ofSpan hspan
      haveI : Fintype ((linearIndepOn_empty p.asIdeal.ResidueField id).extend
          (Set.empty_subset (Set.range fun m : M =>
            (1 : p.asIdeal.ResidueField) ⊗ₜ[R] m))) :=
        FiniteDimensional.fintypeBasisIndex b
      have hsub := (linearIndepOn_empty p.asIdeal.ResidueField id).extend_subset
        (Set.empty_subset (Set.range fun m : M =>
          (1 : p.asIdeal.ResidueField) ⊗ₜ[R] m))
      have hmem : ∀ i : ((linearIndepOn_empty p.asIdeal.ResidueField id).extend
          (Set.empty_subset (Set.range fun m : M =>
            (1 : p.asIdeal.ResidueField) ⊗ₜ[R] m))),
          ∃ m : M, (1 : p.asIdeal.ResidueField) ⊗ₜ[R] m
            = (i : p.asIdeal.ResidueField ⊗[R] M) := fun i => hsub i.2
      choose mfun hmfun using hmem
      have hcard : Fintype.card _ ≤ n := (Module.finrank_eq_card_basis b) ▸ hdim
      refine ⟨fun j => if h : (j : ℕ) < Fintype.card _
        then mfun ((Fintype.equivFin _).symm ⟨j, h⟩) else 0, ?_⟩
      rw [eq_top_iff, ← b.span_eq]
      refine Submodule.span_le.mpr ?_
      rintro z ⟨i, rfl⟩
      have hj : ((Fin.castLE hcard ((Fintype.equivFin _) i)) : ℕ) < Fintype.card _ :=
        ((Fintype.equivFin _) i).2
      refine Submodule.subset_span ⟨Fin.castLE hcard ((Fintype.equivFin _) i), ?_⟩
      have hidx : (⟨((Fin.castLE hcard ((Fintype.equivFin _) i)) : ℕ), hj⟩ :
          Fin (Fintype.card _)) = (Fintype.equivFin _) i := Fin.ext rfl
      simp only [dif_pos hj, hidx, Equiv.symm_apply_apply, hmfun i]
      exact (Module.Basis.ofSpan_apply_self hspan i).symm
    refine ⟨x, ?_⟩
    -- fibre of the quotient vanishes, hence the stalk at `p` vanishes (support of a f.g. module)
    have hfib : Subsingleton (p.asIdeal.ResidueField ⊗[R]
        (M ⧸ Submodule.span R (Set.range x))) := by
      set q := (Submodule.span R (Set.range x)).mkQ with hq
      have hqsurj : Function.Surjective (q.baseChange p.asIdeal.ResidueField) := by
        have := LinearMap.lTensor_surjective p.asIdeal.ResidueField
          (Submodule.mkQ_surjective (Submodule.span R (Set.range x)))
        rwa [show (⇑(q.baseChange p.asIdeal.ResidueField)) = ⇑(q.lTensor _) from rfl]
      have hker : ∀ w : p.asIdeal.ResidueField ⊗[R] M,
          q.baseChange p.asIdeal.ResidueField w = 0 := by
        intro w
        have hw : w ∈ Submodule.span p.asIdeal.ResidueField
            (Set.range fun i => (1 : p.asIdeal.ResidueField) ⊗ₜ[R] x i) := by
          rw [hxspan]; trivial
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
        · rintro _ ⟨i, rfl⟩
          rw [LinearMap.baseChange_tmul,
            show q (x i) = 0 from (Submodule.Quotient.mk_eq_zero _).mpr
              (Submodule.subset_span ⟨i, rfl⟩),
            TensorProduct.tmul_zero]
        · exact map_zero _
        · intro y z _ _ hy hz
          rw [map_add, hy, hz, add_zero]
        · intro c y _ hy
          rw [map_smul, hy, smul_zero]
      refine ⟨fun z₁ z₂ => ?_⟩
      obtain ⟨w₁, rfl⟩ := hqsurj z₁
      obtain ⟨w₂, rfl⟩ := hqsurj z₂
      rw [hker w₁, hker w₂]
    rw [← not_nontrivial_iff_subsingleton] at hfib ⊢
    intro hnt
    exact hfib ((Module.mem_support_iff_nontrivial_residueField_tensorProduct p).mp
      (Module.mem_support_iff.mpr hnt))
  -- (ii) the spanning descends to a basic open `D(g)`
  haveI := hx
  obtain ⟨g, hgp, hgsub⟩ := LocalizedModule.exists_subsingleton_away
    (M := M ⧸ Submodule.span R (Set.range x)) p.asIdeal
  refine ⟨g, hgp, ?_⟩
  -- (iii) assemble: the induced surjection onto `R_g ⊗ M` and its f.g. kernel
  haveI := hgsub
  haveI hsub2 : Subsingleton ((Localization.Away g) ⊗[R]
      (M ⧸ Submodule.span R (Set.range x))) :=
    (LocalizedModule.equivTensorProduct (Submonoid.powers g)
      (M ⧸ Submodule.span R (Set.range x))).symm.toEquiv.subsingleton
  -- the simple tensors `1 ⊗ x i` span `R_g ⊗ M`
  have hspanRg : Submodule.span (Localization.Away g)
      (Set.range fun i => (1 : Localization.Away g) ⊗ₜ[R] x i) = ⊤ := by
    have key : ∀ s ∈ Submodule.span R (Set.range x), ∀ c : Localization.Away g,
        c ⊗ₜ[R] s ∈ Submodule.span (Localization.Away g)
          (Set.range fun i => (1 : Localization.Away g) ⊗ₜ[R] x i) := by
      intro s hs
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hs
      · rintro _ ⟨i, rfl⟩ c
        rw [show c ⊗ₜ[R] x i = c • ((1 : Localization.Away g) ⊗ₜ[R] x i) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)
      · intro c
        rw [TensorProduct.tmul_zero]
        exact Submodule.zero_mem _
      · intro y z _ _ hy hz c
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ (hy c) (hz c)
      · intro r y _ hy c
        rw [TensorProduct.tmul_smul]
        exact Submodule.smul_of_tower_mem _ r (hy c)
    haveI : Subsingleton (((Localization.Away g) ⊗[R] M) ⧸
        (LinearMap.range (TensorProduct.map
          (LinearMap.id : Localization.Away g →ₗ[R] Localization.Away g)
          (Submodule.span R (Set.range x)).subtype))) :=
      (TensorProduct.tensorQuotientEquiv (Localization.Away g)
        (Submodule.span R (Set.range x))).symm.toEquiv.subsingleton
    have htop : LinearMap.range (TensorProduct.map
        (LinearMap.id : Localization.Away g →ₗ[R] Localization.Away g)
        (Submodule.span R (Set.range x)).subtype) = ⊤ :=
      eq_top_iff.mpr fun z _ => (Submodule.Quotient.mk_eq_zero _).mp
        (Subsingleton.elim _ 0)
    refine eq_top_iff.mpr fun z _ => ?_
    have hz : z ∈ LinearMap.range (TensorProduct.map
        (LinearMap.id : Localization.Away g →ₗ[R] Localization.Away g)
        (Submodule.span R (Set.range x)).subtype) := htop ▸ Submodule.mem_top
    obtain ⟨w, rfl⟩ := hz
    induction w with
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | tmul c s =>
      obtain ⟨s, hs⟩ := s
      simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, Submodule.coe_subtype]
      exact key s hs c
    | add w₁ w₂ h₁ h₂ =>
      rw [map_add]
      exact Submodule.add_mem _ (h₁ Submodule.mem_top) (h₂ Submodule.mem_top)
  -- the presentation: `π` sends `e_i ↦ 1 ⊗ x i`; `α` enumerates a finite kernel basis
  have hπ' : Function.Surjective (Fintype.linearCombination (Localization.Away g)
      (fun i => (1 : Localization.Away g) ⊗ₜ[R] x i)) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspanRg]
  have hkfg : (LinearMap.ker (Fintype.linearCombination (Localization.Away g)
      (fun i => (1 : Localization.Away g) ⊗ₜ[R] x i))).FG :=
    Module.FinitePresentation.fg_ker _ hπ'
  obtain ⟨m, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hkfg
  refine ⟨m, Fintype.linearCombination (Localization.Away g) k,
    Fintype.linearCombination (Localization.Away g)
      (fun i => (1 : Localization.Away g) ⊗ₜ[R] x i), hπ', ?_⟩
  rw [LinearMap.exact_iff, Fintype.range_linearCombination, hk]

/-- **[L1-b, the affine core]** For `M = coker (α : R^m → R^n)` and any `R`-algebra `A`:
the base change `A ⊗ M` is finite locally free of rank `n` (flat with all stalk ranks `n`)
iff every matrix entry of `α` dies in `A`. Forward: flat + finite ⟹ free stalks; the
surjection `A^n ↠ A ⊗ M` has finitely generated kernel (fp) which vanishes fibrewise by
rank count, hence vanishes (Nakayama at every prime), so `α ⊗ A = 0` by right-exactness.
Backward: `α ⊗ A = 0` makes `A ⊗ M ≅ A^n`. KM p. 163: `W ∩ U = V(coefficients of α)`. -/
private theorem locallyFreeRankLocusAux_core_iff {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {m n : ℕ} (α : (Fin m → R) →ₗ[R] (Fin n → R))
    {M : Type u} [AddCommGroup M] [Module R M] (π : (Fin n → R) →ₗ[R] M)
    (hπ : Function.Surjective π) (hexact : Function.Exact α π) :
    (Module.Flat A (A ⊗[R] M) ∧
        ∀ p : PrimeSpectrum A, Module.rankAtStalk (A ⊗[R] M) p = n) ↔
      ∀ (i : Fin m) (j : Fin n), algebraMap R A (α (Pi.single i 1) j) = 0 := by
  -- The base-changed presentation is exact (right-exactness of `A ⊗ -`).
  have hexA : Function.Exact (α.baseChange A) (π.baseChange A) := by
    have h1 : Function.Exact (α.lTensor A) (π.lTensor A) := lTensor_exact A hexact hπ
    rwa [show (⇑(α.baseChange A) : A ⊗[R] (Fin m → R) → A ⊗[R] (Fin n → R))
        = ⇑(α.lTensor A) from rfl,
      show (⇑(π.baseChange A) : A ⊗[R] (Fin n → R) → A ⊗[R] M) = ⇑(π.lTensor A) from rfl]
  have hsurjA : Function.Surjective (π.baseChange A) := by
    have := LinearMap.lTensor_surjective A hπ
    rwa [show (⇑(π.baseChange A) : A ⊗[R] (Fin n → R) → A ⊗[R] M) = ⇑(π.lTensor A) from rfl]
  constructor
  · -- flat + constant rank `n` ⟹ the presentation matrix dies in `A`
    rintro ⟨hflat, hrank⟩
    haveI := hflat
    -- `M`, hence `A ⊗ M`, is finitely presented; so the kernel `K` of `πₐ` is f.g.
    haveI hMfp : Module.FinitePresentation R M := by
      refine Module.finitePresentation_of_surjective π hπ ?_
      rw [LinearMap.exact_iff.mp hexact, LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map α
    haveI : Module.Projective A (A ⊗[R] M) := Module.Flat.projective_of_finitePresentation
    obtain ⟨s, hs⟩ := Module.projective_lifting_property (π.baseChange A)
      LinearMap.id hsurjA
    have hs' : ∀ y : A ⊗[R] M, (π.baseChange A) (s y) = y := fun y =>
      congrArg (fun g : A ⊗[R] M →ₗ[A] A ⊗[R] M => g y) hs
    have hsinj : Function.Injective s := fun y₁ y₂ h => by
      rw [← hs' y₁, ← hs' y₂, h]
    -- the section splits the free module as `range s ⊕ K`
    set K := LinearMap.ker (π.baseChange A) with hK
    let pr : (A ⊗[R] (Fin n → R)) →ₗ[A] LinearMap.range s :=
      (s ∘ₗ π.baseChange A).codRestrict (LinearMap.range s) fun x => ⟨_, rfl⟩
    have hproj : ∀ x : LinearMap.range s, pr x = x := by
      rintro ⟨_, y, rfl⟩
      exact Subtype.ext (by simp [pr, hs' y])
    have hkerpr : LinearMap.ker pr = K := by
      ext x
      simp only [LinearMap.mem_ker, hK]
      constructor
      · intro h
        have := congrArg Subtype.val h
        simp only [LinearMap.codRestrict_apply, pr, LinearMap.coe_comp,
          Function.comp_apply, ZeroMemClass.coe_zero] at this
        have h2 := congrArg (π.baseChange A) this
        rwa [hs', map_zero] at h2
      · intro h
        refine Subtype.ext ?_
        simp [pr, h]
    have hcompl : IsCompl (LinearMap.range s) K := by
      rw [← hkerpr]
      exact LinearMap.isCompl_of_proj hproj
    -- rank bookkeeping: `n = n + rankAtStalk K`, so `K` has rank `0` everywhere
    haveI hKfin : Module.Finite A K := by
      rw [Module.Finite.iff_fg]
      exact Module.FinitePresentation.fg_ker (π.baseChange A) hsurjA
    haveI hKflat : Module.Flat A K := by
      have : Module.Projective A K := by
        refine .of_split (LinearMap.ker (π.baseChange A)).subtype
          ((LinearMap.id - s ∘ₗ π.baseChange A).codRestrict _ fun x => by
            rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
              LinearMap.coe_comp, Function.comp_apply, map_sub, hs', sub_self]) ?_
        ext x
        simp [LinearMap.mem_ker.mp x.2]
      exact Module.Flat.of_projective
    haveI : Module.Finite A (LinearMap.range s) :=
      Module.Finite.equiv (LinearEquiv.ofInjective s hsinj)
    haveI : Module.Flat A (LinearMap.range s) :=
      Module.Flat.of_linearEquiv (LinearEquiv.ofInjective s hsinj).symm
    have hKrank : Module.rankAtStalk (R := A) K = 0 := by
      have e3 : (LinearMap.range s × K) ≃ₗ[A] (A ⊗[R] (Fin n → R)) :=
        Submodule.prodEquivOfIsCompl _ _ hcompl
      have h1 : Module.rankAtStalk (R := A) (LinearMap.range s × K)
          = Module.rankAtStalk (A ⊗[R] (Fin n → R)) := by
        ext p
        rw [Module.rankAtStalk_eq_of_equiv e3]
      rw [Module.rankAtStalk_prod] at h1
      have h2 : Module.rankAtStalk (R := A) (LinearMap.range s)
          = Module.rankAtStalk (A ⊗[R] M) := by
        ext p
        rw [Module.rankAtStalk_eq_of_equiv (LinearEquiv.ofInjective s hsinj).symm]
      have h3 : Module.rankAtStalk (A ⊗[R] (Fin n → R))
          = Module.rankAtStalk (R := A) (Fin n → A) := by
        ext p
        rw [Module.rankAtStalk_eq_of_equiv
          (Algebra.TensorProduct.piScalarRight R A A (Fin n)).toLinearEquiv]
      funext p
      have h4 := congrFun h1 p
      have h5 := congrFun h2 p
      have h3p := congrFun h3 p
      haveI : Nontrivial A := ⟨0, 1, fun h01 =>
        (Ideal.ne_top_iff_one _).mp p.2.ne_top (h01 ▸ p.asIdeal.zero_mem)⟩
      have h6 : Module.rankAtStalk (R := A) (Fin n → A) p = n := by
        rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fin_fun]
        rfl
      simp only [Pi.add_apply] at h4
      rw [h5, hrank p, h3p, h6] at h4
      simp only [Pi.zero_apply]
      omega
    -- hence `K = ⊥`, so the base-changed matrix vanishes, giving the entries
    have hKbot : K = ⊥ := by
      have := Module.rankAtStalk_eq_zero_iff_subsingleton.mp hKrank
      exact Submodule.eq_bot_of_subsingleton
    have hα0 : α.baseChange A = 0 := by
      have hle : LinearMap.range (α.baseChange A) ≤ K := by
        rw [hK, LinearMap.exact_iff.mp hexA]
      rw [hKbot, le_bot_iff, LinearMap.range_eq_bot] at hle
      exact hle
    intro i j
    have h7 : (α.baseChange A) (1 ⊗ₜ[R] Pi.single i 1) = 0 := by rw [hα0]; rfl
    rw [LinearMap.baseChange_tmul] at h7
    have h8 := congrArg
      (Algebra.TensorProduct.piScalarRight R A A (Fin n)).toLinearEquiv h7
    rw [map_zero] at h8
    have h9 : (Algebra.TensorProduct.piScalarRight R A A (Fin n)).toLinearEquiv
        ((1 : A) ⊗ₜ[R] (α (Pi.single i 1))) = fun j => α (Pi.single i 1) j • (1 : A) := rfl
    rw [h9] at h8
    have h10 := congrFun h8 j
    rwa [Algebra.smul_def, mul_one] at h10
  · -- entries die ⟹ `A ⊗ M ≅ Aⁿ`
    intro hent
    -- the base-changed matrix vanishes
    have hα0 : α.baseChange A = 0 := by
      apply LinearMap.restrictScalars_injective R
      apply TensorProduct.ext'
      intro a v
      simp only [LinearMap.coe_restrictScalars, LinearMap.baseChange_tmul,
        LinearMap.zero_apply]
      have hv : α v = ∑ i : Fin m, v i • α (Pi.single i 1) := by
        have hsingle : ∀ i : Fin m, (fun j => if i = j then (1 : R) else 0)
            = Pi.single i 1 := fun i => by
          funext j
          simp [Pi.single_apply, eq_comm]
        conv_lhs => rw [pi_eq_sum_univ v, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hsingle i]
      rw [hv, TensorProduct.tmul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [TensorProduct.tmul_smul]
      suffices h : a ⊗ₜ[R] (α (Pi.single i 1)) = (0 : A ⊗[R] (Fin n → R)) by
        rw [h, smul_zero]
      apply (Algebra.TensorProduct.piScalarRight R A A (Fin n)).toLinearEquiv.injective
      rw [map_zero]
      have hrfl : (Algebra.TensorProduct.piScalarRight R A A (Fin n)).toLinearEquiv
          (a ⊗ₜ[R] (α (Pi.single i 1))) = fun j => α (Pi.single i 1) j • a := rfl
      rw [hrfl]
      funext j
      rw [Algebra.smul_def, hent i j, zero_mul]
      rfl
    -- hence the base-changed surjection is an isomorphism onto `A ⊗ M`
    have hker : LinearMap.ker (π.baseChange A) = ⊥ := by
      rw [LinearMap.exact_iff.mp hexA, hα0, LinearMap.range_zero]
    let e1 : (A ⊗[R] (Fin n → R)) ≃ₗ[A] A ⊗[R] M :=
      LinearEquiv.ofBijective (π.baseChange A) ⟨LinearMap.ker_eq_bot.mp hker, hsurjA⟩
    let e2 : (Fin n → A) ≃ₗ[A] A ⊗[R] M :=
      (Algebra.TensorProduct.piScalarRight R A A (Fin n)).toLinearEquiv.symm.trans e1
    constructor
    · exact Module.Flat.of_linearEquiv e2.symm
    · intro p
      haveI : Nontrivial A := ⟨0, 1, fun h01 =>
        (Ideal.ne_top_iff_one _).mp p.2.ne_top (h01 ▸ p.asIdeal.zero_mem)⟩
      rw [Module.rankAtStalk_eq_of_equiv e2.symm, Module.rankAtStalk_eq_finrank_of_free,
        Module.finrank_fin_fun]
      rfl

/-- **[L1-d0, cancel-base-change stability]** The rank-`n` local-freeness condition read
through an intermediate algebra `R'` agrees with the condition over `R` (the
`B ⊗[R'] (R' ⊗[R] M) ≅ B ⊗[R] M` cancellation, transporting flatness and stalk ranks). -/
private theorem locallyFreeRankLocusAux_cond_cancel {R R' B : Type u} [CommRing R]
    [CommRing R'] [CommRing B] [Algebra R R'] [Algebra R' B] [Algebra R B]
    [IsScalarTower R R' B] {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ} :
    (Module.Flat B (B ⊗[R'] (R' ⊗[R] M)) ∧
        ∀ p : PrimeSpectrum B, Module.rankAtStalk (B ⊗[R'] (R' ⊗[R] M)) p = n) ↔
      (Module.Flat B (B ⊗[R] M) ∧
        ∀ p : PrimeSpectrum B, Module.rankAtStalk (B ⊗[R] M) p = n) := by
  have e : (B ⊗[R'] (R' ⊗[R] M)) ≃ₗ[B] B ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R R' B B M
  constructor
  · rintro ⟨h1, h2⟩
    haveI := h1
    exact ⟨Module.Flat.of_linearEquiv e.symm, fun p => by
      rw [Module.rankAtStalk_eq_of_equiv e.symm]
      exact h2 p⟩
  · rintro ⟨h1, h2⟩
    haveI := h1
    exact ⟨Module.Flat.of_linearEquiv e, fun p => by
      rw [Module.rankAtStalk_eq_of_equiv e]
      exact h2 p⟩

/-- **[L1-d1, the patch interface]** Over a patch ring `R'` carrying an `n`-generator
presentation of `R' ⊗ M`, the rank-`n` condition for any `R'`-algebra `B` is the vanishing
in `B` of the entries ideal of the presentation ([L1-b] + [L1-d0]). -/
private theorem locallyFreeRankLocusAux_patch_iff {R R' B : Type u} [CommRing R]
    [CommRing R'] [CommRing B] [Algebra R R'] [Algebra R' B] [Algebra R B]
    [IsScalarTower R R' B] {M : Type u} [AddCommGroup M] [Module R M] {n m : ℕ}
    (α : (Fin m → R') →ₗ[R'] (Fin n → R'))
    (π : (Fin n → R') →ₗ[R'] (R' ⊗[R] M)) (hπ : Function.Surjective π)
    (hexact : Function.Exact α π) :
    (Module.Flat B (B ⊗[R] M) ∧
        ∀ p : PrimeSpectrum B, Module.rankAtStalk (B ⊗[R] M) p = n) ↔
      (Ideal.span (Set.range fun ij : Fin m × Fin n =>
        α (Pi.single ij.1 1) ij.2)).map (algebraMap R' B) = ⊥ := by
  rw [← locallyFreeRankLocusAux_cond_cancel (R := R) (R' := R'),
    locallyFreeRankLocusAux_core_iff α π hπ hexact, Ideal.map_span, Submodule.span_eq_bot]
  constructor
  · rintro h _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩
    exact h i j
  · intro h i j
    exact h _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩

/-- **[L1-c, uniqueness of the universal vanishing ideal]** Two ideals that die in exactly
the same `R`-algebras are equal (test on `R/I` and `R/J`). This glues the locally-chosen
presentation ideals into the canonical ideal sheaf (`map_ideal_basicOpen` holds because
both sides represent the same functor over the localized algebras). -/
private theorem locallyFreeRankLocusAux_unique {R : Type u} [CommRing R] {I J : Ideal R}
    (h : ∀ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      I.map (algebraMap R A) = ⊥ ↔ J.map (algebraMap R A) = ⊥) : I = J := by
  have key : ∀ (I' J' : Ideal R), (∀ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      I'.map (algebraMap R A) = ⊥ ↔ J'.map (algebraMap R A) = ⊥) → J' ≤ I' := by
    intro I' J' h'
    have h1 : I'.map (algebraMap R (R ⧸ I')) = ⊥ := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.map_quotient_self]
    have h2 := (h' (R ⧸ I') inferInstance inferInstance).mp h1
    rwa [Ideal.Quotient.algebraMap_eq, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h2
  exact le_antisymm (key J I fun A cA aA => (h A cA aA).symm) (key I J h)

/-- **[L1-d2, away-clearing]** Membership in the extension of an ideal along
`R' → R'[1/b]` is, up to a power of `b`, membership in the ideal itself. -/
private theorem locallyFreeRankLocusAux_away_clear {R' : Type u} [CommRing R']
    (J : Ideal R') (b : R') {y : R'}
    (hy : algebraMap R' (Localization.Away b) y
      ∈ J.map (algebraMap R' (Localization.Away b))) :
    ∃ k : ℕ, b ^ k * y ∈ J := by
  obtain ⟨⟨⟨j, hj⟩, s⟩, hjs⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers b) _).mp hy
  obtain ⟨k, hk⟩ := s.2
  rw [← hk, ← map_mul, ← sub_eq_zero, ← map_sub] at hjs
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers b) _ _).mp hjs
  obtain ⟨k', hk'⟩ := c.2
  rw [← hk'] at hc
  refine ⟨k' + k, ?_⟩
  have hbky : b ^ (k' + k) * y = b ^ k' * j := by linear_combination hc
  rw [hbky]
  exact J.mul_mem_left _ hj

/-- **[L1-d3, overlap agreement]** Two patch rings mapping to a common further algebra `S`
cut out the same extended entries ideal: both extensions represent the same condition over
`S`-algebras ([L1-d1]), so they agree by uniqueness ([L1-c]). -/
private theorem locallyFreeRankLocusAux_agree {R R₁ R₂ S : Type u} [CommRing R]
    [CommRing R₁] [CommRing R₂] [CommRing S] [Algebra R R₁] [Algebra R R₂] [Algebra R₁ S]
    [Algebra R₂ S] [Algebra R S] [IsScalarTower R R₁ S] [IsScalarTower R R₂ S]
    {M : Type u} [AddCommGroup M] [Module R M] {n m₁ m₂ : ℕ}
    (α₁ : (Fin m₁ → R₁) →ₗ[R₁] (Fin n → R₁))
    (π₁ : (Fin n → R₁) →ₗ[R₁] (R₁ ⊗[R] M)) (hπ₁ : Function.Surjective π₁)
    (hex₁ : Function.Exact α₁ π₁)
    (α₂ : (Fin m₂ → R₂) →ₗ[R₂] (Fin n → R₂))
    (π₂ : (Fin n → R₂) →ₗ[R₂] (R₂ ⊗[R] M)) (hπ₂ : Function.Surjective π₂)
    (hex₂ : Function.Exact α₂ π₂) :
    (Ideal.span (Set.range fun ij : Fin m₁ × Fin n =>
        α₁ (Pi.single ij.1 1) ij.2)).map (algebraMap R₁ S)
      = (Ideal.span (Set.range fun ij : Fin m₂ × Fin n =>
        α₂ (Pi.single ij.1 1) ij.2)).map (algebraMap R₂ S) := by
  refine locallyFreeRankLocusAux_unique fun B cB aB => ?_
  letI : Algebra R₁ B := ((algebraMap S B).comp (algebraMap R₁ S)).toAlgebra
  letI : Algebra R₂ B := ((algebraMap S B).comp (algebraMap R₂ S)).toAlgebra
  letI : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R R₁ B := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R R₁ S])
  haveI : IsScalarTower R R₂ B := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R R₂ S])
  rw [Ideal.map_map, Ideal.map_map,
    show (algebraMap S B).comp (algebraMap R₁ S) = algebraMap R₁ B from
      (RingHom.algebraMap_toAlgebra _).symm,
    show (algebraMap S B).comp (algebraMap R₂ S) = algebraMap R₂ B from
      (RingHom.algebraMap_toAlgebra _).symm,
    ← locallyFreeRankLocusAux_patch_iff α₁ π₁ hπ₁ hex₁,
    ← locallyFreeRankLocusAux_patch_iff α₂ π₂ hπ₂ hex₂]

/-- **[L1-d, the affine universal ideal]** Over an affine base, the "finite locally free of
rank `n`" condition on base changes of `M` is cut out by a single ideal: combining the local
`n`-generator presentations ([L1-a], on a finite basic-open cover extracted by
quasi-compactness), the entries-ideal characterisation over each patch ([L1-b]), and the
quasi-coherent gluing of the patch ideals (agreement on overlaps by uniqueness [L1-c]).
This is the affine heart of KM 6.4.3's flattening locus. -/
private theorem locallyFreeRankLocusAux_exists_ideal {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] {n : ℕ}
    (hb : ∀ (K : Type u) (_ : Field K) (_ : Algebra R K),
      Module.finrank K (K ⊗[R] M) ≤ n) :
    ∃ I : Ideal R, ∀ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      (Module.Flat A (A ⊗[R] M) ∧
          ∀ p : PrimeSpectrum A, Module.rankAtStalk (A ⊗[R] M) p = n) ↔
        I.map (algebraMap R A) = ⊥ := by
  classical
  -- per-prime local `n`-generator presentations ([L1-a])
  choose gfun hgp mfun αfun πfun hπsurj hexact using
    fun p : PrimeSpectrum R => locallyFreeRankLocusAux_exists_presentation hb p
  -- the chosen `g`s generate the unit ideal
  have hunit : Ideal.span (Set.range gfun) = ⊤ := by
    by_contra h
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
    exact hgp ⟨P, hP.isPrime⟩ (hle (Ideal.subset_span ⟨⟨P, hP.isPrime⟩, rfl⟩))
  -- a finite subfamily already generates the unit ideal
  obtain ⟨T, hT, h1T⟩ := Submodule.mem_span_finite_of_mem_span
    (hunit ▸ Submodule.mem_top : (1 : R) ∈ Ideal.span (Set.range gfun))
  choose pf hpf using fun t : T => hT t.2
  -- the per-patch entries ideals and their common refinement
  let J : (p : PrimeSpectrum R) → Ideal (Localization.Away (gfun p)) := fun p =>
    Ideal.span (Set.range fun ij : Fin (mfun p) × Fin n =>
      (αfun p) (Pi.single ij.1 1) ij.2)
  refine ⟨⨅ t : T, (J (pf t)).comap (algebraMap R (Localization.Away (gfun (pf t)))),
    fun A cA aA => ⟨fun hP => ?_, fun hI => ?_⟩⟩
  · -- the condition kills the glued ideal
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro r hr
    rw [RingHom.mem_ker]
    -- for each patch, the image of `r` in `A` dies after inverting `b t := algebraMap (g t)`
    have hloc : ∀ t : T, ∃ k : ℕ,
        algebraMap R A (gfun (pf t)) ^ k * algebraMap R A r = 0 := by
      intro t
      set g := gfun (pf t) with hg
      set b := algebraMap R A g with hb
      letI algRg : Algebra (Localization.Away g) (Localization.Away b) :=
        (Localization.awayMap (algebraMap R A) g).toAlgebra
      haveI : IsScalarTower R (Localization.Away g) (Localization.Away b) := by
        refine IsScalarTower.of_algebraMap_eq' ?_
        rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq R A
          (Localization.Away b)]
        exact (IsLocalization.map_comp _).symm
      -- the condition localizes from `A` to `A_t`
      obtain ⟨hflat, hrank⟩ := hP
      haveI := hflat
      have e : (Localization.Away b) ⊗[R] M ≃ₗ[Localization.Away b]
          (Localization.Away b) ⊗[A] (A ⊗[R] M) :=
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R A
          (Localization.Away b) (Localization.Away b) M).symm
      have hPt : Module.Flat (Localization.Away b) ((Localization.Away b) ⊗[R] M) ∧
          ∀ q : PrimeSpectrum (Localization.Away b),
            Module.rankAtStalk ((Localization.Away b) ⊗[R] M) q = n := by
        refine ⟨Module.Flat.of_linearEquiv e, fun q => ?_⟩
        rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_baseChange]
        exact hrank _
      -- hence the entries ideal dies over `A_t`, so `r`'s image there is `0`
      have hJt := (locallyFreeRankLocusAux_patch_iff (αfun (pf t)) (πfun (pf t))
        (hπsurj (pf t)) (hexact (pf t))).mp hPt
      have hr_t : algebraMap R (Localization.Away g) r ∈ J (pf t) :=
        Ideal.mem_comap.mp ((Submodule.mem_iInf _).mp hr t)
      have hzero : algebraMap A (Localization.Away b) (algebraMap R A r) = 0 := by
        rw [← IsScalarTower.algebraMap_apply R A (Localization.Away b),
          IsScalarTower.algebraMap_apply R (Localization.Away g) (Localization.Away b),
          ← Ideal.mem_bot, ← hJt]
        exact Ideal.mem_map_of_mem _ hr_t
      obtain ⟨⟨s, hs⟩, hsk⟩ :=
        (IsLocalization.map_eq_zero_iff (Submonoid.powers b) _ _).mp hzero
      obtain ⟨k, rfl⟩ := hs
      exact ⟨k, hsk⟩
    choose kfun hkfun using hloc
    -- a single power `K` works for every patch
    set K := Finset.univ.sup kfun with hK
    have hbig : ∀ t : T, algebraMap R A (gfun (pf t)) ^ K * algebraMap R A r = 0 := by
      intro t
      have hle : kfun t ≤ K := Finset.le_sup (Finset.mem_univ t)
      calc algebraMap R A (gfun (pf t)) ^ K * algebraMap R A r
          = algebraMap R A (gfun (pf t)) ^ (K - kfun t) *
              (algebraMap R A (gfun (pf t)) ^ kfun t * algebraMap R A r) := by
            rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
        _ = 0 := by rw [hkfun t, mul_zero]
    -- the images of the finite subcover still generate the unit ideal in `A`
    have hTA : Ideal.span ((algebraMap R A) '' ↑T) = ⊤ := by
      refine (Ideal.eq_top_iff_one _).mpr ?_
      have h1' : (1 : A) ∈ Ideal.map (algebraMap R A) (Ideal.span (↑T : Set R)) := by
        simpa using Ideal.mem_map_of_mem (algebraMap R A) h1T
      rwa [Ideal.map_span] at h1'
    -- conclude by the annihilator-ideal trick with the `K`-th powers
    have hpow := Ideal.span_pow_eq_top _ hTA K
    have hann : Ideal.span ((fun x => x ^ K) '' ((algebraMap R A) '' ↑T)) ≤
        LinearMap.ker (LinearMap.toSpanSingleton A A (algebraMap R A r)) := by
      rw [Ideal.span_le]
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨t', ht'⟩ := hT hy
      have hyt : y = gfun (pf ⟨y, hy⟩) := (hpf ⟨y, hy⟩).symm ▸ rfl
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
        smul_eq_mul, hyt]
      exact hbig ⟨y, hy⟩
    have h1ann : (1 : A) ∈ LinearMap.ker (LinearMap.toSpanSingleton A A
        (algebraMap R A r)) := hann (hpow ▸ Submodule.mem_top)
    simpa [LinearMap.toSpanSingleton_apply] using h1ann
  · -- the glued ideal's vanishing forces the condition
    have hIle : ∀ r ∈ (⨅ t : T, (J (pf t)).comap
        (algebraMap R (Localization.Away (gfun (pf t))))), algebraMap R A r = 0 := by
      intro r hr
      have h1 := Ideal.mem_map_of_mem (algebraMap R A) hr
      rw [hI] at h1
      exact Ideal.mem_bot.mp h1
    -- Step 1: each patch ideal dies after inverting the image of its `g` (saturation)
    have hJA : ∀ t : T, (J (pf t)).map
        (Localization.awayMap (algebraMap R A) (gfun (pf t))) = ⊥ := by
      intro t
      show (Ideal.span _).map _ = ⊥
      rw [Ideal.map_span, Submodule.span_eq_bot]
      rintro _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩
      set g := gfun (pf t) with hgdef
      set e := (αfun (pf t)) (Pi.single i 1) j with hedef
      have he : e ∈ J (pf t) := Ideal.subset_span ⟨⟨i, j⟩, rfl⟩
      -- clear the denominator of `e`
      obtain ⟨⟨r₀, s⟩, hr₀⟩ := IsLocalization.surj (Submonoid.powers g) e
      obtain ⟨k, hk⟩ := s.2
      -- a power of `g` pushes `r₀` into every patch ideal
      have hq : ∀ q : T, ∃ kq : ℕ, algebraMap R (Localization.Away (gfun (pf q)))
          (g ^ kq * r₀) ∈ J (pf q) := by
        intro q
        set gq := gfun (pf q) with hgq
        set S' := Localization.Away (algebraMap R (Localization.Away gq) g) with hS'
        letI : Algebra (Localization.Away g) S' :=
          (Localization.awayMap (algebraMap R (Localization.Away gq)) g).toAlgebra
        haveI : IsScalarTower R (Localization.Away g) S' := by
          refine IsScalarTower.of_algebraMap_eq' ?_
          rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq R
            (Localization.Away gq) S']
          exact (IsLocalization.map_comp _).symm
        have hagree := locallyFreeRankLocusAux_agree (R := R) (S := S')
          (αfun (pf t)) (πfun (pf t)) (hπsurj (pf t)) (hexact (pf t))
          (αfun (pf q)) (πfun (pf q)) (hπsurj (pf q)) (hexact (pf q))
        have hmem : algebraMap (Localization.Away gq) S'
            (algebraMap R (Localization.Away gq) r₀)
            ∈ (J (pf q)).map (algebraMap (Localization.Away gq) S') := by
          rw [← hagree]
          have h1 : algebraMap (Localization.Away gq) S'
              (algebraMap R (Localization.Away gq) r₀)
              = algebraMap (Localization.Away g) S'
                (algebraMap R (Localization.Away g) r₀) := by
            rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
          rw [h1, ← hr₀, map_mul]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ he)
        obtain ⟨kq, hkq⟩ := locallyFreeRankLocusAux_away_clear _ _ hmem
        refine ⟨kq, ?_⟩
        rwa [map_mul, map_pow]
      choose kq hkq using hq
      set K' := Finset.univ.sup kq with hK'
      -- `g^K' * r₀` lies in the glued ideal, hence dies in `A`
      have hrI : algebraMap R A (g ^ K' * r₀) = 0 := by
        refine hIle _ ((Submodule.mem_iInf _).mpr fun q => Ideal.mem_comap.mpr ?_)
        have hsplit : g ^ K' * r₀ = g ^ (K' - kq q) * (g ^ kq q * r₀) := by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ q))]
        rw [hsplit, map_mul]
        exact Ideal.mul_mem_left _ _ (hkq q)
      -- transport to `A[1/b]` and cancel the invertible powers of `g`
      have h0 : Localization.awayMap (algebraMap R A) g
          (algebraMap R (Localization.Away g) (g ^ K' * r₀)) = 0 := by
        rw [← RingHom.comp_apply,
          show (Localization.awayMap (algebraMap R A) g).comp
              (algebraMap R (Localization.Away g))
            = (algebraMap A (Localization.Away (algebraMap R A g))).comp (algebraMap R A)
            from IsLocalization.map_comp _,
          RingHom.comp_apply, hrI, map_zero]
      have hexp : algebraMap R (Localization.Away g) (g ^ K' * r₀)
          = algebraMap R (Localization.Away g) g ^ (K' + k) * e := by
        have hs' : algebraMap R (Localization.Away g) (g ^ k)
            = algebraMap R (Localization.Away g) ↑s := by rw [← hk]
        calc algebraMap R (Localization.Away g) (g ^ K' * r₀)
            = algebraMap R (Localization.Away g) (g ^ K')
                * algebraMap R (Localization.Away g) r₀ := map_mul _ _ _
          _ = algebraMap R (Localization.Away g) (g ^ K')
                * (e * algebraMap R (Localization.Away g) ↑s) := by rw [← hr₀]
          _ = algebraMap R (Localization.Away g) (g ^ K')
                * (e * algebraMap R (Localization.Away g) (g ^ k)) := by rw [hs']
          _ = algebraMap R (Localization.Away g) g ^ (K' + k) * e := by
              rw [map_pow, map_pow, pow_add]
              ring
      rw [hexp, map_mul, map_pow] at h0
      have hu : IsUnit (Localization.awayMap (algebraMap R A) g
          (algebraMap R (Localization.Away g) g)) := by
        rw [← RingHom.comp_apply,
          show (Localization.awayMap (algebraMap R A) g).comp
              (algebraMap R (Localization.Away g))
            = (algebraMap A (Localization.Away (algebraMap R A g))).comp (algebraMap R A)
            from IsLocalization.map_comp _,
          RingHom.comp_apply]
        exact IsLocalization.map_units _ ⟨algebraMap R A g, Submonoid.mem_powers _⟩
      rwa [(hu.pow (K' + k)).mul_right_eq_zero] at h0
    -- Step 2: the condition holds over each `A[1/b t]` (patch interface + step 1)
    have hPt : ∀ t : T,
        Module.Flat (Localization.Away (algebraMap R A (gfun (pf t))))
          ((Localization.Away (algebraMap R A (gfun (pf t)))) ⊗[R] M) ∧
        ∀ q : PrimeSpectrum (Localization.Away (algebraMap R A (gfun (pf t)))),
          Module.rankAtStalk
            ((Localization.Away (algebraMap R A (gfun (pf t)))) ⊗[R] M) q = n := by
      intro t
      set g := gfun (pf t) with hgdef
      set b := algebraMap R A g with hbdef
      letI : Algebra (Localization.Away g) (Localization.Away b) :=
        (Localization.awayMap (algebraMap R A) g).toAlgebra
      haveI : IsScalarTower R (Localization.Away g) (Localization.Away b) := by
        refine IsScalarTower.of_algebraMap_eq' ?_
        rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq R A
          (Localization.Away b)]
        exact (IsLocalization.map_comp _).symm
      refine (locallyFreeRankLocusAux_patch_iff (αfun (pf t)) (πfun (pf t))
        (hπsurj (pf t)) (hexact (pf t))).mpr ?_
      show (J (pf t)).map _ = ⊥
      rw [RingHom.algebraMap_toAlgebra]
      exact hJA t
    -- the images of the subcover generate the unit ideal of `A`
    have hTA : Ideal.span (Set.range fun t : T => algebraMap R A (gfun (pf t))) = ⊤ := by
      have h1' : (1 : A) ∈ Ideal.map (algebraMap R A) (Ideal.span (↑T : Set R)) := by
        simpa using Ideal.mem_map_of_mem (algebraMap R A) h1T
      rw [Ideal.map_span] at h1'
      have hset : (algebraMap R A) '' ↑T
          = Set.range fun t : T => algebraMap R A (gfun (pf t)) := by
        ext x
        simp only [Set.mem_image, Set.mem_range]
        constructor
        · rintro ⟨y, hy, rfl⟩
          refine ⟨⟨y, hy⟩, ?_⟩
          show algebraMap R A (gfun (pf ⟨y, hy⟩)) = algebraMap R A y
          rw [hpf ⟨y, hy⟩]
        · rintro ⟨t, rfl⟩
          refine ⟨gfun (pf t), ?_, rfl⟩
          rw [hpf t]
          exact t.2
      rw [hset] at h1'
      exact (Ideal.eq_top_iff_one _).mpr h1'
    -- Step 3a: flatness glues over the cover
    haveI hflatA : Module.Flat A (A ⊗[R] M) := by
      refine Module.flat_of_localized_span A (A ⊗[R] M) _ hTA ?_
      intro r
      obtain ⟨t, ht⟩ := r.2
      rw [← ht]
      set b := algebraMap R A (gfun (pf t)) with hbdef
      haveI hf1 : Module.Flat (Localization.Away b) ((Localization.Away b) ⊗[R] M) :=
        (hPt t).1
      haveI : Module.Flat (Localization.Away b)
          ((Localization.Away b) ⊗[A] (A ⊗[R] M)) :=
        Module.Flat.of_linearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange
          R A (Localization.Away b) (Localization.Away b) M)
      haveI : Module.Flat A (Localization.Away b) :=
        IsLocalization.flat _ (Submonoid.powers b)
      haveI : Module.Flat A ((Localization.Away b) ⊗[A] (A ⊗[R] M)) :=
        Module.Flat.trans A (Localization.Away b) _
      exact Module.Flat.of_linearEquiv
        ((LocalizedModule.equivTensorProduct (Submonoid.powers b)
          (A ⊗[R] M)).restrictScalars A)
    refine ⟨hflatA, fun q => ?_⟩
    -- Step 3b: the rank at any prime is computed on a patch containing it
    have hexists : ∃ t : T, algebraMap R A (gfun (pf t)) ∉ q.asIdeal := by
      by_contra h
      push_neg at h
      have hle : Ideal.span (Set.range fun t : T => algebraMap R A (gfun (pf t)))
          ≤ q.asIdeal := Ideal.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact h t)
      rw [hTA] at hle
      exact q.2.ne_top (top_le_iff.mp hle)
    obtain ⟨t, hqt⟩ := hexists
    set b := algebraMap R A (gfun (pf t)) with hbdef
    have hrange : q ∈ Set.range (PrimeSpectrum.comap
        (algebraMap A (Localization.Away b))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b]
      exact hqt
    obtain ⟨q', hq'⟩ := hrange
    have hbase := Module.rankAtStalk_baseChange (R := A) (M := A ⊗[R] M)
      (S := Localization.Away b) q'
    rw [hq'] at hbase
    rw [← hbase, Module.rankAtStalk_eq_of_equiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A (Localization.Away b)
        (Localization.Away b) M)]
    exact (hPt t).2 q'

end LocallyFreeRankLocusAux

section LocallyFreeRankLocusSheaf

open scoped TensorProduct

variable {W : Scheme.{u}} (f : W ⟶ S) [IsFinite f] [LocallyOfFinitePresentation f]

/-- The pushforward section module of a finite lfp morphism over an affine open is a
finitely presented module (the [L1-e] instance package, following the `vanishingLocus`
pattern). -/
private theorem locallyFreeRankLocusSheaf_fp (U : S.affineOpens) :
    letI := ((f.app U.1).hom).toAlgebra
    Module.FinitePresentation Γ(S, U.1) Γ(W, f ⁻¹ᵁ U.1) := by
  letI := ((f.app U.1).hom).toAlgebra
  haveI : Module.Finite Γ(S, U.1) Γ(W, f ⁻¹ᵁ U.1) := f.finite_app U.1 U.2
  haveI hfp : RingHom.FinitePresentation (f.appLE U.1 (f ⁻¹ᵁ U.1) le_rfl).hom :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation f ‹_› U
      ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩ le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at hfp
  haveI : Algebra.FinitePresentation Γ(S, U.1) Γ(W, f ⁻¹ᵁ U.1) := hfp
  exact Module.FinitePresentation.of_finite_of_finitePresentation _ _

/-- **[L1-e1]** The flattening ideal sheaf of KM 6.4.3: on each affine open it is the
affine universal ideal ([L1-d]) of the pushforward module. `map_ideal_basicOpen` holds
because both sides carry the same universal property ([L1-c] uniqueness). -/
private noncomputable def locallyFreeRankLocusSheaf (n : ℕ)
    (hb : ∀ (U : S.affineOpens) (K : Type u) (_ : Field K)
      (_ : Algebra Γ(S, U.1) K),
      letI := ((f.app U.1).hom).toAlgebra
      Module.finrank K (K ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) ≤ n) : S.IdealSheafData where
  ideal U :=
    letI := ((f.app U.1).hom).toAlgebra
    haveI := locallyFreeRankLocusSheaf_fp f U
    (locallyFreeRankLocusAux_exists_ideal (M := Γ(W, f ⁻¹ᵁ U.1)) (n := n) (hb U)).choose
  map_ideal_basicOpen U g := by
    classical
    -- instance battery (verbatim `vanishingLocus` pattern, all in `basicOpen` spelling)
    letI := ((f.app U.1).hom).toAlgebra
    letI := ((f.app (S.basicOpen g)).hom).toAlgebra
    letI := ((S.presheaf.map (homOfLE <| S.basicOpen_le g).op).hom).toAlgebra
    letI := ((W.presheaf.map (homOfLE
      (show f ⁻¹ᵁ S.basicOpen g ≤ f ⁻¹ᵁ U.1 from
        fun _ hx => S.basicOpen_le g hx)).op).hom).toAlgebra
    letI := ((f.appLE U.1 (f ⁻¹ᵁ S.basicOpen g)
      (show f ⁻¹ᵁ S.basicOpen g ≤ f ⁻¹ᵁ U.1 from
        fun _ hx => S.basicOpen_le g hx)).hom).toAlgebra
    haveI : IsScalarTower Γ(S, U.1) Γ(S, S.basicOpen g) Γ(W, f ⁻¹ᵁ S.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' (by
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
          RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]
        simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map])
    haveI : IsScalarTower Γ(S, U.1) Γ(W, f ⁻¹ᵁ U.1) Γ(W, f ⁻¹ᵁ S.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' (by
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
          RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]
        simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map])
    haveI := locallyFreeRankLocusSheaf_fp f U
    -- the `.1`-spelled givens at the basic open, re-keyed by defeq ascription
    haveI hfpV : letI := ((f.app (S.basicOpen g)).hom).toAlgebra
        Module.FinitePresentation Γ(S, S.basicOpen g) Γ(W, f ⁻¹ᵁ S.basicOpen g) :=
      locallyFreeRankLocusSheaf_fp f (S.affineBasicOpen g)
    have hbV : ∀ (K : Type u) (_ : Field K) (_ : Algebra Γ(S, S.basicOpen g) K),
        letI := ((f.app (S.basicOpen g)).hom).toAlgebra
        Module.finrank K (K ⊗[Γ(S, S.basicOpen g)] Γ(W, f ⁻¹ᵁ S.basicOpen g)) ≤ n :=
      hb (S.affineBasicOpen g)
    -- quasi-coherence: the pushforward sections localize
    haveI hSloc : IsLocalization.Away g Γ(S, S.basicOpen g) :=
      U.2.isLocalization_basicOpen g
    haveI hWloc := (U.2.preimage f).isLocalization_of_eq_basicOpen
      (algebraMap Γ(S, U.1) Γ(W, f ⁻¹ᵁ U.1) g)
      (homOfLE (show f ⁻¹ᵁ S.basicOpen g ≤ f ⁻¹ᵁ U.1 from
        fun _ hx => S.basicOpen_le g hx))
      (by rw [Scheme.preimage_basicOpen, RingHom.algebraMap_toAlgebra])
    haveI : IsLocalizedModule (Submonoid.powers g)
        (IsScalarTower.toAlgHom Γ(S, U.1) Γ(W, f ⁻¹ᵁ U.1)
          Γ(W, f ⁻¹ᵁ S.basicOpen g)).toLinearMap := by
      haveI : IsLocalization (Algebra.algebraMapSubmonoid (R := Γ(S, U.1))
          Γ(W, f ⁻¹ᵁ U.1) (Submonoid.powers g)) Γ(W, f ⁻¹ᵁ S.basicOpen g) := by
        rw [show Algebra.algebraMapSubmonoid (R := Γ(S, U.1)) Γ(W, f ⁻¹ᵁ U.1)
            (Submonoid.powers g) = Submonoid.powers
              (algebraMap Γ(S, U.1) Γ(W, f ⁻¹ᵁ U.1) g) from
          Submonoid.map_powers _ g]
        exact hWloc
      infer_instance
    have ebc := (IsLocalizedModule.isBaseChange (Submonoid.powers g)
      Γ(S, S.basicOpen g)
      (IsScalarTower.toAlgHom Γ(S, U.1) Γ(W, f ⁻¹ᵁ U.1)
        Γ(W, f ⁻¹ᵁ S.basicOpen g)).toLinearMap).equiv
    -- both sides are the universal ideal over `Γ(S, bo g)`: equal by uniqueness [L1-c]
    show Ideal.map _ ((locallyFreeRankLocusAux_exists_ideal
      (M := Γ(W, f ⁻¹ᵁ U.1)) (n := n) (hb U)).choose)
      = (locallyFreeRankLocusAux_exists_ideal
        (M := Γ(W, f ⁻¹ᵁ S.basicOpen g)) (n := n) hbV).choose
    refine locallyFreeRankLocusAux_unique fun B cB aB => ?_
    letI : Algebra Γ(S, U.1) B := ((algebraMap Γ(S, S.basicOpen g) B).comp
      (algebraMap Γ(S, U.1) Γ(S, S.basicOpen g))).toAlgebra
    haveI : IsScalarTower Γ(S, U.1) Γ(S, S.basicOpen g) B :=
      IsScalarTower.of_algebraMap_eq' (by rw [RingHom.algebraMap_toAlgebra])
    have etrans : (B ⊗[Γ(S, S.basicOpen g)] Γ(W, f ⁻¹ᵁ S.basicOpen g))
        ≃ₗ[B] B ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1) :=
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
        ebc.symm).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(S, U.1)
          Γ(S, S.basicOpen g) B B Γ(W, f ⁻¹ᵁ U.1))
    have hL : (Ideal.map (CommRingCat.Hom.hom (S.presheaf.map (homOfLE
          (S.basicOpen_le g)).op))
          ((locallyFreeRankLocusAux_exists_ideal
            (M := Γ(W, f ⁻¹ᵁ U.1)) (n := n) (hb U)).choose)).map (algebraMap _ B) = ⊥
        ↔ ((locallyFreeRankLocusAux_exists_ideal
            (M := Γ(W, f ⁻¹ᵁ U.1)) (n := n) (hb U)).choose).map
            (algebraMap Γ(S, U.1) B) = ⊥ := by
      rw [Ideal.map_map]
      constructor
      · intro h
        rwa [show (algebraMap Γ(S, S.basicOpen g) B).comp
          (CommRingCat.Hom.hom (S.presheaf.map (homOfLE (S.basicOpen_le g)).op))
          = algebraMap Γ(S, U.1) B from rfl] at h
      · intro h
        rwa [show (algebraMap Γ(S, S.basicOpen g) B).comp
          (CommRingCat.Hom.hom (S.presheaf.map (homOfLE (S.basicOpen_le g)).op))
          = algebraMap Γ(S, U.1) B from rfl]
    refine hL.trans (Iff.trans ((locallyFreeRankLocusAux_exists_ideal
        (M := Γ(W, f ⁻¹ᵁ U.1)) (n := n) (hb U)).choose_spec B cB
          inferInstance).symm
      (Iff.trans ?_ ((locallyFreeRankLocusAux_exists_ideal
        (M := Γ(W, f ⁻¹ᵁ S.basicOpen g)) (n := n) hbV).choose_spec B cB aB)))
    constructor
    · rintro ⟨h1, h2⟩
      haveI := h1
      exact ⟨Module.Flat.of_linearEquiv etrans, fun p => by
        rw [Module.rankAtStalk_eq_of_equiv etrans]; exact h2 p⟩
    · rintro ⟨h1, h2⟩
      haveI := h1
      exact ⟨Module.Flat.of_linearEquiv etrans.symm, fun p => by
        rw [Module.rankAtStalk_eq_of_equiv etrans.symm]; exact h2 p⟩

/-- The defining property of the flattening ideal sheaf on an affine open: an algebra
kills it iff the base-changed pushforward module is finite locally free of rank `n`. -/
private theorem locallyFreeRankLocusSheaf_spec (n : ℕ)
    (hb : ∀ (U : S.affineOpens) (K : Type u) (_ : Field K)
      (_ : Algebra Γ(S, U.1) K),
      letI := ((f.app U.1).hom).toAlgebra
      Module.finrank K (K ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) ≤ n)
    (U : S.affineOpens) (A : Type u) (cA : CommRing A) (aA : Algebra Γ(S, U.1) A) :
    letI := ((f.app U.1).hom).toAlgebra
    ((Module.Flat A (A ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) ∧
        ∀ p : PrimeSpectrum A,
          Module.rankAtStalk (A ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) p = n) ↔
      ((locallyFreeRankLocusSheaf f n hb).ideal U).map (algebraMap Γ(S, U.1) A) = ⊥) := by
  letI := ((f.app U.1).hom).toAlgebra
  haveI := locallyFreeRankLocusSheaf_fp f U
  exact (locallyFreeRankLocusAux_exists_ideal (M := Γ(W, f ⁻¹ᵁ U.1)) (n := n)
    (hb U)).choose_spec A cA aA

end LocallyFreeRankLocusSheaf

section LocallyFreeRankLocusBridge

open scoped TensorProduct

variable {W : Scheme.{u}} (f : W ⟶ S) [IsFinite f] [LocallyOfFinitePresentation f]

/-- The geometric identification behind the chart bridge: the pullback of `f` along an
affine chart point is the `Spec` of the section tensor product, with the projection
matching the `Spec` of the left inclusion (sealed; consumed by the bridge and by the
emptiness transport). -/
private theorem locallyFreeRankLocus_pullback_iso {X : Scheme.{u}} [IsAffine X]
    (U : S.affineOpens) (x' : X ⟶ ↑U.1) :
    letI := (((f ∣_ U.1).appTop).hom).toAlgebra
    letI := ((x'.appTop).hom).toAlgebra
    ∃ e : pullback f (x' ≫ U.1.ι) ≅
      Spec (.of (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤))),
      pullback.snd f (x' ≫ U.1.ι) = e.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤))))
        ≫ X.isoSpec.inv := by
  letI := (((f ∣_ U.1).appTop).hom).toAlgebra
  letI := ((x'.appTop).hom).toAlgebra
  haveI : IsAffine (↑U.1 : Scheme.{u}) := U.2
  haveI : IsAffine (↑(f ⁻¹ᵁ U.1) : Scheme.{u}) := U.2.preimage f
  -- paste the restriction square onto the `x'`-square
  have hbig : IsPullback
      (pullback.fst (f ∣_ U.1) x' ≫ (f ⁻¹ᵁ U.1).ι)
      (pullback.snd (f ∣_ U.1) x') f (x' ≫ U.1.ι) :=
    (IsPullback.of_hasPullback (f ∣_ U.1) x').paste_horiz
      (isPullback_morphismRestrict f U.1).flip
  -- conjugate both legs of the small pullback to `Spec` maps
  have hsq₁ : x' ≫ (↑U.1 : Scheme.{u}).isoSpec.hom
      = X.isoSpec.hom ≫ Spec.map (x'.appTop) :=
    (Scheme.isoSpec_hom_naturality x').symm
  have hsq₂ : (f ∣_ U.1) ≫ (↑U.1 : Scheme.{u}).isoSpec.hom
      = (↑(f ⁻¹ᵁ U.1) : Scheme.{u}).isoSpec.hom ≫ Spec.map ((f ∣_ U.1).appTop) :=
    (Scheme.isoSpec_hom_naturality (f ∣_ U.1)).symm
  let m : pullback x' (f ∣_ U.1) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(↑U.1, ⊤) Γ(X, ⊤))))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(↑U.1, ⊤) Γ(↑(f ⁻¹ᵁ U.1), ⊤)))) :=
    pullback.map _ _ _ _ X.isoSpec.hom (↑(f ⁻¹ᵁ U.1) : Scheme.{u}).isoSpec.hom
      (↑U.1 : Scheme.{u}).isoSpec.hom hsq₁ hsq₂
  haveI : IsIso m := by
    show IsIso (pullback.map _ _ _ _ X.isoSpec.hom
      (↑(f ⁻¹ᵁ U.1) : Scheme.{u}).isoSpec.hom
      (↑U.1 : Scheme.{u}).isoSpec.hom hsq₁ hsq₂)
    infer_instance
  refine ⟨hbig.isoPullback.symm ≪≫ pullbackSymmetry (f ∣_ U.1) x' ≪≫ asIso m ≪≫
    pullbackSpecIso Γ(↑U.1, ⊤) Γ(X, ⊤) Γ(↑(f ⁻¹ᵁ U.1), ⊤), ?_⟩
  have h₁ : pullback.snd f (x' ≫ U.1.ι)
      = hbig.isoPullback.inv ≫ pullback.snd (f ∣_ U.1) x' := by
    rw [Iso.eq_inv_comp, hbig.isoPullback_hom_snd]
  have h₂ : pullback.snd (f ∣_ U.1) x'
      = (pullbackSymmetry (f ∣_ U.1) x').hom ≫ pullback.fst x' (f ∣_ U.1) :=
    (pullbackSymmetry_hom_comp_fst _ _).symm
  have h₃ : pullback.fst x' (f ∣_ U.1)
      = m ≫ pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(↑U.1, ⊤) Γ(X, ⊤))))
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(↑U.1, ⊤) Γ(↑(f ⁻¹ᵁ U.1), ⊤))))
        ≫ X.isoSpec.inv := by
    have hm : m ≫ pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(↑U.1, ⊤) Γ(X, ⊤))))
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(↑U.1, ⊤) Γ(↑(f ⁻¹ᵁ U.1), ⊤))))
        = pullback.fst x' (f ∣_ U.1) ≫ X.isoSpec.hom := pullback.lift_fst _ _ _
    rw [← Category.assoc, hm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h₄ : pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(↑U.1, ⊤) Γ(X, ⊤))))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(↑U.1, ⊤) Γ(↑(f ⁻¹ᵁ U.1), ⊤))))
      = (pullbackSpecIso Γ(↑U.1, ⊤) Γ(X, ⊤) Γ(↑(f ⁻¹ᵁ U.1), ⊤)).hom
        ≫ Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)))) := by
    rw [← pullbackSpecIso_inv_fst', Iso.hom_inv_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  slice_rhs 4 5 => rw [← h₄]
  slice_rhs 3 5 => rw [← h₃]
  slice_rhs 2 3 => rw [← h₂]
  slice_rhs 1 2 => rw [← h₁]

/-- The section-ring identification behind the chart bridge, sealed behind its own
constant (the construction is let-heavy; consumers only need existence). -/
private theorem locallyFreeRankLocus_sections_equiv {X : Scheme.{u}} [IsAffine X]
    (U : S.affineOpens) (x' : X ⟶ ↑U.1) :
    letI := ((x'.appTop).hom.comp ((Scheme.Opens.topIso U.1).inv.hom)).toAlgebra
    letI := ((f.app U.1).hom).toAlgebra
    letI := (((f ∣_ U.1).appTop).hom).toAlgebra
    letI := ((x'.appTop).hom).toAlgebra
    Nonempty ((Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤))
      ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) := by
  letI := ((x'.appTop).hom.comp ((Scheme.Opens.topIso U.1).inv.hom)).toAlgebra
  letI := ((f.app U.1).hom).toAlgebra
  letI := (((f ∣_ U.1).appTop).hom).toAlgebra
  letI := ((x'.appTop).hom).toAlgebra
  refine ⟨?_⟩
  -- the restriction/topIso square
  have hsq : (f ∣_ U.1).appTop ≫ (Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom
      = (Scheme.Opens.topIso U.1).hom ≫ f.app U.1 := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop,
      Scheme.Hom.resLE_app_top]
    simp only [Scheme.Hom.app_eq_appLE, Category.assoc]
    rw [Iso.inv_hom_id, Category.comp_id]
  have hsq' : ∀ u, (Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom.hom
      (((f ∣_ U.1).appTop).hom u)
      = (f.app U.1).hom (((Scheme.Opens.topIso U.1).hom).hom u) := fun u =>
    congrArg (fun g : Γ(↑U.1, ⊤) ⟶ Γ(W, f ⁻¹ᵁ U.1) => g.hom u) hsq
  -- the canonical scalar towers on the two tensor products suffice; test the
  -- transported algebra maps on the carrying identity
  have hcarry : ∀ u : Γ(↑U.1, ⊤),
      (1 : Γ(X, ⊤)) ⊗ₜ[Γ(S, U.1)] (f.app U.1).hom ((Scheme.Opens.topIso U.1).hom.hom u)
        = ((x'.appTop).hom u) ⊗ₜ[Γ(S, U.1)] (1 : Γ(W, f ⁻¹ᵁ U.1)) := by
    intro u
    have h2 := congrArg
      (fun g : Γ(S, U.1) →+* (Γ(X, ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) =>
        g (((Scheme.Opens.topIso U.1).hom).hom u))
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        (R := Γ(S, U.1)) (A := Γ(X, ⊤)) (B := Γ(W, f ⁻¹ᵁ U.1)))
    simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.includeRight_apply] at h2
    have h3 : (algebraMap Γ(S, U.1) Γ(X, ⊤))
        (((Scheme.Opens.topIso U.1).hom).hom u) = (x'.appTop).hom u := by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
      congr 1
      exact congrArg (fun g : Γ(↑U.1, ⊤) ⟶ Γ(↑U.1, ⊤) => g.hom u)
        (Scheme.Opens.topIso U.1).hom_inv_id
    rw [← h3]
    exact h2.symm
  -- ring-carrier algebra structures (no tensor-side letI: canonical actions rule there)
  letI : Algebra Γ(S, U.1) Γ(↑U.1, ⊤) :=
    (((Scheme.Opens.topIso U.1).inv).hom).toAlgebra
  haveI : IsScalarTower Γ(S, U.1) Γ(↑U.1, ⊤) Γ(X, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra Γ(S, U.1) Γ(↑(f ⁻¹ᵁ U.1), ⊤) :=
    (((f ∣_ U.1).appTop).hom.comp (((Scheme.Opens.topIso U.1).inv).hom)).toAlgebra
  haveI : IsScalarTower Γ(S, U.1) Γ(↑U.1, ⊤) Γ(↑(f ⁻¹ᵁ U.1), ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- the algebra map of the patch matches the section-side one through the topIsos
  have halg : ∀ s : Γ(S, U.1),
      algebraMap Γ(S, U.1) Γ(↑(f ⁻¹ᵁ U.1), ⊤) s
        = (Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).inv.hom ((f.app U.1).hom s) := by
    intro s
    have h1 : (f.app U.1).hom s
        = (f.app U.1).hom (((Scheme.Opens.topIso U.1).hom).hom
          (((Scheme.Opens.topIso U.1).inv).hom s)) := by
      congr 1
      exact (congrArg (fun g : Γ(S, U.1) ⟶ Γ(S, U.1) => g.hom s)
        (Scheme.Opens.topIso U.1).inv_hom_id).symm
    rw [h1, ← hsq' (((Scheme.Opens.topIso U.1).inv).hom s)]
    have h2 : ∀ y, ((Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).inv.hom)
        (((Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom.hom) y) = y := fun y =>
      congrArg (fun g : Γ(↑(f ⁻¹ᵁ U.1), ⊤) ⟶ Γ(↑(f ⁻¹ᵁ U.1), ⊤) => g.hom y)
        (Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom_inv_id
    rw [h2]
    rfl
  -- the middle base change collapses onto the restricted sections
  -- the middle base change collapses onto the restricted sections
  let ℓ : Γ(W, f ⁻¹ᵁ U.1) →ₗ[Γ(S, U.1)] Γ(↑(f ⁻¹ᵁ U.1), ⊤) :=
    { toFun := ((Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).inv).hom
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun s y => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, map_mul,
          show (algebraMap Γ(S, U.1) Γ(W, f ⁻¹ᵁ U.1)) s = (f.app U.1).hom s from rfl,
          ← halg s, ← Algebra.smul_def] }
  have hℓ : ∀ y, ℓ y = ((Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).inv).hom y := fun _ => rfl
  have hui : ∀ u : Γ(↑U.1, ⊤),
      algebraMap Γ(S, U.1) Γ(↑U.1, ⊤) (((Scheme.Opens.topIso U.1).hom).hom u) = u :=
    fun u => congrArg (fun g : Γ(↑U.1, ⊤) ⟶ Γ(↑U.1, ⊤) => g.hom u)
      (Scheme.Opens.topIso U.1).hom_inv_id
  let inv₁ : Γ(↑(f ⁻¹ᵁ U.1), ⊤) →ₗ[Γ(↑U.1, ⊤)]
      (Γ(↑U.1, ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) :=
    { toFun := fun y => (1 : Γ(↑U.1, ⊤)) ⊗ₜ[Γ(S, U.1)]
        (((Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom).hom y)
      map_add' := fun _ _ => by rw [map_add, TensorProduct.tmul_add]
      map_smul' := fun u y => by
        simp only [RingHom.id_apply]
        have h1 : u • y = ((f ∣_ U.1).appTop).hom u * y := rfl
        rw [h1, map_mul, hsq' u]
        have h2 : (((Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom).hom y) = _ := rfl
        rw [show (f.app U.1).hom (((Scheme.Opens.topIso U.1).hom).hom u)
            * (((Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom).hom y)
          = (((Scheme.Opens.topIso U.1).hom).hom u)
            • (((Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom).hom y) from
          (Algebra.smul_def _ _).symm]
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
          Algebra.smul_def, mul_one, hui u, TensorProduct.smul_tmul',
          Algebra.smul_def, mul_one, Algebra.algebraMap_self, RingHom.id_apply] }
  have e₁ : (Γ(↑U.1, ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) ≃ₗ[Γ(↑U.1, ⊤)]
      Γ(↑(f ⁻¹ᵁ U.1), ⊤) := by
    refine LinearEquiv.ofLinear (LinearMap.liftBaseChange _ ℓ) inv₁ ?_ ?_
    · refine LinearMap.ext fun y => ?_
      show LinearMap.liftBaseChange _ ℓ ((1 : Γ(↑U.1, ⊤)) ⊗ₜ[Γ(S, U.1)]
        (((Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom).hom y)) = y
      rw [LinearMap.liftBaseChange_tmul, one_smul, hℓ]
      exact congrArg (fun g : Γ(↑(f ⁻¹ᵁ U.1), ⊤) ⟶ Γ(↑(f ⁻¹ᵁ U.1), ⊤) => g.hom y)
        (Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom_inv_id
    · refine LinearMap.ext fun z => ?_
      induction z with
      | zero => simp
      | tmul u m =>
        show inv₁ (LinearMap.liftBaseChange _ ℓ (u ⊗ₜ m)) = u ⊗ₜ m
        rw [LinearMap.liftBaseChange_tmul, map_smul]
        have h4 : ((Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom).hom (ℓ m) = m :=
          congrArg (fun g : Γ(W, f ⁻¹ᵁ U.1) ⟶ Γ(W, f ⁻¹ᵁ U.1) => g.hom m)
            (Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).inv_hom_id
        show u • ((1 : Γ(↑U.1, ⊤)) ⊗ₜ[Γ(S, U.1)]
          ((Scheme.Opens.topIso (f ⁻¹ᵁ U.1)).hom).hom (ℓ m)) = u ⊗ₜ m
        rw [h4, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add z₁ z₂ h₁ h₂ =>
        show inv₁ (LinearMap.liftBaseChange _ ℓ (z₁ + z₂)) = z₁ + z₂
        rw [map_add, map_add]
        exact congrArg₂ (· + ·) h₁ h₂
  exact ((TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(S, U.1) Γ(↑U.1, ⊤)
      Γ(X, ⊤) Γ(X, ⊤) Γ(W, f ⁻¹ᵁ U.1)).symm.trans
    (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl Γ(X, ⊤) Γ(X, ⊤)) e₁)).symm

/-- Semilinear span transport: a ring isomorphism `B ≃+* K` onto a field, intertwining the
`R`-algebra maps, bounds the `K`-dimension of `K ⊗[R] M` by the cardinality of any
`B`-spanning family of `B ⊗[R] M` (sealed; the fibre-size translation of the chart
bridge — applied with `B` the sections of a `Spec K` chart point). -/
private theorem locallyFreeRankLocus_finrank_le_of_span {R B K M : Type u} [CommRing R]
    [CommRing B] [Field K] [Algebra R B] [Algebra R K] [AddCommGroup M] [Module R M]
    (e : B ≃+* K) (he : ∀ r, e (algebraMap R B r) = algebraMap R K r)
    (s : Finset (B ⊗[R] M)) (hs : Submodule.span B (s : Set (B ⊗[R] M)) = ⊤) :
    Module.finrank K (K ⊗[R] M) ≤ s.card := by
  classical
  let eL : B ≃ₗ[R] K := (AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv
  let Φ : (B ⊗[R] M) ≃ₗ[R] (K ⊗[R] M) := TensorProduct.congr eL (LinearEquiv.refl R M)
  have hΦ : ∀ b : B, ∀ w : B ⊗[R] M, Φ (b • w) = e b • Φ w := by
    intro b w
    induction w with
    | zero => simp
    | tmul b₀ m =>
        simp only [TensorProduct.smul_tmul', smul_eq_mul, Φ, TensorProduct.congr_tmul,
          LinearEquiv.refl_apply]
        rw [show eL (b * b₀) = e b * eL b₀ from map_mul e b b₀]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  have hspan : Submodule.span K ((s.image ⇑Φ : Finset (K ⊗[R] M)) : Set (K ⊗[R] M)) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz : Φ.symm z ∈ Submodule.span B (s : Set (B ⊗[R] M)) := hs ▸ Submodule.mem_top
    have key : ∀ w ∈ Submodule.span B (s : Set (B ⊗[R] M)),
        Φ w ∈ Submodule.span K ((s.image ⇑Φ : Finset (K ⊗[R] M)) : Set (K ⊗[R] M)) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
          exact Submodule.subset_span
            (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hw)))
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul b w _ hw => rw [hΦ]; exact Submodule.smul_mem _ _ hw
    simpa using key _ hz
  calc Module.finrank K (K ⊗[R] M)
      = Module.finrank K (⊤ : Submodule K (K ⊗[R] M)) := (finrank_top _ _).symm
    _ = Module.finrank K (Submodule.span K
          ((s.image ⇑Φ : Finset (K ⊗[R] M)) : Set (K ⊗[R] M))) := by rw [hspan]
    _ ≤ (s.image ⇑Φ).card := by
          simpa using finrank_span_le_card ((s.image ⇑Φ : Finset (K ⊗[R] M)) : Set (K ⊗[R] M))
    _ ≤ s.card := Finset.card_image_le

/-- Emptiness transport for the chart bridge: if the pullback of `f` along an affine chart
point is the empty scheme, the section tensor product is trivial (sealed; the empty branch
of the fibre dichotomy). -/
private theorem locallyFreeRankLocus_sections_subsingleton {X : Scheme.{u}} [IsAffine X]
    (U : S.affineOpens) (x' : X ⟶ ↑U.1)
    (hE : IsEmpty (pullback f (x' ≫ U.1.ι) : Scheme.{u})) :
    letI := (((f ∣_ U.1).appTop).hom).toAlgebra
    letI := ((x'.appTop).hom).toAlgebra
    Subsingleton (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)) := by
  letI := (((f ∣_ U.1).appTop).hom).toAlgebra
  letI := ((x'.appTop).hom).toAlgebra
  obtain ⟨eP, -⟩ := locallyFreeRankLocus_pullback_iso f U x'
  rw [← PrimeSpectrum.isEmpty_iff_subsingleton]
  exact ⟨fun p => hE.false (eP.inv.base p)⟩

/-- **[L1-e0, the affine chart bridge]** For an affine test scheme `X` mapping into an
affine chart `U` of `S`, the geometric rank-`n` local-freeness of the pulled-back `f` is
the module-theoretic condition for the pushforward sections, base-changed to `Γ(X)`. This
is the single point where geometry meets the affine theory: `f` finite makes the pullback
affine, `iff_of_isAffine` reads flatness on global sections, `IsAffine.finrank` reads the
rank function through `Spec`, and the pasting `pullback f (x' ≫ ι) ≅ pullback (f ∣_ U) x'`
plus `pullbackSpecIso` compute the global sections as the tensor product. -/
private theorem locallyFreeRankLocus_chart_iff {X : Scheme.{u}} [IsAffine X]
    (U : S.affineOpens) (x' : X ⟶ ↑U.1) (n : ℕ) :
    letI := ((x'.appTop).hom.comp ((Scheme.Opens.topIso U.1).inv.hom)).toAlgebra
    letI := ((f.app U.1).hom).toAlgebra
    ((Flat (pullback.snd f (x' ≫ U.1.ι)) ∧
        ∀ p : X, (pullback.snd f (x' ≫ U.1.ι)).finrank p = n) ↔
      (Module.Flat Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) ∧
        ∀ q : PrimeSpectrum Γ(X, ⊤),
          Module.rankAtStalk (Γ(X, ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) q = n)) := by
  letI := ((x'.appTop).hom.comp ((Scheme.Opens.topIso U.1).inv.hom)).toAlgebra
  letI := ((f.app U.1).hom).toAlgebra
  haveI : IsAffine (↑U.1 : Scheme.{u}) := U.2
  haveI : IsAffine (↑(f ⁻¹ᵁ U.1) : Scheme.{u}) := U.2.preimage f
  -- (A) the geometric identification (sealed)
  letI := (((f ∣_ U.1).appTop).hom).toAlgebra
  letI := ((x'.appTop).hom).toAlgebra
  obtain ⟨eP, heP⟩ := locallyFreeRankLocus_pullback_iso f U x'
  -- (B) flatness transports through the identification to the ring side
  have hflat_iff : Flat (pullback.snd f (x' ≫ U.1.ι)) ↔
      Module.Flat Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)) := by
    rw [heP, ← Category.assoc, MorphismProperty.cancel_right_of_respectsIso (P := @Flat),
      MorphismProperty.cancel_left_of_respectsIso (P := @Flat),
      HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
  -- (C) given flatness, the rank function transports likewise
  have hrank_iff : Flat (pullback.snd f (x' ≫ U.1.ι)) →
      ((∀ p : X, (pullback.snd f (x' ≫ U.1.ι)).finrank p = n) ↔
      ∀ q : PrimeSpectrum Γ(X, ⊤),
        Module.rankAtStalk (R := Γ(X, ⊤))
          (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)) q = n) := by
    intro hfl
    -- the tensor is a finite module, so the `Spec` leg is a finite flat morphism
    haveI : IsFinite (f ∣_ U.1) := inferInstance
    haveI : Module.Finite Γ(↑U.1, ⊤) Γ(↑(f ⁻¹ᵁ U.1), ⊤) := (f ∣_ U.1).finite_appTop
    haveI hMfin : Module.Finite Γ(X, ⊤)
        (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)) :=
      Module.Finite.base_change _ _ _
    have hφfin : (CommRingCat.ofHom (algebraMap Γ(X, ⊤)
        (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)))).hom.Finite := by
      rw [CommRingCat.hom_ofHom]
      exact RingHom.finite_algebraMap.mpr hMfin
    have hφflat : (CommRingCat.ofHom (algebraMap Γ(X, ⊤)
        (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)))).hom.Flat := by
      rw [CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
      exact hflat_iff.mp hfl
    -- the composed map's rank equals the `Spec` map's rank at the transported point
    have hpt : ∀ p : X, (pullback.snd f (x' ≫ U.1.ι)).finrank p
        = (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤)
            (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤))))).finrank (X.isoSpec.hom p) := by
      intro p
      rw [heP]
      haveI hflSM : Flat (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤)
          (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)))) ≫ X.isoSpec.inv) := by
        rw [MorphismProperty.cancel_right_of_respectsIso (P := @Flat)]
        rw [heP, ← Category.assoc,
          MorphismProperty.cancel_right_of_respectsIso (P := @Flat),
          MorphismProperty.cancel_left_of_respectsIso (P := @Flat)] at hfl
        exact hfl
      haveI hfinSM : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤)
          (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)))) ≫ X.isoSpec.inv) := by
        haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤)
            (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤))))) :=
          (IsFinite.SpecMap_iff _).mpr hφfin
        infer_instance
      have hsq : IsPullback (𝟙 _)
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤)
            (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)))))
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤)
            (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)))) ≫ X.isoSpec.inv)
          X.isoSpec.inv :=
        IsPullback.of_horiz_isIso ⟨by simp⟩
      rw [Scheme.Hom.finrank_comp_left_of_isIso]
      have := Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq (X.isoSpec.hom p)
      rw [show X.isoSpec.inv (X.isoSpec.hom p) = p by simp] at this
      rw [← this]
    constructor
    · intro h q
      have hq := hpt (X.isoSpec.inv q)
      rw [show X.isoSpec.hom (X.isoSpec.inv q) = q by simp] at hq
      rw [← h (X.isoSpec.inv q), hq, Scheme.Hom.finrank_SpecMap_eq_finrank hφfin hφflat,
        CommRingCat.hom_ofHom, RingHom.finrank_algebraMap]
    · intro h p
      rw [hpt p, Scheme.Hom.finrank_SpecMap_eq_finrank hφfin hφflat,
        CommRingCat.hom_ofHom, RingHom.finrank_algebraMap]
      exact h _
  -- (D) the ring-side module is the section-side module (sealed construction)
  obtain ⟨eM⟩ := locallyFreeRankLocus_sections_equiv f U x'
  -- transports across `eM`, elaborated once
  have hrk := Module.rankAtStalk_eq_of_equiv eM
  have hfl₁ : Module.Flat Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)) →
      Module.Flat Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) := fun h => by
    haveI := h
    exact Module.Flat.of_linearEquiv eM.symm
  have hfl₂ : Module.Flat Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) →
      Module.Flat Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(↑U.1, ⊤)] Γ(↑(f ⁻¹ᵁ U.1), ⊤)) := fun h => by
    haveI := h
    exact Module.Flat.of_linearEquiv eM
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hfl₁ (hflat_iff.mp h1), fun q => ?_⟩
    rw [← congrFun hrk q]
    exact (hrank_iff h1).mp h2 q
  · rintro ⟨h1, h2⟩
    have hgf : Flat (pullback.snd f (x' ≫ U.1.ι)) := hflat_iff.mpr (hfl₂ h1)
    refine ⟨hgf, (hrank_iff hgf).mpr fun q => ?_⟩
    rw [congrFun hrk q]
    exact h2 q

/-- **[L1-e3, the per-chart condition]** For an affine chart `V ⊆ T` mapped into an affine
chart `U ⊆ S` by `t`, the geometric rank-`n` local-freeness of `f` pulled back over `V` is
exactly the vanishing in `Γ(T, V)` of the flattening ideal of `U` (composing the chart
bridge with the universal ideal's specification; the interface is in `appLE`-form so both
directions of the locus theorem consume it directly). -/
private theorem locallyFreeRankLocus_chart_cond {T : Scheme.{u}} (t : T ⟶ S) (n : ℕ)
    (hb : ∀ (U : S.affineOpens) (K : Type u) (_ : Field K) (_ : Algebra Γ(S, U.1) K),
      letI := ((f.app U.1).hom).toAlgebra
      Module.finrank K (K ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) ≤ n)
    (U : S.affineOpens) (V : T.affineOpens) (e : V.1 ≤ t ⁻¹ᵁ U.1) :
    (Flat (pullback.snd f (V.1.ι ≫ t)) ∧
        ∀ p : ↑V.1, (pullback.snd f (V.1.ι ≫ t)).finrank p = n) ↔
      ∀ z ∈ (locallyFreeRankLocusSheaf f n hb).ideal U, (t.appLE U.1 V.1 e).hom z = 0 := by
  letI := ((f.app U.1).hom).toAlgebra
  let x' : (↑V.1 : Scheme.{u}) ⟶ (↑U.1 : Scheme.{u}) := t.resLE U.1 V.1 e
  letI := ((x'.appTop).hom.comp ((Scheme.Opens.topIso U.1).inv.hom)).toAlgebra
  haveI : IsAffine (↑V.1 : Scheme.{u}) := V.2
  have h1 := locallyFreeRankLocus_chart_iff f U x' n
  rw [show x' ≫ U.1.ι = V.1.ι ≫ t from Scheme.Hom.resLE_comp_ι t e] at h1
  have h2 := locallyFreeRankLocusSheaf_spec f n hb U Γ(↑V.1, ⊤) inferInstance inferInstance
  -- the chart algebra map is `appLE` conjugated by the top-sections isomorphism
  have hkey : ∀ z : Γ(S, U.1), algebraMap Γ(S, U.1) Γ(↑V.1, ⊤) z =
      ((Scheme.Opens.topIso V.1).inv.hom) ((t.appLE U.1 V.1 e).hom z) := by
    intro z
    show ((x'.appTop).hom.comp ((Scheme.Opens.topIso U.1).inv.hom)) z = _
    rw [RingHom.comp_apply,
      show x'.appTop = (Scheme.Opens.topIso U.1).hom ≫ t.appLE U.1 V.1 e ≫
        (Scheme.Opens.topIso V.1).inv from Scheme.Hom.resLE_app_top t e]
    have hround : (Scheme.Opens.topIso U.1).hom.hom ((Scheme.Opens.topIso U.1).inv.hom z)
        = z := by
      have := congrArg (fun ψ : Γ(S, U.1) ⟶ Γ(S, U.1) => ψ.hom z)
        (Scheme.Opens.topIso U.1).inv_hom_id
      simpa using this
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hround]
  have hinj : Function.Injective ((Scheme.Opens.topIso V.1).inv.hom) :=
    (Scheme.Opens.topIso V.1).symm.commRingCatIsoToRingEquiv.injective
  refine h1.trans (h2.trans ⟨fun hmap z hz => ?_, fun hvan => ?_⟩)
  · have h0 : algebraMap Γ(S, U.1) Γ(↑V.1, ⊤) z ∈
        ((locallyFreeRankLocusSheaf f n hb).ideal U).map
          (algebraMap Γ(S, U.1) Γ(↑V.1, ⊤)) := Ideal.mem_map_of_mem _ hz
    rw [hmap, Ideal.mem_bot, hkey] at h0
    exact hinj (h0.trans (map_zero _).symm)
  · rw [eq_bot_iff]
    refine Ideal.map_le_iff_le_comap.mpr fun z hz => ?_
    rw [Ideal.mem_comap, Ideal.mem_bot, hkey, hvan z hz, map_zero]

end LocallyFreeRankLocusBridge

open scoped TensorProduct in
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
  classical
  -- [L1-e2] the scheme-level fibre dichotomy gives the per-affine module bound
  have hb' : ∀ (U : S.affineOpens) (K : Type u) (_ : Field K) (_ : Algebra Γ(S, U.1) K),
      letI := ((f.app U.1).hom).toAlgebra
      Module.finrank K (K ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) ≤ n := by
    intro U K fK aK
    letI := ((f.app U.1).hom).toAlgebra
    haveI : Module.Finite Γ(S, U.1) Γ(W, f ⁻¹ᵁ U.1) := f.finite_app U.1 U.2
    -- the chart point of `U` with residue field `K`
    let x' : Spec (CommRingCat.of K) ⟶ ↑U.1 :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) K)) ≫ U.2.isoSpec.inv
    letI := ((x'.appTop).hom.comp ((Scheme.Opens.topIso U.1).inv.hom)).toAlgebra
    letI := (((f ∣_ U.1).appTop).hom).toAlgebra
    letI := ((x'.appTop).hom).toAlgebra
    -- the section ring of the chart point is `K` itself, compatibly over `Γ(S, U)`
    let eK : Γ(Spec (CommRingCat.of K), ⊤) ≃+* K :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
    have hcomp : (Scheme.Opens.topIso U.1).inv ≫ x'.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
        CommRingCat.ofHom (algebraMap Γ(S, U.1) K) := by
      show (Scheme.Opens.topIso U.1).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) K)) ≫ U.2.isoSpec.inv).appTop ≫ _ = _
      rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_inv_appTop, Category.assoc,
        Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
      exact (Scheme.ΓSpecIso Γ(S, U.1)).inv_hom_id_assoc
        (CommRingCat.ofHom (algebraMap Γ(S, U.1) K))
    have he : ∀ r : Γ(S, U.1),
        eK (algebraMap Γ(S, U.1) Γ(Spec (CommRingCat.of K), ⊤) r) =
          algebraMap Γ(S, U.1) K r := fun r =>
      congrArg (fun ψ : Γ(S, U.1) ⟶ CommRingCat.of K => ψ.hom r) hcomp
    -- fibre dichotomy at the chart point
    rcases hb K (x' ≫ U.1.ι) with hE | ⟨hF, hR⟩
    · -- empty fibre: the tensor is trivial, so the empty family spans
      haveI := locallyFreeRankLocus_sections_subsingleton f U x' hE
      obtain ⟨eM⟩ := locallyFreeRankLocus_sections_equiv f U x'
      haveI : Subsingleton
          (Γ(Spec (CommRingCat.of K), ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) :=
        eM.symm.toEquiv.subsingleton
      have h0 := locallyFreeRankLocus_finrank_le_of_span eK he
        (∅ : Finset (Γ(Spec (CommRingCat.of K), ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)))
        (Subsingleton.elim _ _)
      simpa using h0.trans (Nat.zero_le n)
    · -- nonempty fibre: flat of rank `n`; read through the chart bridge
      obtain ⟨hflatB, hrankB⟩ := (locallyFreeRankLocus_chart_iff f U x' n).mp ⟨hF, hR⟩
      -- the section ring is a field via `eK`
      have hBfield : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
        ⟨⟨eK.symm 0, eK.symm 1, fun h => zero_ne_one (α := K) (by simpa using congrArg eK h)⟩,
          mul_comm, fun {a} ha => ⟨eK.symm (eK a)⁻¹, eK.injective (by
            rw [map_mul, RingEquiv.apply_symm_apply, map_one, mul_inv_cancel₀
              (fun h0 => ha (by simpa using congrArg eK.symm h0))])⟩⟩
      letI := hBfield.toField
      haveI : Module.Finite Γ(Spec (CommRingCat.of K), ⊤)
          (Γ(Spec (CommRingCat.of K), ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) :=
        Module.Finite.base_change _ _ _
      -- constant rank `n` over the field means dimension `n`
      have hn : Module.finrank Γ(Spec (CommRingCat.of K), ⊤)
          (Γ(Spec (CommRingCat.of K), ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)) = n := by
        have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free
          (R := Γ(Spec (CommRingCat.of K), ⊤))
          (M := Γ(Spec (CommRingCat.of K), ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1)))
          ⟨⊥, Ideal.isPrime_bot⟩
        rw [← hrankB ⟨⊥, Ideal.isPrime_bot⟩, h1, Pi.natCast_apply, Nat.cast_id]
      -- a basis gives a spanning family of size `n`
      let b := Module.finBasis Γ(Spec (CommRingCat.of K), ⊤)
        (Γ(Spec (CommRingCat.of K), ⊤) ⊗[Γ(S, U.1)] Γ(W, f ⁻¹ᵁ U.1))
      refine le_trans (locallyFreeRankLocus_finrank_le_of_span eK he
        (Finset.univ.image ⇑b) ?_) ?_
      · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
        exact b.span_eq
      · exact le_trans Finset.card_image_le (by simp [hn])
  refine ⟨locallyFreeRankLocusSheaf f n hb', fun T t => ?_⟩
  rw [ModularCurves.exists_factor_subschemeι_iff]
  -- [L1-e3] the factoring locus is exactly the flat-of-rank-`n` locus.
  -- The kernel is the largest ideal sheaf under the componentwise kernels (`ofIdeals` gci):
  have hker_iff : (locallyFreeRankLocusSheaf f n hb') ≤ t.ker ↔
      ∀ U : S.affineOpens, (locallyFreeRankLocusSheaf f n hb').ideal U ≤
        RingHom.ker (t.app U.1).hom :=
    (Scheme.IdealSheafData.gci.gc _ _).symm
  rw [hker_iff]
  -- per-chart geometric condition (through the bridge [L1-e0] + the affine spec)
  constructor
  · -- vanishing on every affine of `S` ⟹ the geometric condition
    intro hle
    -- every chart satisfies the geometric condition, through the per-chart bridge
    have hchart : ∀ (U : S.affineOpens) (V : T.affineOpens) (e : V.1 ≤ t ⁻¹ᵁ U.1),
        Flat (pullback.snd f (V.1.ι ≫ t)) ∧
          ∀ p : ↑V.1, (pullback.snd f (V.1.ι ≫ t)).finrank p = n := by
      intro U V e
      refine (locallyFreeRankLocus_chart_cond f t n hb' U V e).mpr fun z hz => ?_
      have h0 : (t.app U.1).hom z = 0 := by
        have h1 := hle U hz
        rwa [RingHom.mem_ker] at h1
      show ((t.app U.1 ≫ T.presheaf.map (homOfLE e).op).hom) z = 0
      rw [CommRingCat.comp_apply, h0, map_zero]
    -- an affine chart pair through every point of `T`
    have hcover : ∀ x : T, ∃ (U : S.affineOpens) (V : T.affineOpens),
        x ∈ V.1 ∧ V.1 ≤ t ⁻¹ᵁ U.1 := by
      intro x
      obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        S.isBasis_affineOpens (show t.base x ∈ (⊤ : S.Opens) from trivial)
      obtain ⟨V, hV, hxV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        T.isBasis_affineOpens (show x ∈ t ⁻¹ᵁ U from hxU)
      exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVle⟩
    choose Ux Vx hmem hVle using hcover
    -- the pasted square: each chart pullback is the base change of `pullback.snd f t`
    have hsq : ∀ x : T, IsPullback
        (pullback.fst (pullback.snd f t) (Vx x).1.ι ≫ pullback.fst f t)
        (pullback.snd (pullback.snd f t) (Vx x).1.ι) f ((Vx x).1.ι ≫ t) := fun x =>
      (IsPullback.of_hasPullback (pullback.snd f t) (Vx x).1.ι).paste_horiz
        (IsPullback.of_hasPullback f t)
    have hVtop : (⨆ x : T, (Vx x).1) = ⊤ := by
      rw [eq_top_iff]
      exact fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hmem x⟩
    -- flatness is Zariski-local on the target, and holds over each chart
    haveI hflat : Flat (pullback.snd f t) := by
      refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun x : T => (Vx x).1) hVtop fun x => ?_
      have h1 := (isPullback_morphismRestrict (pullback.snd f t) (Vx x).1).flip
      rw [← h1.isoPullback_hom_snd, ← (hsq x).isoPullback_hom_snd,
        MorphismProperty.cancel_left_of_respectsIso (P := @Flat),
        MorphismProperty.cancel_left_of_respectsIso (P := @Flat)]
      exact (hchart (Ux x) (Vx x) (hVle x)).1
    refine ⟨hflat, fun x => ?_⟩
    -- the rank at `x` is computed on the chart through `x`
    have hch := hchart (Ux x) (Vx x) (hVle x)
    haveI := hch.1
    have hrk := Scheme.Hom.finrank_of_isPullback _ _ _ _
      (IsPullback.of_hasPullback (pullback.snd f t) (Vx x).1.ι) ⟨x, hmem x⟩
    rw [show ((Vx x).1.ι ⟨x, hmem x⟩ : T) = x from rfl] at hrk
    rw [← hrk, ← (hsq x).isoPullback_hom_snd, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hch.2 ⟨x, hmem x⟩
  · -- the geometric condition ⟹ vanishing (elementwise, on an affine cover of `t ⁻¹ᵁ U`)
    rintro ⟨hflat, hrank⟩
    intro U z hz
    rw [RingHom.mem_ker]
    -- the restriction of `t.app U z` to every affine chart inside `t ⁻¹ᵁ U` vanishes
    have hvan : ∀ (V : T.affineOpens) (e : V.1 ≤ t ⁻¹ᵁ U.1),
        (T.presheaf.map (homOfLE e).op).hom ((t.app U.1).hom z) = 0 := by
      intro V e
      -- the chart pullback is the base change of `pullback.snd f t` along `V.ι`
      have hsq : IsPullback (pullback.fst (pullback.snd f t) V.1.ι ≫ pullback.fst f t)
          (pullback.snd (pullback.snd f t) V.1.ι) f (V.1.ι ≫ t) :=
        (IsPullback.of_hasPullback (pullback.snd f t) V.1.ι).paste_horiz
          (IsPullback.of_hasPullback f t)
      have hsnd : pullback.snd f (V.1.ι ≫ t) =
          hsq.isoPullback.inv ≫ pullback.snd (pullback.snd f t) V.1.ι :=
        (Iso.eq_inv_comp _).mpr hsq.isoPullback_hom_snd
      have hcflat : Flat (pullback.snd f (V.1.ι ≫ t)) := by
        rw [hsnd, MorphismProperty.cancel_left_of_respectsIso (P := @Flat)]
        infer_instance
      have hcrank : ∀ p : ↑V.1, (pullback.snd f (V.1.ι ≫ t)).finrank p = n := by
        intro p
        rw [hsnd, Scheme.Hom.finrank_comp_left_of_isIso,
          Scheme.Hom.finrank_of_isPullback _ _ _ _
            (IsPullback.of_hasPullback (pullback.snd f t) V.1.ι) p]
        exact hrank _
      have hz0 := (locallyFreeRankLocus_chart_cond f t n hb' U V e).mp ⟨hcflat, hcrank⟩ z hz
      rwa [show t.appLE U.1 V.1 e = t.app U.1 ≫ T.presheaf.map (homOfLE e).op from rfl,
        CommRingCat.comp_apply] at hz0
    -- affine charts cover `t ⁻¹ᵁ U`; a section vanishing on all of them is zero
    have hcover : ∀ p : {q : T // q ∈ t ⁻¹ᵁ U.1}, ∃ V : T.affineOpens,
        p.1 ∈ V.1 ∧ V.1 ≤ t ⁻¹ᵁ U.1 := by
      intro p
      obtain ⟨V, hV, hpV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        T.isBasis_affineOpens p.2
      exact ⟨⟨V, hV⟩, hpV, hVle⟩
    choose Vc hmem hVle using hcover
    refine T.sheaf.eq_of_locally_eq' (fun p => (Vc p).1) (t ⁻¹ᵁ U.1)
      (fun p => homOfLE (hVle p)) (fun q hq => ?_) _ 0 (fun p => ?_)
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hq⟩, hmem ⟨q, hq⟩⟩
    · show (T.presheaf.map (homOfLE (hVle p)).op).hom ((t.app U.1).hom z)
        = (T.presheaf.map (homOfLE (hVle p)).op).hom 0
      rw [map_zero]
      exact hvan (Vc p) (hVle p)

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
      (∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S) (P : E.Point t)
        (h : T ⟶ D.ideal.subscheme), h ≫ D.ideal.subschemeι = P.1 →
        ((∃ k : T ⟶ Z.subscheme, k ≫ Z.subschemeι = h) ↔
          E.IsDivisorGenerator N D t (Point.asSection E t P))) ∧
      ∀ V : D.ideal.subscheme.affineOpens, (Z.ideal V).FG := by
  haveI : Smooth (E.baseChange (D.ideal.subschemeι ≫ E.π)).π :=
    SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨Z, hZ, hfg⟩ := RelEffCartierDiv.exists_incidenceLocusEQ'
    (E.baseChange (D.ideal.subschemeι ≫ E.π)).smooth
    (Section.orderDivisor (E.baseChange (D.ideal.subschemeι ≫ E.π))
      (Point.asSection E (D.ideal.subschemeι ≫ E.π) (E.divisorTautPoint D)) N)
    (D.baseChange (D.ideal.subschemeι ≫ E.π))
  refine ⟨Z, fun T t P h hcomp => ?_, hfg⟩
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
  have hct : h ≫ (D.ideal.subschemeι ≫ E.π) = t := by
    rw [← Category.assoc, hcomp]; exact P.2
  refine Iff.trans (fullLevelLocusAux_comap_iff hct _ _) ?_
  have hP2 : (D.baseChange (D.ideal.subschemeι ≫ E.π)).ideal.comap (fullLevelLocusAux_theta hct)
      = (D.baseChange t).ideal := by
    rw [RelEffCartierDiv.baseChange_ideal, ← Scheme.IdealSheafData.comap_comp,
      fullLevelLocusAux_theta_fst, ← RelEffCartierDiv.baseChange_ideal]
  have hP1 : (Section.orderDivisor (E.baseChange (D.ideal.subschemeι ≫ E.π))
        (Point.asSection E (D.ideal.subschemeι ≫ E.π) (E.divisorTautPoint D)) N).ideal.comap
        (fullLevelLocusAux_theta hct)
      = (Section.orderDivisor (E.baseChange t) (Point.asSection E t P) N).ideal := by
    simp only [Section.orderDivisor]
    rw [fullLevelLocusAux_sectionsDivisor_ideal, fullLevelLocusAux_sectionsDivisor_ideal,
      Scheme.IdealSheafData.comap_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hm_a : h ≫ (subgroupLocusAux_val E (D.ideal.subschemeι ≫ E.π)
          ((((a : ℕ) : ℤ) + 1) • Point.asSection E (D.ideal.subschemeι ≫ E.π)
            (E.divisorTautPoint D)) ≫ pullback.fst E.π (D.ideal.subschemeι ≫ E.π))
        = subgroupLocusAux_val E t ((((a : ℕ) : ℤ) + 1) • Point.asSection E t P)
          ≫ pullback.fst E.π t := by
      rw [exactOrderLocusAux_val_smul_asSection_fst, exactOrderLocusAux_val_smul_asSection_fst,
        ← Category.assoc]
      exact congrArg (· ≫ E.mulByHom (((a : ℕ) : ℤ) + 1)) hcomp
    have key := exactOrderLocusAux_ker_comap_eq
      (subgroupLocusAux_val E (D.ideal.subschemeι ≫ E.π)
        ((((a : ℕ) : ℤ) + 1) • Point.asSection E (D.ideal.subschemeι ≫ E.π) (E.divisorTautPoint D)))
      (subgroupLocusAux_val E t ((((a : ℕ) : ℤ) + 1) • Point.asSection E t P))
      (exactOrderLocusAux_val_isClosedImmersion E _ _)
      (exactOrderLocusAux_val_isClosedImmersion E t _)
      (subgroupLocusAux_val_snd E _ _)
      (subgroupLocusAux_val_snd E t _)
      hm_a
      (fullLevelLocusAux_theta hct) (𝟙 (pullback E.π t))
      (fullLevelLocusAux_theta_snd hct) (Category.id_comp _)
      (by rw [Category.id_comp, fullLevelLocusAux_theta_fst])
    rw [Scheme.IdealSheafData.comap_id] at key
    exact key
  refine Iff.trans (Iff.of_eq (congrArg₂ Eq hP1 hP2)) ?_
  simp only [EllipticCurve.IsDivisorGenerator]
  exact ⟨fun hb => ⟨E.hasExactOrder_of_orderDivisor_ideal_eq N D hD t (Point.asSection E t P) hb, hb⟩,
    fun hh => hh.2⟩

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
  (E.exists_generatorLocus N D hD).choose_spec.1

/-- **([T-SG3-LFP], the equations pin)** The generator locus is affine-locally finitely
generated — KM's *"defined, locally on `S`, by finitely many equations"* — hence its
inclusion `D^× ↪ D` is locally of finite presentation. -/
theorem generatorSpaceι_locallyOfFinitePresentation (N : ℕ) [NeZero N]
    (D : RelEffCartierDiv E.π) (hD : D.IsSubgroup E) :
    LocallyOfFinitePresentation (E.generatorSpaceι N D hD) :=
  lfp_subschemeι_of_fg (E.exists_generatorLocus N D hD).choose_spec.2

/-- Kernels of closed immersions transport along a postcomposed isomorphism (sealed;
the per-factor step of the order-divisor pasting naturality). -/
private theorem generatorSpace_baseChange_ker_comap {X Y Z : Scheme.{u}} (v : X ⟶ Y)
    (e : Y ⟶ Z) [IsClosedImmersion v] [IsIso e] :
    (Scheme.Hom.ker (v ≫ e)).comap e = v.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (v ≫ e) e]
  have h : IsPullback v (𝟙 X) e (v ≫ e) := IsPullback.of_vert_isIso ⟨by simp⟩
  rw [show pullback.fst e (v ≫ e) = h.isoPullback.inv ≫ v from
    (Iso.eq_inv_comp _).mpr h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- Containment of the base-changed divisor ideal in a kernel is containment of the
divisor ideal in the kernel of the `E`-projected value (sealed; both directions of the
generator-scheme factoring transport). -/
private theorem generatorSpace_baseChange_le_ker_iff (D : RelEffCartierDiv E.π)
    {T Q : Scheme.{u}} (t : T ⟶ S) (v : Q ⟶ pullback E.π t) :
    (D.baseChange t).ideal ≤ Scheme.Hom.ker v ↔
      D.ideal ≤ Scheme.Hom.ker (v ≫ pullback.fst E.π t) := by
  rw [RelEffCartierDiv.baseChange_ideal,
    show Scheme.Hom.ker (v ≫ pullback.fst E.π t) =
        (Scheme.Hom.ker v).map (pullback.fst E.π t) from by
      rw [← Scheme.IdealSheafData.map_bot, ← Scheme.IdealSheafData.map_bot,
        Scheme.IdealSheafData.map_comp],
    Scheme.IdealSheafData.le_map_iff_comap_le]

/-- The value of an integer multiple of the original point, pulled back through the
pasting isomorphism, is the value of the multiple of the transported point (sealed; the
morphism-level input to the order-divisor pasting naturality — stated with `ψ.inv` so the
whole equation elaborates at the raw iterated-pullback spelling). -/
private theorem generatorSpace_baseChange_val_comp {T Q : Scheme.{u}} (t : T ⟶ S)
    (q : Q ⟶ T) (P : E.Point (q ≫ t)) (P' : (E.baseChange t).Point q)
    (hPP' : P'.1 ≫ pullback.fst E.π t = P.1) (m : ℤ) :
    subgroupLocusAux_val E (q ≫ t) (m • EllipticCurve.Point.asSection E (q ≫ t) P) ≫
        (pullbackLeftPullbackSndIso E.π t q).inv =
      subgroupLocusAux_val (E.baseChange t) q
        (m • EllipticCurve.Point.asSection (E.baseChange t) q P') := by
  have hsmul' : @CategoryStruct.comp Scheme _ Q (pullback (pullback.snd E.π t) q)
        (pullback E.π t)
        (subgroupLocusAux_val (E.baseChange t) q
          (m • EllipticCurve.Point.asSection (E.baseChange t) q P'))
        (pullback.fst (pullback.snd E.π t) q) =
      (P'.1 : Q ⟶ pullback E.π t) ≫ (E.baseChange t).mulByHom m :=
    exactOrderLocusAux_val_smul_asSection_fst (E.baseChange t) q m P'
  have hval' : @CategoryStruct.comp Scheme _ Q (pullback (pullback.snd E.π t) q) Q
        (subgroupLocusAux_val (E.baseChange t) q
          (m • EllipticCurve.Point.asSection (E.baseChange t) q P'))
        (pullback.snd (pullback.snd E.π t) q) =
      𝟙 Q :=
    subgroupLocusAux_val_snd (E.baseChange t) q _
  have hmul' : @CategoryStruct.comp Scheme _ (pullback E.π t) (pullback E.π t) E.E
      ((E.baseChange t).mulByHom m) (pullback.fst E.π t) =
      pullback.fst E.π t ≫ E.mulByHom m :=
    EllipticCurve.mulByHom_baseChange_fst E t m
  have hmulsnd' : @CategoryStruct.comp Scheme _ (pullback E.π t) (pullback E.π t) T
      ((E.baseChange t).mulByHom m) (pullback.snd E.π t) = pullback.snd E.π t :=
    EllipticCurve.mulByHom_baseChange_snd E t m
  have hP'2 : @CategoryStruct.comp Scheme _ Q (pullback E.π t) T P'.1
      (pullback.snd E.π t) = q := P'.2
  have hPP'' : @CategoryStruct.comp Scheme _ Q (pullback E.π t) E.E P'.1
      (pullback.fst E.π t) = P.1 := hPP'
  have hkey₁ : @CategoryStruct.comp Scheme _ Q (pullback E.π t) E.E
      (@CategoryStruct.comp Scheme _ Q (pullback E.π t) (pullback E.π t) P'.1
        ((E.baseChange t).mulByHom m))
      (pullback.fst E.π t) = P.1 ≫ E.mulByHom m := by
    rw [Category.assoc, hmul', ← Category.assoc, hPP'']
  have hkey₂ : @CategoryStruct.comp Scheme _ Q (pullback E.π t) T
      (@CategoryStruct.comp Scheme _ Q (pullback E.π t) (pullback E.π t) P'.1
        ((E.baseChange t).mulByHom m))
      (pullback.snd E.π t) = q := by
    rw [Category.assoc, hmulsnd', hP'2]
  apply pullback.hom_ext
  · -- the `pullback E.π t`-component: compare both `E`- and `T`-legs
    rw [Category.assoc, hsmul']
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
        exactOrderLocusAux_val_smul_asSection_fst E (q ≫ t) m P]
      exact hkey₁.symm
    · rw [Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
        ← Category.assoc, subgroupLocusAux_val_snd, Category.id_comp]
      exact hkey₂.symm
  · rw [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hval',
      subgroupLocusAux_val_snd]


/-- Kernels of closed immersions transport along a precomposed inverse isomorphism, in
comap form (sealed; the per-factor step of the order-divisor pasting naturality). -/
private theorem generatorSpace_baseChange_ker_inv {X Y Z : Scheme.{u}} (v : X ⟶ Z)
    (e : Y ≅ Z) [IsClosedImmersion v] :
    Scheme.Hom.ker (v ≫ e.inv) = (Scheme.Hom.ker v).comap e.hom := by
  haveI : IsClosedImmersion (v ≫ e.inv) := inferInstance
  have h := generatorSpace_baseChange_ker_comap (v ≫ e.inv) e.hom
  rw [Category.assoc, e.inv_hom_id, Category.comp_id] at h
  exact h.symm

/-- **The order-divisor pasting naturality**: the order divisor of the transported point
over the iterated pullback is the comap along the pasting isomorphism of the order divisor
of the original point over the composite pullback (sealed; the divisor-side half is
`RelEffCartierDiv.baseChange_baseChange_ideal`). -/
private theorem generatorSpace_baseChange_orderDivisor_ideal {T Q : Scheme.{u}} (t : T ⟶ S)
    (q : Q ⟶ T) (P : E.Point (q ≫ t)) (P' : (E.baseChange t).Point q)
    (hPP' : P'.1 ≫ pullback.fst E.π t = P.1) (N : ℕ) [NeZero N] :
    (Section.orderDivisor ((E.baseChange t).baseChange q)
        (EllipticCurve.Point.asSection (E.baseChange t) q P') N).ideal =
      @Scheme.IdealSheafData.comap (pullback (pullback.snd E.π t) q)
        (pullback E.π (q ≫ t))
        (Section.orderDivisor (E.baseChange (q ≫ t))
          (EllipticCurve.Point.asSection E (q ≫ t) P) N).ideal
        (pullbackLeftPullbackSndIso E.π t q).hom := by
  simp only [EllipticCurve.Section.orderDivisor]
  rw [fullLevelLocusAux_sectionsDivisor_ideal, fullLevelLocusAux_sectionsDivisor_ideal]
  have hcp : @Scheme.IdealSheafData.comap (pullback (pullback.snd E.π t) q)
      (pullback E.π (q ≫ t))
      ((∏ i : Fin N, Scheme.Hom.ker
        ((((i : ℕ) : ℤ) + 1) • EllipticCurve.Point.asSection E (q ≫ t) P).1 :
          Scheme.IdealSheafData (E.baseChange (q ≫ t)).E))
      (pullbackLeftPullbackSndIso E.π t q).hom =
      ∏ i : Fin N, @Scheme.IdealSheafData.comap (pullback (pullback.snd E.π t) q)
        (pullback E.π (q ≫ t))
        (Scheme.Hom.ker ((((i : ℕ) : ℤ) + 1) • EllipticCurve.Point.asSection E (q ≫ t) P).1)
        (pullbackLeftPullbackSndIso E.π t q).hom :=
    Scheme.IdealSheafData.comap_prod _ _ _
  rw [hcp]
  refine Finset.prod_congr rfl fun a _ => ?_
  haveI := exactOrderLocusAux_val_isClosedImmersion E (q ≫ t)
    ((((a : ℕ) : ℤ) + 1) • EllipticCurve.Point.asSection E (q ≫ t) P)
  have h1 := congrArg Scheme.Hom.ker
    (generatorSpace_baseChange_val_comp E t q P P' hPP' (((a : ℕ) : ℤ) + 1))
  have h2 := generatorSpace_baseChange_ker_inv
    (subgroupLocusAux_val E (q ≫ t)
      ((((a : ℕ) : ℤ) + 1) • EllipticCurve.Point.asSection E (q ≫ t) P))
    (pullbackLeftPullbackSndIso E.π t q)
  exact h1.symm.trans h2

/-- **The `IsDivisorGenerator` composite-vs-iterated base-change bridge** (sealed): a point
of `E` over `q ≫ t` generates `D` iff the corresponding point of `E ×_S T` over `q`
generates `D ×_S T`. Both sides reduce to their order-divisor–ideal equalities
(`hasExactOrder_of_orderDivisor_ideal_eq`), which correspond under comap along the pasting
isomorphism. -/
private theorem generatorSpace_baseChange_isDivisorGenerator_iff (N : ℕ) [NeZero N]
    (D : RelEffCartierDiv E.π) (hD : D.IsSubgroup E) {T Q : Scheme.{u}} (t : T ⟶ S)
    (q : Q ⟶ T) (P : E.Point (q ≫ t)) (P' : (E.baseChange t).Point q)
    (hPP' : P'.1 ≫ pullback.fst E.π t = P.1) :
    (E.baseChange t).IsDivisorGenerator N (D.baseChange t) q
        (EllipticCurve.Point.asSection (E.baseChange t) q P') ↔
      E.IsDivisorGenerator N D (q ≫ t) (EllipticCurve.Point.asSection E (q ≫ t) P) := by
  have hDT : (D.baseChange t).IsSubgroup (E.baseChange t) :=
    RelEffCartierDiv.IsSubgroup.baseChange E hD t
  have h1 : (E.baseChange t).IsDivisorGenerator N (D.baseChange t) q
      (EllipticCurve.Point.asSection (E.baseChange t) q P') ↔
      (Section.orderDivisor ((E.baseChange t).baseChange q)
        (EllipticCurve.Point.asSection (E.baseChange t) q P') N).ideal =
          ((D.baseChange t).baseChange q).ideal :=
    ⟨fun hh => hh.2, fun hb => ⟨(E.baseChange t).hasExactOrder_of_orderDivisor_ideal_eq N
      (D.baseChange t) hDT q _ hb, hb⟩⟩
  have h2 : E.IsDivisorGenerator N D (q ≫ t)
      (EllipticCurve.Point.asSection E (q ≫ t) P) ↔
      (Section.orderDivisor (E.baseChange (q ≫ t))
        (EllipticCurve.Point.asSection E (q ≫ t) P) N).ideal =
          (D.baseChange (q ≫ t)).ideal :=
    ⟨fun hh => hh.2, fun hb =>
      ⟨E.hasExactOrder_of_orderDivisor_ideal_eq N D hD (q ≫ t) _ hb, hb⟩⟩
  rw [h1, h2, generatorSpace_baseChange_orderDivisor_ideal E t q P P' hPP' N,
    RelEffCartierDiv.baseChange_baseChange_ideal D t q]
  constructor
  · intro h
    have h' := congrArg
      (Scheme.IdealSheafData.comap · (pullbackLeftPullbackSndIso E.π t q).inv) h
    simp only [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
      Scheme.IdealSheafData.comap_id] at h'
    exact h'
  · exact fun h => by rw [h]

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
  classical
  set hD' := RelEffCartierDiv.IsSubgroup.baseChange E hD t with hhD'
  -- tautological generator data over the fibre product (raw-valued aliases throughout)
  set q₁ : pullback (E.generatorSpaceπ N D hD) t ⟶ T :=
    pullback.snd (E.generatorSpaceπ N D hD) t with hq₁
  set k₁ : pullback (E.generatorSpaceπ N D hD) t ⟶ E.generatorSpace N D hD :=
    pullback.fst (E.generatorSpaceπ N D hD) t with hk₁
  set h₁ := k₁ ≫ E.generatorSpaceι N D hD with hh₁
  have hP₁π : (h₁ ≫ D.ideal.subschemeι) ≫ E.π = q₁ ≫ t := by
    rw [hh₁, Category.assoc, Category.assoc]
    exact pullback.condition
  set P₁ : E.Point (q₁ ≫ t) := ⟨h₁ ≫ D.ideal.subschemeι, hP₁π⟩ with hP₁
  have hgen₁ := (E.generatorSpace_spec N D hD (q₁ ≫ t) P₁ h₁ rfl).mp ⟨k₁, rfl⟩
  set v₁ : pullback (E.generatorSpaceπ N D hD) t ⟶ pullback E.π t :=
    pullback.lift (h₁ ≫ D.ideal.subschemeι) q₁ hP₁π with hv₁
  set P₁' : (E.baseChange t).Point q₁ := ⟨v₁, pullback.lift_snd _ _ _⟩ with hP₁'
  have hPP₁' : P₁'.1 ≫ pullback.fst E.π t = P₁.1 := pullback.lift_fst _ _ _
  have hgen₁' := (generatorSpace_baseChange_isDivisorGenerator_iff E N D hD t q₁
    P₁ P₁' hPP₁').mpr hgen₁
  have hker₁ : D.ideal ≤ Scheme.Hom.ker P₁.1 :=
    (ModularCurves.exists_factor_subschemeι_iff _ _).mp ⟨h₁, rfl⟩
  have hker₁' : (D.baseChange t).ideal ≤ Scheme.Hom.ker P₁'.1 :=
    (generatorSpace_baseChange_le_ker_iff E D t P₁'.1).mpr
      (le_of_le_of_eq hker₁ (congrArg Scheme.Hom.ker hPP₁').symm)
  obtain ⟨h₁', hcomp₁'⟩ := (ModularCurves.exists_factor_subschemeι_iff
    (@RelEffCartierDiv.ideal (E.baseChange t).E T (E.baseChange t).π (D.baseChange t))
    P₁'.1).mpr hker₁'
  obtain ⟨α, hα⟩ := ((E.baseChange t).generatorSpace_spec N (D.baseChange t) hD' q₁
    P₁' h₁' hcomp₁').mpr hgen₁'
  -- tautological generator data over the base-changed generator scheme
  set gπ' := (E.baseChange t).generatorSpaceπ N (D.baseChange t) hD' with hgπ'
  set gι' := (E.baseChange t).generatorSpaceι N (D.baseChange t) hD' with hgι'
  set Dι' := (@RelEffCartierDiv.ideal (E.baseChange t).E T
    (E.baseChange t).π (D.baseChange t)).subschemeι with hDι'
  set v₂ : (E.baseChange t).generatorSpace N (D.baseChange t) hD' ⟶ pullback E.π t :=
    @CategoryStruct.comp Scheme _ _ _ (pullback E.π t) gι' Dι' with hv₂
  have hc₁ : h₁' ≫ Dι' = v₁ := hcomp₁'
  have hc₁r : @CategoryStruct.comp Scheme _ _ _ (pullback E.π t) h₁' Dι' = v₁ := hcomp₁'
  have hv₂snd : v₂ ≫ pullback.snd E.π t = gπ' := by
    rw [hv₂, Category.assoc]; rfl
  set P₂' : (E.baseChange t).Point gπ' := ⟨v₂, hv₂snd⟩ with hP₂'
  have hgen₂' := ((E.baseChange t).generatorSpace_spec N (D.baseChange t) hD' gπ'
    P₂' gι' rfl).mp ⟨𝟙 _, Category.id_comp _⟩
  have hP₂π : (v₂ ≫ pullback.fst E.π t) ≫ E.π = gπ' ≫ t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hv₂snd]
  set P₂ : E.Point (gπ' ≫ t) := ⟨v₂ ≫ pullback.fst E.π t, hP₂π⟩ with hP₂
  have hgen₂ := (generatorSpace_baseChange_isDivisorGenerator_iff E N D hD t gπ'
    P₂ P₂' rfl).mp hgen₂'
  have hker₂' : (D.baseChange t).ideal ≤ Scheme.Hom.ker P₂'.1 :=
    (ModularCurves.exists_factor_subschemeι_iff _ _).mp ⟨gι', rfl⟩
  have hker₂ : D.ideal ≤ Scheme.Hom.ker P₂.1 :=
    (generatorSpace_baseChange_le_ker_iff E D t P₂'.1).mp hker₂'
  obtain ⟨h₂S, hcomp₂S⟩ := (ModularCurves.exists_factor_subschemeι_iff _ _).mpr hker₂
  obtain ⟨k₂, hk₂⟩ := (E.generatorSpace_spec N D hD (gπ' ≫ t) P₂ h₂S hcomp₂S).mpr hgen₂
  have hβw : k₂ ≫ E.generatorSpaceπ N D hD = gπ' ≫ t := by
    show k₂ ≫ E.generatorSpaceι N D hD ≫ D.ideal.subschemeι ≫ E.π = gπ' ≫ t
    rw [← Category.assoc, hk₂, ← Category.assoc, hcomp₂S]
    exact hP₂π
  set β : (E.baseChange t).generatorSpace N (D.baseChange t) hD' ⟶
      pullback (E.generatorSpaceπ N D hD) t := pullback.lift k₂ gπ' hβw with hβ
  -- monomorphism instances (through the `choose`-wrapping definitions)
  haveI hm₁ : Mono (E.generatorSpaceι N D hD) :=
    show Mono ((E.exists_generatorLocus N D hD).choose.subschemeι) from inferInstance
  haveI hmD : Mono Dι' := by
    rw [hDι']; infer_instance
  haveI hm₂ : Mono ((E.baseChange t).generatorSpaceι N (D.baseChange t) hD') :=
    show Mono (((E.baseChange t).exists_generatorLocus N
      (D.baseChange t) hD').choose.subschemeι) from inferInstance
  -- α is compatible with the structure maps
  have hαπ : α ≫ gπ' = q₁ := by
    have h0 : α ≫ gπ' = ((α ≫ gι') ≫ Dι') ≫ pullback.snd E.π t := by
      rw [Category.assoc, Category.assoc]; rfl
    rw [h0, hα, hc₁]
    exact pullback.lift_snd _ _ _
  refine ⟨⟨α, β, ?_, ?_⟩, hαπ⟩
  · -- α ≫ β = 𝟙: compare both projections of the fibre product
    apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp,
        show β ≫ pullback.fst (E.generatorSpaceπ N D hD) t = k₂ from
          pullback.lift_fst _ _ _, ← cancel_mono (E.generatorSpaceι N D hD),
        ← cancel_mono D.ideal.subschemeι, Category.assoc, Category.assoc,
        ← Category.assoc k₂, hk₂, hcomp₂S]
      have hnat : α ≫ P₂'.1 = P₁'.1 := by
        show α ≫ v₂ = v₁
        rw [hv₂, ← Category.assoc, hα]
        exact hc₁r
      have hαv : α ≫ P₂.1 = P₁.1 := by
        have h1 : α ≫ P₂.1 = (α ≫ P₂'.1) ≫ pullback.fst E.π t := by
          rw [← Category.assoc]; rfl
        rw [h1, hnat, hPP₁']
      exact hαv
    · rw [Category.assoc, Category.id_comp,
        show β ≫ pullback.snd (E.generatorSpaceπ N D hD) t = gπ' from
          pullback.lift_snd _ _ _]
      exact hαπ
  · -- β ≫ α = 𝟙: cancel the two closed immersions of the generator scheme
    rw [← cancel_mono ((E.baseChange t).generatorSpaceι N (D.baseChange t) hD'),
      ← cancel_mono Dι', Category.id_comp, Category.assoc, Category.assoc,
      ← Category.assoc α, ← hgι', hα, hc₁]
    -- β ≫ v₁ = gι' ≫ Dι' (both the raw value of the tautological point)
    apply pullback.hom_ext
    · have hL : @CategoryStruct.comp Scheme _ _ (pullback E.π t) E.E (β ≫ v₁)
          (pullback.fst E.π t) = v₂ ≫ pullback.fst E.π t := by
        rw [Category.assoc,
          show v₁ ≫ pullback.fst E.π t = h₁ ≫ D.ideal.subschemeι from
            pullback.lift_fst _ _ _, hh₁,
          show β ≫ (k₁ ≫ E.generatorSpaceι N D hD) ≫ D.ideal.subschemeι =
            ((β ≫ k₁) ≫ E.generatorSpaceι N D hD) ≫ D.ideal.subschemeι from by
              simp only [Category.assoc],
          show β ≫ k₁ = k₂ from pullback.lift_fst _ _ _, hk₂, hcomp₂S]
      exact hL
    · have hLs : @CategoryStruct.comp Scheme _ _ (pullback E.π t) T (β ≫ v₁)
          (pullback.snd E.π t) = gπ' := by
        rw [Category.assoc,
          show v₁ ≫ pullback.snd E.π t = q₁ from pullback.lift_snd _ _ _]
        exact pullback.lift_snd _ _ _
      exact hLs.trans hv₂snd.symm

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
  refine ⟨hD, hdeg, E.generatorSpace N D hD, E.generatorSpaceπ N D hD, ?_, hflat, hlfp, ?_⟩
  · -- `D^× ⟶ S` is surjective: rank `φ(N) ≥ 1` everywhere.
    have hsurj : Surjective (E.generatorSpaceπ N D hD) := by
      rw [← Scheme.Hom.one_le_finrank_iff_surjective]
      intro s
      rw [hrank s]
      exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    exact hsurj.surj
  · -- The tautological point of `D` over `D^×` is a generator (`generatorSpace_spec` at the
    -- identity factorisation of `generatorSpaceι`).
    have hgen := E.generatorSpace_spec N D hD (E.generatorSpaceπ N D hD)
      ⟨E.generatorSpaceι N D hD ≫ D.ideal.subschemeι, Category.assoc _ _ _⟩
      (E.generatorSpaceι N D hD) rfl
    exact ⟨_, hgen.mp ⟨𝟙 _, Category.id_comp _⟩⟩

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
  have hkill : (N : ℤ) • P₀ = 0 := hord.smul_eq_zero
  -- multiples of `P₀` only depend on the exponent mod `N`
  have hF : ∀ m : ℤ, (m • P₀ : E.Point (𝟙 S))
      = ((((m : ZMod N)).val : ℤ) • P₀ : E.Point (𝟙 S)) := by
    intro m
    have hz : ((m - (((m : ZMod N)).val : ℤ) : ℤ) : ZMod N) = 0 := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id]
      ring
    obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    have hm : m = (((m : ZMod N)).val : ℤ) + (N : ℤ) * q := by linarith
    calc m • P₀ = ((((m : ZMod N)).val : ℤ) + (N : ℤ) * q) • P₀ := by rw [← hm]
      _ = (((m : ZMod N)).val : ℤ) • P₀ + ((N : ℤ) * q) • P₀ := add_smul _ _ _
      _ = (((m : ZMod N)).val : ℤ) • P₀ := by
          rw [mul_comm ((N : ℕ) : ℤ) q, mul_smul, hkill, smul_zero, add_zero]
  -- the order-divisor ideal as an indexed product
  have hpos : IsSeparated E.π ∧ SmoothOfRelativeDimension 1 E.π := ⟨inferInstance, E.smooth⟩
  have hidealQ : ∀ Q : E.Section, (Q.orderDivisor E N).ideal
      = ∏ b : Fin N, Scheme.Hom.ker (((((b : ℕ) : ℤ) + 1) • Q : E.Point (𝟙 S))).1 := by
    intro Q
    rw [Section.orderDivisor, RelEffCartierDiv.sectionsDivisor, dif_pos hpos]
  -- reindexing `Fin N` through `b ↦ (b : ZMod N) + 1`
  have hbij : Function.Bijective (fun b : Fin N => ((b : ℕ) : ZMod N) + 1) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun b₁ b₂ h12 => ?_, by rw [ZMod.card]; exact (Fintype.card_fin N)⟩
    have h13 : ((b₁ : ℕ) : ZMod N) = ((b₂ : ℕ) : ZMod N) := by
      simpa using h12
    have hv := congrArg ZMod.val h13
    rw [ZMod.val_cast_of_lt b₁.2, ZMod.val_cast_of_lt b₂.2] at hv
    exact Fin.ext hv
  have hprod : ∀ {M : Type u} [CommMonoid M] (f : ZMod N → M),
      ∏ b : Fin N, f (((b : ℕ) : ZMod N) + 1) = ∏ z : ZMod N, f z := by
    intro M _ f
    exact Fintype.prod_bijective _ hbij _ _ (fun b => rfl)
  -- `a` is a unit mod `N`
  have hcop : Nat.Coprime a.natAbs N := by
    have : a.gcd (N : ℤ) = a.natAbs.gcd ((N : ℤ)).natAbs := rfl
    rwa [this, Int.natAbs_natCast] at ha
  have hunit : IsUnit ((a : ℤ) : ZMod N) := by
    rcases Int.natAbs_eq a with hpm | hpm
    · rw [hpm, Int.cast_natCast, ← ZMod.coe_unitOfCoprime a.natAbs hcop]
      exact (ZMod.unitOfCoprime a.natAbs hcop).isUnit
    · rw [hpm, Int.cast_neg, Int.cast_natCast, ← ZMod.coe_unitOfCoprime a.natAbs hcop]
      exact (ZMod.unitOfCoprime a.natAbs hcop).isUnit.neg
  obtain ⟨u, hu⟩ := hunit
  have hmulbij : Function.Bijective (fun z : ZMod N => z * ((a : ℤ) : ZMod N)) := by
    rw [← hu]
    exact (Units.mulRight u).bijective
  -- the permuted-product identity
  have hmain : ((a • P₀).orderDivisor E N).ideal = (P₀.orderDivisor E N).ideal := by
    rw [hidealQ (a • P₀), hidealQ P₀]
    have hstep1 : ∀ b : Fin N,
        Scheme.Hom.ker (((((b : ℕ) : ℤ) + 1) • (a • P₀) : E.Point (𝟙 S))).1
          = Scheme.Hom.ker ((((((((b : ℕ) : ZMod N) + 1) * ((a : ℤ) : ZMod N))).val : ℤ)
              • P₀ : E.Point (𝟙 S))).1 := by
      intro b
      congr 2
      rw [smul_smul, hF ((((b : ℕ) : ℤ) + 1) * a)]
      congr 3
      push_cast
      ring
    have hstep2 : ∀ b : Fin N,
        Scheme.Hom.ker (((((b : ℕ) : ℤ) + 1) • P₀ : E.Point (𝟙 S))).1
          = Scheme.Hom.ker ((((((b : ℕ) : ZMod N) + 1)).val : ℤ)
              • P₀ : E.Point (𝟙 S)).1 := by
      intro b
      congr 2
      rw [hF (((b : ℕ) : ℤ) + 1)]
      congr 3
      push_cast
      ring
    calc ∏ b : Fin N, Scheme.Hom.ker (((((b : ℕ) : ℤ) + 1) • (a • P₀) : E.Point (𝟙 S))).1
        = ∏ b : Fin N, Scheme.Hom.ker ((((((((b : ℕ) : ZMod N) + 1) *
            ((a : ℤ) : ZMod N))).val : ℤ) • P₀ : E.Point (𝟙 S))).1 :=
          Finset.prod_congr rfl fun b _ => hstep1 b
      _ = ∏ z : ZMod N, Scheme.Hom.ker ((((z * ((a : ℤ) : ZMod N)).val : ℤ)
            • P₀ : E.Point (𝟙 S))).1 :=
          hprod (fun z => Scheme.Hom.ker ((((z * ((a : ℤ) : ZMod N)).val : ℤ)
            • P₀ : E.Point (𝟙 S))).1)
      _ = ∏ z : ZMod N, Scheme.Hom.ker (((z.val : ℤ) • P₀ : E.Point (𝟙 S))).1 :=
          Fintype.prod_bijective _ hmulbij _ _ (fun z => rfl)
      _ = ∏ b : Fin N, Scheme.Hom.ker ((((((b : ℕ) : ZMod N) + 1)).val : ℤ)
            • P₀ : E.Point (𝟙 S)).1 :=
          (hprod (fun z => Scheme.Hom.ker (((z.val : ℤ) • P₀ : E.Point (𝟙 S))).1)).symm
      _ = ∏ b : Fin N, Scheme.Hom.ker (((((b : ℕ) : ℤ) + 1) • P₀ : E.Point (𝟙 S))).1 :=
          Finset.prod_congr rfl fun b _ => (hstep2 b).symm
  have hideal : ((a • P₀).orderDivisor E N).ideal = D.ideal := hmain.trans hgen
  refine ⟨?_, hideal⟩
  -- exact order transports across the divisor identification
  have hdiveq : (a • P₀).orderDivisor E N = D := RelEffCartierDiv.ext hideal
  show ((a • P₀).orderDivisor E N).IsSubgroup E
  rw [hdiveq]
  exact hD

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
  set hD' := RelEffCartierDiv.IsSubgroup.baseChange E hD t with hhD'
  refine ⟨fun x => hnc ?_⟩
  -- transport the fibre point into the base-changed generator space
  obtain ⟨e, he⟩ := E.generatorSpace_baseChange N D hD t
  -- the generator space is finite over `Spec k`, hence affine with finite section ring
  haveI hιfin : IsFinite ((E.baseChange t).generatorSpaceι N (D.baseChange t) hD') :=
    show IsFinite (((E.baseChange t).exists_generatorLocus N (D.baseChange t)
      hD').choose.subschemeι) from inferInstance
  haveI hDfin : IsFinite ((D.baseChange t).ideal.subschemeι ≫ pullback.snd E.π t) :=
    (D.baseChange t).finite
  haveI hπfin : IsFinite ((E.baseChange t).generatorSpaceπ N (D.baseChange t) hD') :=
    show IsFinite ((E.baseChange t).generatorSpaceι N (D.baseChange t) hD' ≫
      ((D.baseChange t).ideal.subschemeι ≫ pullback.snd E.π t)) from
      MorphismProperty.IsStableUnderComposition.comp_mem (P := @IsFinite) _ _ ‹_› ‹_›
  haveI : IsAffine ((E.baseChange t).generatorSpace N (D.baseChange t) hD') :=
    isAffine_of_isAffineHom ((E.baseChange t).generatorSpaceπ N (D.baseChange t) hD')
  -- the structure ring map and its finiteness
  set σ : CommRingCat.of k ⟶ Γ((E.baseChange t).generatorSpace N (D.baseChange t) hD', ⊤) :=
    Spec.preimage (((E.baseChange t).generatorSpace N (D.baseChange t) hD').isoSpec.inv ≫
      (E.baseChange t).generatorSpaceπ N (D.baseChange t) hD') with hσ
  have hσmap : Spec.map σ =
      ((E.baseChange t).generatorSpace N (D.baseChange t) hD').isoSpec.inv ≫
        (E.baseChange t).generatorSpaceπ N (D.baseChange t) hD' := Spec.map_preimage _
  have hσfin : σ.hom.Finite := by
    rw [← AlgebraicGeometry.IsFinite.SpecMap_iff, hσmap]
    infer_instance
  -- the section ring is nontrivial (the fibre point witnesses a prime)
  haveI hnontriv :
      Nontrivial ↑Γ((E.baseChange t).generatorSpace N (D.baseChange t) hD', ⊤) := by
    have y : PrimeSpectrum ↑Γ((E.baseChange t).generatorSpace N (D.baseChange t) hD', ⊤) :=
      ((E.baseChange t).generatorSpace N (D.baseChange t) hD').isoSpec.hom.base (e.hom.base x)
    exact ⟨0, 1, fun h01 => y.isPrime.ne_top
      ((Ideal.eq_top_iff_one _).mpr (h01 ▸ y.asIdeal.zero_mem))⟩
  -- a maximal ideal gives a finite-residue point
  obtain ⟨m, hmax⟩ := Ideal.exists_maximal
    ↑Γ((E.baseChange t).generatorSpace N (D.baseChange t) hD', ⊤)
  haveI := hmax
  letI : Field (↑Γ((E.baseChange t).generatorSpace N (D.baseChange t) hD', ⊤) ⧸ m) :=
    Ideal.Quotient.field m
  set q : Spec (CommRingCat.of
      (↑Γ((E.baseChange t).generatorSpace N (D.baseChange t) hD', ⊤) ⧸ m)) ⟶
      (E.baseChange t).generatorSpace N (D.baseChange t) hD' :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫
      ((E.baseChange t).generatorSpace N (D.baseChange t) hD').isoSpec.inv with hq
  set h : Spec (CommRingCat.of
      (↑Γ((E.baseChange t).generatorSpace N (D.baseChange t) hD', ⊤) ⧸ m)) ⟶
      Spec (CommRingCat.of k) :=
    q ≫ (E.baseChange t).generatorSpaceπ N (D.baseChange t) hD' with hh
  have hcomp : h = Spec.map (σ ≫ CommRingCat.ofHom (Ideal.Quotient.mk m)) := by
    rw [hh, hq, Spec.map_comp, Category.assoc, hσmap]
    rfl
  -- the cover properties: surjective, flat, finitely presented
  have hsurj : Function.Surjective h.base := by
    haveI : Subsingleton ↑(Spec (CommRingCat.of k)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum k))
    intro s
    have pt : ↑(Spec (CommRingCat.of
        (↑Γ((E.baseChange t).generatorSpace N (D.baseChange t) hD', ⊤) ⧸ m))) :=
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum
        (↑Γ((E.baseChange t).generatorSpace N (D.baseChange t) hD', ⊤) ⧸ m))
    exact ⟨pt, Subsingleton.elim _ _⟩
  have hρfin : (σ ≫ CommRingCat.ofHom (Ideal.Quotient.mk m)).hom.Finite :=
    RingHom.Finite.comp
      (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hσfin
  have hflat : Flat h := by
    rw [hcomp, HasRingHomProperty.Spec_iff (P := @Flat)]
    show RingHom.Flat _
    letI := (σ ≫ CommRingCat.ofHom (Ideal.Quotient.mk m)).hom.toAlgebra
    show Module.Flat k _
    infer_instance
  have hlfp : LocallyOfFinitePresentation h := by
    rw [hcomp, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp hρfin.to_finiteType
  -- the tautological generator over the finite-residue point
  set P : (E.baseChange t).Point h :=
    ⟨q ≫ (E.baseChange t).generatorSpaceι N (D.baseChange t) hD' ≫
      (D.baseChange t).ideal.subschemeι, by
        rw [hh, generatorSpaceπ]
        simp only [Category.assoc]
        rfl⟩ with hP
  have hgen : (E.baseChange t).IsDivisorGenerator N (D.baseChange t) h
      (Point.asSection (E.baseChange t) h P) :=
    ((E.baseChange t).generatorSpace_spec N (D.baseChange t) hD' h P
      (q ≫ (E.baseChange t).generatorSpaceι N (D.baseChange t) hD')
      (Category.assoc _ _ _)).mp ⟨q, rfl⟩
  -- degree `N` descends along the surjective cover
  have hdegT : ∀ s'', (((D.baseChange t).baseChange h)).degree s'' = N := by
    intro s''
    have hdiv : Section.orderDivisor ((E.baseChange t).baseChange h)
        (Point.asSection (E.baseChange t) h P) N = (D.baseChange t).baseChange h :=
      RelEffCartierDiv.ext hgen.2
    rw [← hdiv]
    exact RelEffCartierDiv.sectionsDivisor_degree ((E.baseChange t).baseChange h).π
      ((E.baseChange t).baseChange h).smooth _ s''
  have hdeg' : ∀ s : ↑(Spec (CommRingCat.of k)), (D.baseChange t).degree s = N := by
    intro s
    obtain ⟨s'', rfl⟩ := hsurj s
    exact ((degree_baseChange_apply (E.baseChange t) (D.baseChange t) h s'').symm).trans
      (hdegT s'')
  exact ⟨hD', hdeg', _, h, hsurj, hflat, hlfp,
    Point.asSection (E.baseChange t) h P, hgen.1, hgen.2⟩

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
  classical
  -- the generator scheme is finite and finitely presented over `S`
  haveI hιfin : IsFinite (E.generatorSpaceι N D hD) :=
    show IsFinite ((E.exists_generatorLocus N D hD).choose.subschemeι) from inferInstance
  haveI hιlfp := E.generatorSpaceι_locallyOfFinitePresentation N D hD
  haveI hDfin := D.finite
  haveI hDlfp := D.lfp
  haveI hπfin : IsFinite (E.generatorSpaceπ N D hD) :=
    show IsFinite (E.generatorSpaceι N D hD ≫ D.ideal.subschemeι ≫ E.π) from inferInstance
  haveI hπlfp : LocallyOfFinitePresentation (E.generatorSpaceπ N D hD) :=
    show LocallyOfFinitePresentation
      (E.generatorSpaceι N D hD ≫ D.ideal.subschemeι ≫ E.π) from inferInstance
  -- the fibre dichotomy for the flattening theorem
  have hb : ∀ (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ S),
      IsEmpty (pullback (E.generatorSpaceπ N D hD) t : Scheme.{u}) ∨
        (Flat (pullback.snd (E.generatorSpaceπ N D hD) t) ∧
          ∀ x : Spec (CommRingCat.of k),
            (pullback.snd (E.generatorSpaceπ N D hD) t).finrank x = N.totient) := by
    intro k _ t
    by_cases hc : (E.baseChange t).IsGammaZeroFppf N (D.baseChange t)
    · right
      obtain ⟨hf', hfl', hlfp', hrk'⟩ :=
        (E.baseChange t).generatorSpace_finiteLocallyFree_of_isGammaZeroFppf N
          (D.baseChange t) (RelEffCartierDiv.IsSubgroup.baseChange E hD t) hc
      obtain ⟨e, he⟩ := E.generatorSpace_baseChange N D hD t
      have hsnd : pullback.snd (E.generatorSpaceπ N D hD) t =
          e.hom ≫ (E.baseChange t).generatorSpaceπ N (D.baseChange t)
            (RelEffCartierDiv.IsSubgroup.baseChange E hD t) := he.symm
      constructor
      · rw [hsnd, MorphismProperty.cancel_left_of_respectsIso (P := @Flat)]
        exact hfl'
      · intro x
        rw [hsnd, Scheme.Hom.finrank_comp_left_of_isIso]
        exact hrk' x
    · left
      exact E.generatorSpace_fibre_isEmpty_of_not_isGammaZeroFppf N D hD k t hc
  obtain ⟨Z, hZ⟩ := ModularCurves.exists_locallyFreeRankLocus
    (E.generatorSpaceπ N D hD) N.totient hb
  refine ⟨Z, fun T t => ?_⟩
  rw [hZ t]
  obtain ⟨e, he⟩ := E.generatorSpace_baseChange N D hD t
  have hπ' : (E.baseChange t).generatorSpaceπ N (D.baseChange t)
      (RelEffCartierDiv.IsSubgroup.baseChange E hD t) =
      e.inv ≫ pullback.snd (E.generatorSpaceπ N D hD) t :=
    (Iso.eq_inv_comp e).mpr he
  constructor
  · rintro ⟨hfl, hrk⟩
    refine (E.baseChange t).isGammaZeroFppf_of_generatorSpace_finiteLocallyFree N
      (D.baseChange t) (RelEffCartierDiv.IsSubgroup.baseChange E hD t)
      (fun s => degree_baseChange_eq E hdeg t s) ?_ ?_ ?_ ?_
    · -- finiteness of the base-changed generator projection
      haveI : IsFinite ((E.baseChange t).generatorSpaceι N (D.baseChange t)
          (RelEffCartierDiv.IsSubgroup.baseChange E hD t)) :=
        show IsFinite (((E.baseChange t).exists_generatorLocus N (D.baseChange t)
          (RelEffCartierDiv.IsSubgroup.baseChange E hD t)).choose.subschemeι)
          from inferInstance
      haveI : IsFinite ((D.baseChange t).ideal.subschemeι ≫ pullback.snd E.π t) :=
        (D.baseChange t).finite
      exact show IsFinite ((E.baseChange t).generatorSpaceι N (D.baseChange t)
        (RelEffCartierDiv.IsSubgroup.baseChange E hD t) ≫
          ((D.baseChange t).ideal.subschemeι ≫ pullback.snd E.π t)) from
        MorphismProperty.IsStableUnderComposition.comp_mem (P := @IsFinite) _ _ ‹_› ‹_›
    · rw [hπ', MorphismProperty.cancel_left_of_respectsIso (P := @Flat)]
      exact hfl
    · haveI := (E.baseChange t).generatorSpaceι_locallyOfFinitePresentation N
        (D.baseChange t) (RelEffCartierDiv.IsSubgroup.baseChange E hD t)
      haveI : LocallyOfFinitePresentation
          ((D.baseChange t).ideal.subschemeι ≫ pullback.snd E.π t) :=
        (D.baseChange t).lfp
      exact show LocallyOfFinitePresentation
        ((E.baseChange t).generatorSpaceι N (D.baseChange t)
          (RelEffCartierDiv.IsSubgroup.baseChange E hD t) ≫
          ((D.baseChange t).ideal.subschemeι ≫ pullback.snd E.π t)) from
        MorphismProperty.IsStableUnderComposition.comp_mem
          (P := @LocallyOfFinitePresentation) _ _ ‹_› ‹_›
    · intro s
      rw [hπ', Scheme.Hom.finrank_comp_left_of_isIso]
      exact hrk s
  · intro hc
    obtain ⟨hf', hfl', hlfp', hrk'⟩ :=
      (E.baseChange t).generatorSpace_finiteLocallyFree_of_isGammaZeroFppf N
        (D.baseChange t) (RelEffCartierDiv.IsSubgroup.baseChange E hD t) hc
    have hsnd : pullback.snd (E.generatorSpaceπ N D hD) t =
        e.hom ≫ (E.baseChange t).generatorSpaceπ N (D.baseChange t)
          (RelEffCartierDiv.IsSubgroup.baseChange E hD t) := he.symm
    constructor
    · rw [hsnd, MorphismProperty.cancel_left_of_respectsIso (P := @Flat)]
      exact hfl'
    · intro x
      rw [hsnd, Scheme.Hom.finrank_comp_left_of_isIso]
      exact hrk' x

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
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- Integer multiples of `P₀` only depend on the residue mod `N` (this is where `hkill` enters).
  have hsmul : ∀ {m m' : ℕ}, (m : ZMod N) = (m' : ZMod N) → (m : ℤ) • P₀ = (m' : ℤ) • P₀ := by
    intro m m' h
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd).mp ((ZMod.natCast_eq_natCast_iff m m' N).mp h)
    have hm : (m : ℤ) = (m' : ℤ) + N * (-k) := by linarith
    rw [hm, add_smul, mul_comm, mul_smul, hkill, smul_zero, add_zero]
  -- The kernel-of-multiple function on residues.
  set K : ZMod N → E.E.IdealSheafData :=
    fun x => Scheme.Hom.ker (((x.val : ℤ) • P₀ : E.Point (𝟙 S)) : S ⟶ E.E) with hK
  -- The additive-order-of-residue map into the divisors of `N`.
  set ord : ZMod N → ℕ := fun x => N / Nat.gcd x.val N with hord
  have hord_mem : ∀ x : ZMod N, ord x ∈ N.divisors := fun x =>
    Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x.val N), hN.ne'⟩
  -- Step 1: the LHS is the product of `K` over all residues.
  have hLHS : (P₀.orderDivisor E N).ideal = ∏ x : ZMod N, K x := by
    rw [Section.orderDivisor, fullLevelLocusAux_sectionsDivisor_ideal]
    refine Fintype.prod_bijective (fun a : Fin N => (((a : ℕ) + 1 : ℕ) : ZMod N)) ?_ _ _
      fun a => ?_
    · rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨fun a b hab => ?_, by simp [ZMod.card]⟩
      have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).mp hab
      have h2 : (a : ℕ) ≡ (b : ℕ) [MOD N] := Nat.ModEq.add_right_cancel' 1 h1
      exact Fin.ext (by rwa [Nat.ModEq, Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at h2)
    · have h1 : (((a : ℕ) : ℤ) + 1) • P₀
          = ((((((a : ℕ) + 1 : ℕ) : ZMod N)).val : ℤ) • P₀ : E.Point (𝟙 S)) := by
        rw [show ((a : ℕ) : ℤ) + 1 = (((a : ℕ) + 1 : ℕ) : ℤ) by push_cast; ring]
        exact hsmul (by simp)
      simp only [hK]
      exact congrArg (fun q : E.Point (𝟙 S) => Scheme.Hom.ker (q : S ⟶ E.E)) h1
  -- Step 2: the RHS is the double product of `K` over divisors and units.
  have hRHS : (∏ d ∈ N.divisors.attach,
        letI : NeZero d.1 := ⟨(Nat.pos_of_mem_divisors d.2).ne'⟩
        (E.primeOrderDivisor ((((N / d.1 : ℕ) : ℤ)) • P₀) d.1).ideal)
      = ∏ d ∈ N.divisors, ∏ x ∈ Finset.univ.filter (fun x : ZMod N => ord x = d), K x := by
    -- (a) each prime-order divisor unfolds to a product of kernels over the totatives of `d`
    -- (the instance-free enumeration `b ∈ range d, gcd(b,d) = 1`).
    trans ∏ d ∈ N.divisors.attach,
        ∏ b ∈ (Finset.range d.1).filter (fun b => Nat.Coprime b d.1),
          Scheme.Hom.ker ((((b * (N / d.1) : ℕ) : ℤ) • P₀ : E.Point (𝟙 S)) : S ⟶ E.E)
    · refine Finset.prod_congr rfl fun d _ => ?_
      letI : NeZero d.1 := ⟨(Nat.pos_of_mem_divisors d.2).ne'⟩
      show (E.primeOrderDivisor ((((N / d.1 : ℕ) : ℤ)) • P₀) d.1).ideal = _
      rw [primeOrderDivisor, fullLevelLocusAux_sectionsDivisor_ideal,
        Equiv.prod_comp (Fintype.equivFinOfCardEq
          (ZMod.card_units_eq_totient d.1)).symm
          (fun u : (ZMod d.1)ˣ =>
            Scheme.Hom.ker ((((((u : ZMod d.1)).val : ℤ) • ((((N / d.1 : ℕ) : ℤ)) • P₀) :
              E.Point (𝟙 S))) : S ⟶ E.E))]
      refine Finset.prod_bij (fun (u : (ZMod d.1)ˣ) _ => (u : ZMod d.1).val)
        (fun u _ => Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime u⟩)
        (fun u₁ _ u₂ _ h => Units.ext (ZMod.val_injective _ h))
        (fun b hb => ?_) (fun u _ => ?_)
      · obtain ⟨hbr, hbc⟩ := Finset.mem_filter.mp hb
        refine ⟨ZMod.unitOfCoprime b hbc, Finset.mem_univ _, ?_⟩
        rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
          Nat.mod_eq_of_lt (Finset.mem_range.mp hbr)]
      · refine congrArg (fun q : E.Point (𝟙 S) => Scheme.Hom.ker (q : S ⟶ E.E)) ?_
        rw [smul_smul]
        norm_cast
    rw [Finset.prod_attach N.divisors
      (fun d => ∏ b ∈ (Finset.range d).filter (fun b => Nat.Coprime b d),
        Scheme.Hom.ker ((((b * (N / d) : ℕ) : ℤ) • P₀ : E.Point (𝟙 S)) : S ⟶ E.E))]
    -- (b) per divisor, the totatives scaled by `N/d` enumerate exactly the residues of
    -- additive order `d`.
    refine Finset.prod_congr rfl fun d hd => ?_
    have hdvd : d ∣ N := (Nat.mem_divisors.mp hd).1
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hNd0 : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN hdvd) hd0
    have hmul : d * (N / d) = N := Nat.mul_div_cancel' hdvd
    have hlt : ∀ b ∈ (Finset.range d).filter (fun b => Nat.Coprime b d),
        b * (N / d) < N := fun b hb => by
      calc b * (N / d) < d * (N / d) :=
            (Nat.mul_lt_mul_right hNd0).mpr (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
        _ = N := hmul
    have hval : ∀ b ∈ (Finset.range d).filter (fun b => Nat.Coprime b d),
        (((b * (N / d) : ℕ) : ZMod N)).val = b * (N / d) := fun b hb => by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt b hb)]
    refine Finset.prod_bij
      (fun b _ => (((b * (N / d) : ℕ) : ZMod N)))
      (fun b hb => ?_) (fun b₁ hb₁ b₂ hb₂ h => ?_) (fun x hx => ?_) (fun b hb => ?_)
    · -- lands in the order-`d` fiber
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show N / Nat.gcd ((((b * (N / d) : ℕ) : ZMod N)).val) N = d
      have hbc := (Finset.mem_filter.mp hb).2
      have hgcd : Nat.gcd (b * (N / d)) N = N / d := by
        have h1 : Nat.gcd (b * (N / d)) (d * (N / d)) = N / d := by
          rw [Nat.gcd_mul_right, Nat.coprime_iff_gcd_eq_one.mp hbc, one_mul]
        rwa [hmul] at h1
      rw [hval b hb, hgcd, Nat.div_div_self hdvd hN.ne']
    · -- injective
      have hv := congrArg ZMod.val h
      rw [hval b₁ hb₁, hval b₂ hb₂] at hv
      exact Nat.eq_of_mul_eq_mul_right hNd0 hv
    · -- surjective onto the fiber
      have hx' : N / Nat.gcd x.val N = d := (Finset.mem_filter.mp hx).2
      have hg_dvd : Nat.gcd x.val N ∣ N := Nat.gcd_dvd_right _ _
      have hg : Nat.gcd x.val N = N / d := by
        rw [← hx', Nat.div_div_self hg_dvd hN.ne']
      have hb_lt : x.val / Nat.gcd x.val N < d := by
        conv_rhs => rw [← hx']
        exact Nat.div_lt_div_of_lt_of_dvd hg_dvd (ZMod.val_lt x)
      have hcop : Nat.Coprime (x.val / Nat.gcd x.val N) d := by
        have := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right x.val hN)
        rwa [hx'] at this
      refine ⟨x.val / Nat.gcd x.val N, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hb_lt, hcop⟩, ?_⟩
      rw [← hg, Nat.div_mul_cancel (Nat.gcd_dvd_left x.val N)]
      exact ZMod.natCast_rightInverse x
    · -- term match
      simp only [hK]
      refine congrArg (fun q : E.Point (𝟙 S) => Scheme.Hom.ker (q : S ⟶ E.E)) ?_
      rw [hval b hb]
  rw [hLHS, hRHS, Finset.prod_fiberwise_of_maps_to (fun x _ => hord_mem x) K]

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

/-- The standard cyclic subgroup `G_d` has constant rank `d` (the `degree = d` conjunct
of KM 6.7.2's cyclicity, through the divisor dictionary). -/
theorem _root_.ModularCurves.EllipticCurve.standardCyclicSubgroup_hasRank {N : ℕ}
    [NeZero N] {D : RelEffCartierDiv E.π} (hG : E.IsGammaZeroFppf N D) {d : ℕ}
    [NeZero d] (hd : d ∣ N) : (E.standardCyclicSubgroup hG hd).HasRank d := fun s =>
  ((E.standardCyclicSubgroup hG hd).toRelEffCartierDiv_degree s).symm.trans <| by
    show (FiniteLocallyFreeSubgroup.ofRelEffCartierDiv _ _).toRelEffCartierDiv.degree s = d
    rw [toRelEffCartierDiv_ofRelEffCartierDiv]
    exact (E.standardCyclicDivisor_isGammaZeroFppf hG hd).2.1 s

/-- The killing-integer instance for standard cyclic subgroups: `G_d` is killed by `d`
(KM 1.4.2, through the banked bridge `hasKillingInt_of_hasRank`). Powers the
`[G.HasKillingInt]` hypotheses of the `quotientCurve` layer at every
`standardCyclicSubgroup` call site of §7 — call sites stay textually unchanged (α-lite). -/
instance {N : ℕ} [NeZero N] {D : RelEffCartierDiv E.π} (hG : E.IsGammaZeroFppf N D)
    {d : ℕ} [NeZero d] (hd : d ∣ N) : (E.standardCyclicSubgroup hG hd).HasKillingInt :=
  (E.standardCyclicSubgroup hG hd).hasKillingInt_of_hasRank
    (E.standardCyclicSubgroup_hasRank hG hd)

-- ATTACK: (1) the DATA is the curve record, not just a scheme: `E/G` needs zero section,
-- group law, and the local Weierstrass model — none of which the scheme-level gate
-- provides; making it separate DS-data (rather than pretending `quotient` is a curve)
-- keeps the gate honest. (2) NOT gated on `E[N]`-finite-étale: the construction consumes
-- `G`'s own `finite`/`flat`/`lfp` fields, exactly like the scheme-level quotient.
-- (3) the pin `quotientCurve_compat` ties the total space to the gate's `G.quotient` by a
-- (non-evil) isomorphism under `E`, not a scheme equality — the eventual construction may
-- take `E := G.quotient` on the nose, upgrading the pin to `rfl`-strength, but consumers
-- must not rely on that.
/-- The descended zero section `S ⟶ E/G`: the image of `E`'s zero section under the
quotient isogeny (isogenies are pointed — KM 6.7.6's `E' = E/G` comes with its marked
point `π(0)`). -/
noncomputable def quotientZero (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    S ⟶ G.quotient :=
  E.zero ≫ G.quotientπ

@[reassoc (attr := simp)]
theorem quotientZero_quotientS (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    G.quotientZero ≫ G.quotientS = 𝟙 S := by
  rw [quotientZero, Category.assoc, G.quotientπ_over]
  exact E.zero_π

/-- **(gate [ELLQUOT-GEOM], smoothness)** `E/G ⟶ S` is smooth of relative dimension 1:
smoothness descends along the finite locally free fppf cover `quotientπ` (KM 6.7.6 /
DR IV.1 — the quotient of an elliptic curve by a finite locally free subgroup is again
an elliptic curve). Register-boxed geometry of the E/C layer. -/
theorem quotient_smoothOfRelativeDimension (G : FiniteLocallyFreeSubgroup E)
    [G.HasKillingInt] : SmoothOfRelativeDimension 1 G.quotientS := by
  sorry

/-- **(gate [ELLQUOT-GEOM], properness)** `E/G ⟶ S` is proper: `E ⟶ E/G` is a finite
surjection from the proper `E`, and properness descends along it. -/
theorem quotient_isProper (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    IsProper G.quotientS := by
  sorry

/-- **(gate [ELLQUOT-GEOM], local Weierstrass model)** `E/G` is Zariski-locally on `S` a
projective Weierstrass model — the elliptic-curve-hood of the quotient (KM 6.7.6). The
Hopf-Galois patch quotients of the glue construction supply the affine models; their
projective closures are the Weierstrass presentations. -/
theorem quotient_locallyWeierstrass (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    LocallyWeierstrass G.quotientS G.quotientZero G.quotientZero_quotientS := by
  sorry

/-- **The geometric record of the quotient curve `E/G`** — REAL data on the SIGNAL
scheme: total space `G.quotient`, structure map `G.quotientS`, zero section the
descended `quotientZero`. The three geometry Props are the named [ELLQUOT-GEOM] gates
above; nothing else is pending. -/
noncomputable def quotientCurveGeom (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    EllipticCurveGeom S where
  E := G.quotient
  π := G.quotientS
  zero := G.quotientZero
  zero_π := G.quotientZero_quotientS
  smooth := G.quotient_smoothOfRelativeDimension
  proper := G.quotient_isProper
  localModel := G.quotient_locallyWeierstrass

/-- **DS-NISOG-1, now REAL modulo [ELLQUOT-GEOM] only** — the quotient elliptic curve
`E/G` (KM 6.7.6's target curve `E'`): the **T-W7a enrichment** `toEllipticCurve` of
`quotientCurveGeom`. The group law is the canonical atlas-glued law of the local
Weierstrass models (`GroupLawDescent`), so `grp`/`comm`/`one_eq_zero` carry **no
group-law gate** — the only sorried inputs are the three [ELLQUOT-GEOM] geometry Props.
Consumers use only the pins (`quotientCurve_compat`, `quotientHom_*`, `pointMap_*`). -/
noncomputable def quotientCurve (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    EllipticCurve S :=
  G.quotientCurveGeom.toEllipticCurve

/-- The quotient curve forgets to the quotient geometric record (definitional). -/
@[simp]
theorem quotientCurve_toEllipticCurveGeom (G : FiniteLocallyFreeSubgroup E)
    [G.HasKillingInt] : G.quotientCurve.toEllipticCurveGeom = G.quotientCurveGeom :=
  rfl

/-- **DS-NISOG-2 (GATE [T-G3D-INFRA])** The quotient `N`-isogeny `π : E ⟶ E/G` (KM
6.7.6's `π`): the SIGNAL quotient projection itself, into the quotient curve's total
space (`quotientCurve.E = G.quotient` definitionally). -/
noncomputable def quotientHom (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    E.E ⟶ G.quotientCurve.E :=
  G.quotientπ

/-- **(pin)** The quotient isogeny is a morphism over `S` — direct from the SIGNAL pin
`quotientπ_over`. -/
theorem quotientHom_over (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    G.quotientHom ≫ G.quotientCurve.π = E.π :=
  G.quotientπ_over

/-- **(pin)** The quotient isogeny collapses `G`-translates — direct from the SIGNAL pin
`quotientπ_isInvariant`. -/
theorem quotientHom_isInvariant (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    G.IsInvariant G.quotientHom :=
  G.quotientπ_isInvariant

/-- **(pin)** Compatibility with the scheme-level gate: the quotient curve's total space
IS the [T-G3D-INFRA] quotient scheme (`rfl`-strength — the construction takes
`E := G.quotient` on the nose — but consumers must go through this pin, not `rfl`). -/
theorem quotientCurve_compat (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    ∃ e : G.quotient ≅ G.quotientCurve.E, G.quotientπ ≫ e.hom = G.quotientHom :=
  ⟨Iso.refl _, Category.comp_id _⟩

/-- The point-level map `E(T) ⟶ (E/G)(T)` induced by the quotient isogeny (KM's
`P ↦ π(P)`, e.g. the `π_d P` of 6.7.4/6.7.11). Real definition (composition), over-ness
from the pin `quotientHom_over`. -/
noncomputable def pointMap (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt]
    {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g) : G.quotientCurve.Point g :=
  ⟨x.1 ≫ G.quotientHom, by rw [Category.assoc, G.quotientHom_over]; exact x.2⟩

@[simp]
theorem pointMap_coe (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] {T : Scheme.{u}}
    {g : T ⟶ S} (x : E.Point g) : (G.pointMap x).1 = x.1 ≫ G.quotientHom :=
  rfl

/-- **(pin)** `π` is pointed: the zero section maps to the zero section — REAL: the
quotient curve's zero section is the descended `E.zero ≫ π` by construction. -/
theorem pointMap_zero (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] {T : Scheme.{u}}
    (g : T ⟶ S) : G.pointMap (0 : E.Point g) = 0 := by
  refine Subtype.ext ?_
  rw [pointMap_coe, G.quotientCurve.point_zero_val, E.point_zero_val]
  show (g ≫ E.zero) ≫ G.quotientπ = g ≫ E.zero ≫ G.quotientπ
  rw [Category.assoc]

section OverMonoidal

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

/-- The quotient isogeny as a morphism in `Over S`, from `E` to the quotient curve
(both carrying their group-object structures). -/
noncomputable def quotientHomOver (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    E.asOver ⟶ G.quotientCurve.asOver :=
  Over.homMk G.quotientHom G.quotientHom_over

@[simp]
theorem quotientHomOver_left (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    G.quotientHomOver.left = G.quotientHom :=
  rfl

/-- **The quotient isogeny is pointed**: it carries `E`'s unit to the quotient curve's
unit — both units are the respective zero sections (`one_eq_zero` on both records), and
the quotient's zero section is the descended one by construction. -/
theorem quotientHomOver_one (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    η[E.asOver] ≫ G.quotientHomOver = η[G.quotientCurve.asOver] := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, quotientHomOver_left]
  rw [E.one_eq_zero, G.quotientCurve.one_eq_zero]
  show ((𝟙_ (Over S)).hom ≫ E.zero) ≫ G.quotientπ = (𝟙_ (Over S)).hom ≫ E.zero ≫ G.quotientπ
  rw [Category.assoc]

/-- **The quotient isogeny is a homomorphism** (KM 6.7.6's "`π` is an isogeny"; GIT
Cor 6.4 over the arbitrary base): `μ_E ≫ π = (π ⊗ π) ≫ μ_{E/G}`. REAL modulo the
cross-charter T-W7.8 pin `isMonHom_of_one_comp_eq'_of_finitePresentation` (the
spreading-out form of rigidity): `π` is pointed (`quotientHomOver_one`); `E/S` is
proper, flat, lfp, universally `O`-connected (all in-tree); the quotient curve is
separated + lfp from its [ELLQUOT-GEOM] geometry fields. -/
theorem quotientHomOver_mul (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    μ[E.asOver] ≫ G.quotientHomOver
      = MonoidalCategory.tensorHom G.quotientHomOver G.quotientHomOver
          ≫ μ[G.quotientCurve.asOver] := by
  haveI : Smooth E.π := SmoothOfRelativeDimension.smooth (n := 1) (f := E.π)
  haveI : Smooth G.quotientCurve.π :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := G.quotientCurve.π)
  haveI : IsProper E.asOver.hom := inferInstanceAs (IsProper E.π)
  haveI : Flat E.asOver.hom := inferInstanceAs (Flat E.π)
  haveI : LocallyOfFinitePresentation E.asOver.hom :=
    inferInstanceAs (LocallyOfFinitePresentation E.π)
  haveI : IsSeparated G.quotientCurve.asOver.hom :=
    inferInstanceAs (IsSeparated G.quotientCurve.π)
  haveI : LocallyOfFinitePresentation G.quotientCurve.asOver.hom :=
    inferInstanceAs (LocallyOfFinitePresentation G.quotientCurve.π)
  exact isMonHom_of_one_comp_eq'_of_finitePresentation
    E.toEllipticCurveGeom.universallyOConnected G.quotientHomOver G.quotientHomOver_one

/-- **(pin)** `π` is a homomorphism on `T`-points (the isogeny is a group-scheme map) —
REAL from `quotientHomOver_mul` via the hom-group transport (post-composition with a
`IsMonHom` is a monoid hom of `Over`-hom groups). -/
theorem pointMap_add (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] {T : Scheme.{u}}
    {g : T ⟶ S} (x y : E.Point g) : G.pointMap (x + y) = G.pointMap x + G.pointMap y := by
  letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (Over.mk g ⟶ G.quotientCurve.asOver) := Hom.commGroup
  haveI : IsMonHom G.quotientHomOver :=
    { one_hom := G.quotientHomOver_one, mul_hom := G.quotientHomOver_mul }
  have hcomp : ∀ z : E.Point g,
      E.pointEquivOverHom g z ≫ G.quotientHomOver
        = G.quotientCurve.pointEquivOverHom g (G.pointMap z) := fun z =>
    Over.OverMorphism.ext rfl
  have key := map_mul (IsMonHom.monoidHom G.quotientHomOver (Over.mk g))
    (E.pointEquivOverHom g x) (E.pointEquivOverHom g y)
  simp only [IsMonHom.monoidHom_apply] at key
  refine (G.quotientCurve.pointEquivOverHom g).injective ?_
  rw [← hcomp (x + y), G.quotientCurve.pointEquivOverHom_add, ← hcomp x, ← hcomp y,
    E.pointEquivOverHom_add, key]

end OverMonoidal

/-- **(pin — the kernel specification)** `Ker π = G` (KM 6.7.6: *"a cyclic `N`-isogeny
`π` with kernel `G`"*): a `T`-point of `E` dies in `E/G` iff it lies on `G`. This is the
load-bearing pin for the whole standard-factorization layer. The reverse implication is
REAL from `G`-invariance; the forward half is gate **[QUOT-KER]** (separation — the
fibres of the glued quotient are exactly the `G`-orbits). -/
theorem pointMap_eq_zero_iff (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt]
    {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g) :
    G.pointMap x = 0 ↔ x ∈ G.pointSubgroup g := by
  constructor
  · intro h
    -- [QUOT-KER]: a point collapsing to the zero of `E/G` factors through `G` — the
    -- separation content of the Hopf-Galois glue (KM 6.7.6 "with kernel G").
    sorry
  · intro hx
    have h1 : ((0 : E.Point g) + x).1 ≫ G.quotientπ = (0 : E.Point g).1 ≫ G.quotientπ :=
      G.quotientπ_isInvariant g 0 x hx
    rw [zero_add] at h1
    have h2 : G.pointMap x = G.pointMap 0 := Subtype.ext h1
    rw [h2, G.pointMap_zero]

/-- **(pin — register-box BB-DEG)** The quotient isogeny is finite (half of "`π` is an
isogeny of degree `rank G`"). Degree-side fact of the Hopf–Galois patch structure;
consumed as a register-box per the v10.212/v10.215 rulings (auto-cleans on the BB-DEG
keystone landing). -/
theorem quotientHom_finite (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    IsFinite G.quotientHom := by
  sorry

/-- **(pin — register-box BB-DEG)** The quotient isogeny is flat. -/
theorem quotientHom_flat (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt] :
    Flat G.quotientHom := by
  sorry

/-- **(pin — register-box BB-DEG)** The degree of the quotient isogeny is the rank of
`G` (KM 6.7.6: a cyclic `N`-isogeny has degree `N`). -/
theorem quotientHom_finrank (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt]
    (y : G.quotientCurve.E) :
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
