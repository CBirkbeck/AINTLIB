module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne

/-!
# Lipschitz parametrization of the frontier of `normLeOne K`

Mathlib proves that the frontier of the norm-`≤ 1` part of the fundamental cone has measure
zero (`volume_frontier_normLeOne`). For the *effective* lattice-point count
(`Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`) one needs the stronger,
quantitative regularity: the frontier of the `realSpace` image
`normAtAllPlaces '' (normLeOne K)` is covered by **finitely many Lipschitz images of the unit
cube** `[0,1]^{r-1}`, `r = #InfinitePlace K`. This is the Lipschitz-boundary input of
Gun–Ramaré–Sivaraman, *Counting ideals in ray classes*, J. Number Theory 243 (2023), §3.3
(after Debaene); it feeds the boundary-cell estimate of Widmer / Lang (GTM 110, Ch. V §2).

## Main definitions

* `Chebotarev.clampUnit`: the coordinatewise retraction of `ι → ℝ` onto the unit cube `Icc 0 1`.
* `Chebotarev.faceMapZero`, `Chebotarev.faceMapSide`: cube parametrizations of the `w₀`-face and
  side faces of the box boundary, transported through `expMapBasis`.
* `Chebotarev.frontierCoverFamily`: the finite family covering the `realSpace` frontier.
* `Chebotarev.liftToMixed`: the lift of a `realSpace`-valued cover map to a `mixedSpace`-valued
  one along the fibres of `normAtAllPlaces`.

## Main results

* `Chebotarev.normLeOne_frontier_lipschitz_cover`: the frontier of `normAtAllPlaces '' normLeOne K`
  in `realSpace K` is covered by finitely many `M`-Lipschitz images of `[0,1]^{r-1}`.
* `Chebotarev.normLeOne_frontier_lipschitz_cover_mixedSpace`: the corresponding cover of
  `frontier (normLeOne K)` in `mixedSpace K`, of dimension `d-1 = finrank ℚ K - 1`.
* `Chebotarev.normLeOne_frontier_lipschitz_cover_index`: the cover transported to the standard
  Euclidean coordinate space `index K → ℝ`, the exact `hlip` hypothesis of the lattice-point count.

## Implementation notes

The proof rests entirely on mathlib's parametrization
`normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K)` where
`paramSet K = Iic 0 × [0,1)^{r-1}` (in the `completeBasis` coordinates), in three layers.

The `realSpace` cover:
1. `expMapBasis` is an open injective map (`OpenPartialHomeomorph` with source `univ`), so
   `frontier (expMapBasis '' paramSet K) ⊆ expMapBasis '' (∂ paramSet K) ∪ {0}`, the `{0}`
   accounting for the closure points escaping to norm `0` as the `w₀`-coordinate `→ -∞`
   (`frontier_image_paramSet_subset`).
2. The box boundary `∂ paramSet K` consists of the face `{x w₀ = 0}` and the side faces
   `{x i = a}`, `a ∈ {0,1}`, `i ≠ w₀`.
3. On the `w₀`-face, `expMapBasis` itself restricted to the compact cube parametrizes the
   image (`faceMapZero`). On a side face the `w₀`-direction is unbounded, but
   `expMapBasis x = exp (x w₀) • expMapBasis (x [w₀ => 0])` (`expMapBasis_apply''`), so the
   substitution `t = exp (x w₀) ∈ (0,1]` linearizes it: the face image is parametrized by the
   compact cube via `faceMapSide`, with `t` taking the cube slot freed by pinning `x i = a`.
4. All parametrizations are restrictions of globally `C¹` maps to the compact convex cube,
   hence Lipschitz there (`ContDiff.locallyLipschitz` +
   `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`); composing with the `1`-Lipschitz
   cube clamp `clampUnit` makes them globally Lipschitz without changing the cube image.

The lift to `mixedSpace K` parametrizes the fibres of `normAtAllPlaces`: a fibre over a
nonnegative `y : realSpace K` is fixed by the signs of the real coordinates (a finite choice
folded into the index) and the phases of the complex coordinates (the extra `r₂` cube
coordinates, via the polar form `z = ‖z‖ · exp((2π θ − π) i)`, `θ ∈ [0,1]`). This turns the
`r − 1` cube coordinates into `(r − 1) + r₂ = d − 1` coordinates, `d = finrank ℚ K`.

Finally the cover is transported to the standard coordinate space `index K → ℝ` (sup metric,
lattice `ℤ^ι`) via the continuous linear chart `(stdBasis K).equivFunL`, inflating the Lipschitz
constants by `‖·‖₊` and relabelling the cube dimension along
`Fintype.card (index K) - 1 = finrank ℚ K - 1`.

## References

* Gun, Ramaré, Sivaraman, *Counting ideals in ray classes*, J. Number Theory 243 (2023), §3.3.
* Lang, *Algebraic Number Theory*, GTM 110, Ch. V §2 (Widmer's boundary-cell estimate).
-/

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units dirichletUnitTheorem Set

open scoped NNReal

/-- The coordinatewise retraction of `ι → ℝ` onto the unit cube `Set.Icc 0 1`, given by
`Set.projIcc` in each coordinate. -/
def clampUnit (ι : Type*) (c : ι → ℝ) : ι → ℝ := fun i ↦ (Set.projIcc 0 1 zero_le_one (c i) : ℝ)

theorem clampUnit_mem_Icc (ι : Type*) (c : ι → ℝ) : clampUnit ι c ∈ Icc (0 : ι → ℝ) 1 :=
  ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.1,
    fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.2⟩

theorem clampUnit_eq_self {ι : Type*} {c : ι → ℝ} (hc : c ∈ Icc (0 : ι → ℝ) 1) :
    clampUnit ι c = c :=
  funext fun i ↦ congrArg _ (Set.projIcc_of_mem _ ⟨hc.1 i, hc.2 i⟩)

/-- A map into a finite pi type is `1`-Lipschitz once each output coordinate's `edist` is
bounded by the input `edist`. The pi-codomain companion of `LipschitzWith.eval`. -/
private theorem lipschitzWith_one_of_edist_apply_le {α κ : Type*} {β : κ → Type*}
    [PseudoEMetricSpace α] [∀ j, PseudoEMetricSpace (β j)] [Fintype κ] {F : α → ∀ j, β j}
    (h : ∀ c d j, edist (F c j) (F d j) ≤ edist c d) : LipschitzWith 1 F :=
  LipschitzWith.of_edist_le fun c d ↦ by
    rw [edist_pi_def]
    exact Finset.sup_le fun j _ ↦ h c d j

theorem lipschitzWith_clampUnit (ι : Type*) [Fintype ι] : LipschitzWith 1 (clampUnit ι) :=
  lipschitzWith_one_of_edist_apply_le fun c d i ↦ (Subtype.edist_eq _ _).symm.trans_le <|
    (((LipschitzWith.projIcc zero_le_one).edist_le_mul (c i) (d i)).trans_eq
      (one_mul _)).trans (edist_le_pi_edist c d i)

/-- A globally `C¹` map into `κ → ℝ`, pre-composed with the cube clamp, is globally Lipschitz;
its image of the unit cube is unchanged. The Lipschitz constant comes from compactness of the
cube (`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`). -/
theorem exists_lipschitzWith_comp_clampUnit {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → ℝ) → κ → ℝ} (hf : ContDiff ℝ 1 f) :
    ∃ M : ℝ≥0, LipschitzWith M (f ∘ clampUnit ι) := by
  have hl := hf.locallyLipschitz.locallyLipschitzOn (s := Icc (0 : ι → ℝ) 1)
  obtain ⟨M, hM⟩ := hl.exists_lipschitzOnWith_of_compact isCompact_Icc
  refine ⟨M, fun c d ↦ (hM (clampUnit_mem_Icc ι c) (clampUnit_mem_Icc ι d)).trans ?_⟩
  gcongr
  simpa using (lipschitzWith_clampUnit ι).edist_le_mul c d

variable (K : Type*) [Field K] [NumberField K]

theorem contDiff_expMapBasis {n : WithTop ℕ∞} : ContDiff ℝ n (⇑(expMapBasis (K := K))) := by
  classical
  rw [show ⇑(expMapBasis (K := K)) = fun x : realSpace K ↦
      Real.exp (x w₀) • fun w : InfinitePlace K ↦
        ∏ i : {w // w ≠ w₀}, w (fundSystem K (equivFinRank.symm i)) ^ x i from
    funext expMapBasis_apply']
  fun_prop (disch := exact fun x ↦ (InfinitePlace.pos_iff.mpr (by simp)).ne')

open scoped Classical in
/-- Parametrization of the `expMapBasis`-image of the `w₀`-face `{x | x w₀ = 0}` of
`paramSet K`: plug `0` in the `w₀`-slot and the cube coordinates in the remaining slots. -/
def faceMapZero (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  expMapBasis fun w ↦ if hw : w = w₀ then 0 else c ⟨w, hw⟩

open scoped Classical in
/-- Parametrization of the `expMapBasis`-image of a side face `{x | x i = a}` (`i ≠ w₀`,
`a ∈ {0,1}`) of `paramSet K`. The `w₀`-direction of the face is the unbounded `Iic 0`; the
substitution `t = exp (x w₀) ∈ (0,1]` (`expMapBasis_apply''`) turns it into the cube coordinate
`c i` — the slot freed by pinning `x i = a`:
`faceMapSide i a c = (c i) • expMapBasis (x [w₀ => 0, i => a, w => c w])`. -/
def faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ)
    (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  c i • expMapBasis fun w ↦ if hw : w = w₀ then 0 else if (⟨w, hw⟩ : {w // w ≠ w₀}) = i then a
    else c ⟨w, hw⟩

open scoped Classical in
theorem contDiff_faceMapZero : ContDiff ℝ 1 (faceMapZero K) := by
  refine (contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_)
  by_cases hw : w = w₀
  · simpa only [dif_pos hw] using contDiff_const
  · simpa only [dif_neg hw] using contDiff_apply ℝ ℝ _

open scoped Classical in
theorem contDiff_faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ) :
    ContDiff ℝ 1 (faceMapSide K i a) := by
  refine (contDiff_apply ℝ ℝ i).smul ((contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_))
  by_cases hw : w = w₀
  · simpa only [dif_pos hw] using contDiff_const
  · simp only [dif_neg hw]
    by_cases hi : (⟨w, hw⟩ : {w // w ≠ w₀}) = i
    · simpa only [if_pos hi] using contDiff_const
    · simpa only [if_neg hi] using contDiff_apply ℝ ℝ _

/-- **Topological reduction.** Since `expMapBasis` is open and injective with source `univ`,
the frontier of `expMapBasis '' paramSet K` is contained in the image of the box boundary
`closure (paramSet K) \ interior (paramSet K)`, together with `{0}` (the escape to norm `0`):
`closure (expMapBasis '' paramSet K) ⊆ compactSet K = expMapBasis '' closure (paramSet K) ∪ {0}`
while `expMapBasis '' interior (paramSet K)` is open, hence inside the interior. -/
theorem frontier_image_paramSet_subset :
    frontier (expMapBasis '' paramSet K) ⊆
      expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ∪ {0} := by
  have hcl : closure (expMapBasis '' paramSet K) ⊆ compactSet K :=
    (isCompact_compactSet K).isClosed.closure_subset_iff.mpr
      ((Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet K))
  have hint : expMapBasis '' interior (paramSet K) ⊆ interior (expMapBasis '' paramSet K) :=
    (expMapBasis.isOpen_image_of_subset_source isOpen_interior
      (by simp [expMapBasis_source])).subset_interior_iff.mpr (Set.image_mono interior_subset)
  refine (Set.sdiff_subset_sdiff hcl hint).trans ?_
  rw [compactSet_eq_union, Set.union_sdiff_distrib,
    ← Set.image_sdiff (injective_expMapBasis K)]
  exact Set.union_subset_union_right _ Set.sdiff_subset

open scoped Classical in
private theorem expMapBasis_mem_iUnion_faceMapSide
    {y : realSpace K} {w : InfinitePlace K} (hwe : w ≠ w₀) (hw₀ : y w₀ ≤ 0)
    (hIcc : ∀ v : InfinitePlace K, v ≠ w₀ → y v ∈ Icc (0 : ℝ) 1) (ha : y w = 0 ∨ y w = 1) :
    (expMapBasis y : realSpace K) ∈
      ⋃ i : {w : InfinitePlace K // w ≠ w₀}, ⋃ a ∈ ({0, 1} : Set ℝ),
        faceMapSide K i a '' Icc 0 1 := by
  set i : {w : InfinitePlace K // w ≠ w₀} := ⟨w, hwe⟩ with hi
  set c : {w : InfinitePlace K // w ≠ w₀} → ℝ :=
    fun j ↦ if j = i then Real.exp (y w₀) else y j.1 with hc
  have hcmem : c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 := by
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩ <;> simp only [hc] <;> split_ifs
    · exact Real.exp_nonneg _
    · exact (hIcc j.1 j.2).1
    · exact Real.exp_le_one_iff.mpr hw₀
    · exact (hIcc j.1 j.2).2
  have hkey : faceMapSide K i (y w) c = expMapBasis y := by
    have hci : c i = Real.exp (y w₀) := by simp [hc]
    have hfun : (fun w' ↦ if hw' : w' = w₀ then (0 : ℝ) else
        if (⟨w', hw'⟩ : {w // w ≠ w₀}) = i then y w else c ⟨w', hw'⟩) =
        fun w' ↦ if w' = w₀ then 0 else y w' := by
      funext w'
      by_cases hw'₀ : w' = w₀
      · simp only [dif_pos hw'₀, if_pos hw'₀]
      · simp only [dif_neg hw'₀, if_neg hw'₀]
        by_cases hw'w : (⟨w', hw'₀⟩ : {w // w ≠ w₀}) = i
        · obtain rfl : w' = w := by rw [hi, Subtype.mk_eq_mk] at hw'w; exact hw'w
          simp only [if_pos hw'w]
        · simp only [hc, if_neg hw'w]
    rw [faceMapSide, expMapBasis_apply'' y, hci, hfun]
  refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion₂.mpr ⟨y w, ?_, ⟨c, hcmem, hkey⟩⟩⟩
  rcases ha with h | h <;> simp [h]

/-- **Face covering.** Every point of the image of the box boundary, together with `0`, lies in
a face-parametrization image of the unit cube: a boundary point has `x w₀ = 0` (the `w₀`-face,
covered by `faceMapZero`) or `x i ∈ {0,1}` for some `i ≠ w₀` (a side face, covered by
`faceMapSide i a` via `t = exp (x w₀)`); `0` itself is the `t = 0` slice of any side face, or
the value of the (degenerate, `r = 1`) zero map handled in the final assembly. -/
theorem image_boundary_subset_faces :
    expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ⊆
      faceMapZero K '' Icc 0 1 ∪
        ⋃ i : {w : InfinitePlace K // w ≠ w₀}, ⋃ a ∈ ({0, 1} : Set ℝ),
          faceMapSide K i a '' Icc 0 1 := by
  classical
  rintro _ ⟨y, ⟨hyc, hyni⟩, rfl⟩
  rw [closure_paramSet, Set.mem_univ_pi] at hyc
  rw [interior_paramSet, Set.mem_univ_pi] at hyni
  push Not at hyni
  obtain ⟨w, hw⟩ := hyni
  have hw₀ : y w₀ ≤ 0 := by simpa using hyc w₀
  have hIcc : ∀ v : InfinitePlace K, v ≠ w₀ → y v ∈ Icc (0 : ℝ) 1 := fun v hv ↦ by
    simpa [hv] using hyc v
  by_cases hwe : w = w₀
  · rw [if_pos hwe, Set.mem_Iio, not_lt, hwe] at hw
    have hy0 : y w₀ = 0 := le_antisymm hw₀ hw
    refine Or.inl ⟨fun i ↦ y i.1, ⟨fun i ↦ (hIcc i.1 i.2).1, fun i ↦ (hIcc i.1 i.2).2⟩, ?_⟩
    rw [faceMapZero]
    congr 1
    funext v
    by_cases hv : v = w₀
    · rw [dif_pos hv, hv, hy0]
    · simp only [dif_neg hv]
  · rw [if_neg hwe] at hw
    have h1 := hIcc w hwe
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hw
    refine Or.inr (expMapBasis_mem_iUnion_faceMapSide K hwe hw₀ hIcc ?_)
    rcases hw with h | h
    · exact Or.inl (le_antisymm h h1.1)
    · exact Or.inr (le_antisymm h1.2 h)

/-- Relabel cube coordinates `Fin (#InfinitePlace K - 1) → ℝ` by the non-distinguished places
`{w ≠ w₀}` via `equivFinRank`. -/
def cubeRelabel (c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) :
    {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  fun j ↦ c (equivFinRank.symm j)

open scoped Classical in
theorem lipschitzWith_cubeRelabel : LipschitzWith 1 (cubeRelabel K) :=
  lipschitzWith_one_of_edist_apply_le (F := cubeRelabel K)
    fun c d j ↦ edist_le_pi_edist c d (equivFinRank.symm j)

theorem cubeRelabel_mem_Icc {c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ}
    (hc : c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1) :
    cubeRelabel K c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
  ⟨fun _ ↦ hc.1 _, fun _ ↦ hc.2 _⟩

theorem exists_cubeRelabel_eq {c' : {w : InfinitePlace K // w ≠ w₀} → ℝ}
    (hc' : c' ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1) :
    ∃ c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1, cubeRelabel K c = c' :=
  ⟨fun j ↦ c' (equivFinRank j), ⟨fun j ↦ hc'.1 _, fun j ↦ hc'.2 _⟩,
    funext fun j ↦ by simp [cubeRelabel]⟩

/-- The finite family covering the frontier: the zero map (index `inl ()`), the `w₀`-face map
(`inr (inl ())`), and the side-face maps `faceMapSide i a` for `i ≠ w₀`, `a ∈ {0,1}`
(`inr (inr (i, b))`, `a = if b then 1 else 0`), each post-clamped to the unit cube and relabelled
through `cubeRelabel`. -/
def frontierCoverFamily :
    (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) →
      (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K :=
  Sum.elim (fun _ _ ↦ 0)
    (Sum.elim (fun _ ↦ faceMapZero K ∘ clampUnit _ ∘ cubeRelabel K)
      fun p ↦ faceMapSide K p.1 (if p.2 then 1 else 0) ∘ clampUnit _ ∘ cubeRelabel K)

/-- Every member of `frontierCoverFamily` is `M`-Lipschitz for a common constant `M`: each face
map is `C¹` on the compact cube hence Lipschitz there (`exists_lipschitzWith_comp_clampUnit`), and
pre-composing with the `1`-Lipschitz `cubeRelabel` preserves the constant; take `M` to be the
supremum over the finitely many faces. -/
theorem exists_lipschitzWith_frontierCoverFamily :
    ∃ M : ℝ≥0, ∀ s, LipschitzWith M (frontierCoverFamily K s) := by
  classical
  obtain ⟨M₀, hM₀⟩ := exists_lipschitzWith_comp_clampUnit (contDiff_faceMapZero K)
  choose Ms hMs using fun p : {w : InfinitePlace K // w ≠ w₀} × Bool ↦
    exists_lipschitzWith_comp_clampUnit (contDiff_faceMapSide K p.1 (if p.2 then 1 else 0))
  refine ⟨M₀ ⊔ Finset.univ.sup Ms, fun s ↦ ?_⟩
  rcases s with _ | _ | p
  · exact (LipschitzWith.const _).weaken zero_le
  · exact (hM₀.comp (lipschitzWith_cubeRelabel K)).weaken (by rw [mul_one]; exact le_sup_left)
  · exact ((hMs p).comp (lipschitzWith_cubeRelabel K)).weaken
      (by rw [mul_one]; exact le_sup_of_le_right (Finset.le_sup (Finset.mem_univ p)))

/-- The frontier of `normAtAllPlaces '' normLeOne K` is covered by the cube images of
`frontierCoverFamily`. The chain is: frontier → box-boundary image `∪ {0}`
(`frontier_image_paramSet_subset`) → the face images (`image_boundary_subset_faces`), then each
face image is the corresponding family member after undoing the relabelling
(`exists_cubeRelabel_eq`) and the clamp (`clampUnit_eq_self`), with `{0}` the value of the zero
map. -/
theorem frontier_subset_frontierCoverFamily :
    frontier (normAtAllPlaces '' normLeOne K) ⊆
      ⋃ s, frontierCoverFamily K s '' Icc 0 1 := by
  classical
  rw [normAtAllPlaces_normLeOne_eq_image]
  refine (frontier_image_paramSet_subset K).trans
    (Set.union_subset ((image_boundary_subset_faces K).trans (Set.union_subset ?_ ?_)) ?_)
  · rintro x ⟨c', hc', rfl⟩
    obtain ⟨c, hc, rfl⟩ := exists_cubeRelabel_eq K hc'
    refine Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inl ()), c, hc, ?_⟩
    change faceMapZero K (clampUnit _ (cubeRelabel K c)) = faceMapZero K (cubeRelabel K c)
    rw [clampUnit_eq_self (cubeRelabel_mem_Icc K hc)]
  · rintro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, a, ha, c', hc', rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := exists_cubeRelabel_eq K hc'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    obtain ⟨b, rfl⟩ : ∃ b : Bool, (if b then (1 : ℝ) else 0) = a := by
      rcases ha with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    refine Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inr (i, b)), c, hc, ?_⟩
    change faceMapSide K i (if b then (1 : ℝ) else 0) (clampUnit _ (cubeRelabel K c)) = _
    rw [clampUnit_eq_self (cubeRelabel_mem_Icc K hc)]
  · rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_iUnion.mpr ⟨Sum.inl (), 0, ⟨le_rfl, fun _ ↦ zero_le_one⟩, rfl⟩

/-- **The Lipschitz cover of the frontier of `normAtAllPlaces '' (normLeOne K)`**
(Gun–Ramaré–Sivaraman §3.3, after Debaene). This is the exact `hlip` regularity hypothesis of
the effective lattice-point count `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`,
specialized to the ideal-counting region: finitely many `M`-Lipschitz maps from
`[0,1]^{r-1}`, `r = #InfinitePlace K`, whose cube images cover the frontier. -/
theorem normLeOne_frontier_lipschitz_cover :
    ∃ (m : ℕ) (M : ℝ≥0)
      (φ : Fin m → (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K),
      (∀ j, LipschitzWith M (φ j)) ∧
        frontier (normAtAllPlaces '' normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1 := by
  classical
  obtain ⟨M, hM⟩ := exists_lipschitzWith_frontierCoverFamily K
  set e := Fintype.equivFin (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool))
  refine ⟨_, M, fun j ↦ frontierCoverFamily K (e.symm j), fun j ↦ hM _, ?_⟩
  rw [e.symm.surjective.iUnion_comp fun s ↦ frontierCoverFamily K s '' Icc 0 1]
  exact frontier_subset_frontierCoverFamily K

/-- The product distance estimate `dist (a u) (b v) ≤ ‖a‖ · dist u v + ‖v‖ · dist a b` in a
normed field, splitting `a u − b v = a (u − v) + (a − b) v`. -/
theorem dist_mul_le_norm_mul_dist {α : Type*} [NormedField α] (a b u v : α) :
    dist (a * u) (b * v) ≤ ‖a‖ * dist u v + ‖v‖ * dist a b := by
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm,
    show a * u - b * v = a * (u - v) + (a - b) * v by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, mul_comm ‖a - b‖ ‖v‖]

/-- The unit-circle exponential `t ↦ exp(t i)` is globally `1`-Lipschitz: it is `circleMap 0 1`,
which is `|R| = 1`-Lipschitz by `lipschitzWith_circleMap`. -/
theorem lipschitzWith_exp_ofReal_mul_I :
    LipschitzWith 1 (fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) := by
  rw [show (fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) = circleMap 0 1 from
    funext fun t ↦ by simp [circleMap]]
  simpa using lipschitzWith_circleMap 0 1

/-- The phase reparametrization `θ ↦ exp((2π θ − π) i)` is `2π`-Lipschitz: it is the
unit-circle exponential (`1`-Lipschitz) composed with the `2π`-Lipschitz affine map
`θ ↦ 2π θ − π`. -/
theorem lipschitzWith_phase :
    LipschitzWith (2 * Real.pi).toNNReal
      (fun t : ℝ ↦
        Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ)) * Complex.I)) := by
  have haff : LipschitzWith (2 * Real.pi).toNNReal (fun t : ℝ ↦ 2 * Real.pi * t - Real.pi) := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity),
      show 2 * Real.pi * x - Real.pi - (2 * Real.pi * y - Real.pi) = 2 * Real.pi * (x - y) by
        ring, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hcomp : (fun t : ℝ ↦
        Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ)) * Complex.I))
      = (fun s : ℝ ↦ Complex.exp ((s : ℂ) * Complex.I))
        ∘ (fun t : ℝ ↦ 2 * Real.pi * t - Real.pi) := by
    funext t
    simp only [Function.comp_apply]
    push_cast
    ring_nf
  rw [hcomp, ← one_mul (2 * Real.pi).toNNReal]
  exact lipschitzWith_exp_ofReal_mul_I.comp haff

/-- The per-place phase-modulus distance bound: with `uθ = exp((2π θ − π) i)`,
`dist (a uθc) (b uθd) ≤ ‖a‖ · (2π · dist θc θd) + dist a b`, using `‖uθd‖ = 1` and the
`2π`-Lipschitz phase. -/
theorem dist_mul_exp_phase_le (a b θc θd : ℝ) :
    dist ((a : ℂ) * Complex.exp ((2 * (Real.pi : ℂ) * (θc : ℂ) - (Real.pi : ℂ)) * Complex.I))
        ((b : ℂ) * Complex.exp ((2 * (Real.pi : ℂ) * (θd : ℂ) - (Real.pi : ℂ)) * Complex.I))
      ≤ ‖(a : ℂ)‖ * (2 * Real.pi * dist θc θd) + dist (a : ℂ) (b : ℂ) := by
  set ud := Complex.exp ((2 * (Real.pi : ℂ) * (θd : ℂ) - (Real.pi : ℂ)) * Complex.I) with hud
  refine (dist_mul_le_norm_mul_dist _ _ _ _).trans ?_
  have hav : ‖ud‖ = 1 := by
    rw [hud, Complex.norm_exp, show ((2 * (Real.pi : ℂ) * (θd : ℂ) - (Real.pi : ℂ)) *
      Complex.I).re = 0 by simp, Real.exp_zero]
  have hphase : dist (Complex.exp ((2 * (Real.pi : ℂ) * (θc : ℂ) - (Real.pi : ℂ)) * Complex.I)) ud
      ≤ 2 * Real.pi * dist θc θd := by
    have h := lipschitzWith_phase.dist_le_mul θc θd
    rwa [Real.coe_toNNReal _ (by positivity)] at h
  rw [hav, one_mul]
  gcongr

/-- Polar parametrization of a complex coordinate by a phase in the unit interval: every
`z : ℂ` equals `‖z‖ · exp((2π θ − π) i)` for some `θ ∈ [0,1]` (`θ = (arg z + π)/(2π)`, lying in
`(0,1]` since `arg z ∈ (−π, π]`). -/
theorem exists_phase_mem_Icc_mul_exp (z : ℂ) :
    ∃ θ : ℝ, θ ∈ Icc (0 : ℝ) 1 ∧
      (‖z‖ : ℂ) * Complex.exp ((2 * Real.pi * θ - Real.pi) * Complex.I) = z := by
  refine ⟨(z.arg + Real.pi) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (by linarith [Complex.neg_pi_lt_arg z]) (by positivity)
  · rw [div_le_one (by positivity)]
    linarith [Complex.arg_le_pi z]
  · have hreal : (2 * Real.pi * ((z.arg + Real.pi) / (2 * Real.pi)) - Real.pi : ℝ) = z.arg := by
      field_simp
      ring
    rw [show ((2 : ℂ) * (Real.pi : ℂ) * (((z.arg + Real.pi) / (2 * Real.pi) : ℝ) : ℂ)
          - (Real.pi : ℂ))
        = ((2 * Real.pi * ((z.arg + Real.pi) / (2 * Real.pi)) - Real.pi : ℝ) : ℂ) by
          push_cast; ring, hreal]
    exact Complex.norm_mul_exp_arg_mul_I z

open scoped Classical in
/-- The lift splits the `d − 1` cube coordinates into the `r − 1 = #InfinitePlace K − 1`
"modulus" coordinates (fed to a `realSpace`-valued cover map) and the `r₂` "phase" coordinates
(one per complex place). The cardinalities match: `(d − 1) = (r − 1) + r₂` follows from
`r₁ + 2 r₂ = d` (`card_add_two_mul_card_eq_rank`) and `r = r₁ + r₂`
(`card_eq_nrRealPlaces_add_nrComplexPlaces`), with `r ≥ 1` (`Fintype.card_pos`). -/
noncomputable def mixedCubeEquiv : Fin (Module.finrank ℚ K - 1)
    ≃ Fin (Fintype.card (InfinitePlace K) - 1) ⊕ {w : InfinitePlace K // IsComplex w} := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have h1 : Fintype.card (InfinitePlace K) = nrRealPlaces K + nrComplexPlaces K :=
    card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h2 : nrRealPlaces K + 2 * nrComplexPlaces K = Module.finrank ℚ K :=
    card_add_two_mul_card_eq_rank K
  have hpos : 1 ≤ Fintype.card (InfinitePlace K) := Fintype.card_pos
  have h3 : nrComplexPlaces K = Fintype.card {w : InfinitePlace K // IsComplex w} := rfl
  lia

/-- Lift a `realSpace`-valued cover map `ψ` to a `mixedSpace`-valued map, using the first
`r − 1` cube coordinates as the modulus input to `ψ` and the last `r₂` coordinates as the phases
of the complex places, with the real places carrying the sign pattern `ε`.

At a real place `w` the coordinate is `± (ψ ·) w`; at a complex place `w` it is
`(ψ ·) w · exp((2π θ_w − π) i)`. By construction `normAtAllPlaces (liftToMixed ψ ε c) = ψ (…)`
whenever the modulus values `(ψ ·) w` are nonnegative. -/
noncomputable def liftToMixed (ψ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K)
    (ε : {w : InfinitePlace K // IsReal w} → Bool)
    (c : Fin (Module.finrank ℚ K - 1) → ℝ) : mixedSpace K :=
  (fun w : {w : InfinitePlace K // IsReal w} ↦
      (if ε w then (1 : ℝ) else -1) * ψ (fun i ↦ c ((mixedCubeEquiv K).symm (Sum.inl i))) w.1,
    fun w : {w : InfinitePlace K // IsComplex w} ↦
      (ψ (fun i ↦ c ((mixedCubeEquiv K).symm (Sum.inl i))) w.1 : ℂ) *
        Complex.exp ((2 * Real.pi * c ((mixedCubeEquiv K).symm (Sum.inr w)) - Real.pi) *
          Complex.I))

open scoped Classical in
/-- If the cover map `ψ` is `M₀`-Lipschitz and uniformly bounded by `B` on the cube image, then
its lift `liftToMixed K ψ ε` is globally Lipschitz. The real coordinates are isometric copies of
`ψ`-coordinates (`M₀`); a complex coordinate `(ψ ·) w · exp((2π θ − π) i)` is bounded by the
product estimate `dist (a u) (b v) ≤ ‖a‖ · dist u v + ‖v‖ · dist a b`, contributing
`B · 2π` from the phase (`lipschitzWith_exp_ofReal_mul_I`) and `M₀` from the modulus. -/
theorem lipschitzWith_liftToMixed {ψ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K}
    {M₀ : ℝ≥0} {B : ℝ} (hψ : LipschitzWith M₀ ψ) (hB : ∀ c, ‖ψ c‖ ≤ B)
    (ε : {w : InfinitePlace K // IsReal w} → Bool) :
    LipschitzWith (M₀ + (B * (2 * Real.pi)).toNNReal) (liftToMixed K ψ ε) := by
  have hBnn : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  set N : ℝ≥0 := M₀ + (B * (2 * Real.pi)).toNNReal with hN
  refine LipschitzWith.of_dist_le_mul fun c d ↦ ?_
  set yc : realSpace K := ψ (fun i ↦ c ((mixedCubeEquiv K).symm (Sum.inl i))) with hyc
  set yd : realSpace K := ψ (fun i ↦ d ((mixedCubeEquiv K).symm (Sum.inl i))) with hyd
  have hmod : dist yc yd ≤ M₀ * dist c d := by
    rw [hyc, hyd]
    refine (hψ.dist_le_mul _ _).trans ?_
    gcongr
    exact (dist_pi_le_iff dist_nonneg).mpr fun i ↦ dist_le_pi_dist c d _
  have hmodc : ∀ w : InfinitePlace K, dist (yc w) (yd w) ≤ M₀ * dist c d :=
    fun w ↦ (dist_le_pi_dist yc yd w).trans hmod
  have hyB : ∀ w : InfinitePlace K, ‖(yc w : ℂ)‖ ≤ B := fun w ↦ by
    rw [Complex.norm_real]
    exact (norm_le_pi_norm yc w).trans (hB _)
  rw [liftToMixed, liftToMixed, Prod.dist_eq]
  refine max_le ((dist_pi_le_iff (by positivity)).mpr fun w ↦ ?_)
    ((dist_pi_le_iff (by positivity)).mpr fun w ↦ ?_)
  · have hsign : dist ((if ε w then (1 : ℝ) else -1) * yc w.1)
        ((if ε w then (1 : ℝ) else -1) * yd w.1) = dist (yc w.1) (yd w.1) := by
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      split_ifs <;> simp
    rw [hsign]
    refine (hmodc w.1).trans ?_
    gcongr
    rw [hN]
    exact_mod_cast le_self_add
  · refine (dist_mul_exp_phase_le (yc w.1) (yd w.1) _ _).trans ?_
    have hmodcw : dist (yc w.1 : ℂ) (yd w.1 : ℂ) ≤ M₀ * dist c d := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        ← Real.dist_eq]
      exact hmodc w.1
    calc ‖(yc w.1 : ℂ)‖ * (2 * Real.pi * dist (c ((mixedCubeEquiv K).symm (Sum.inr w)))
            (d ((mixedCubeEquiv K).symm (Sum.inr w)))) + dist (yc w.1 : ℂ) (yd w.1 : ℂ)
        ≤ B * (2 * Real.pi * dist c d) + M₀ * dist c d := by
          gcongr
          · exact hyB w.1
          · exact dist_le_pi_dist c d _
      _ = (↑M₀ + ↑(B * (2 * Real.pi)).toNNReal) * dist c d := by
          rw [Real.coe_toNNReal _ (by positivity)]
          ring
      _ = ↑N * dist c d := by rw [hN, NNReal.coe_add]

/-- Every member of `frontierCoverFamily` is **globally bounded** by a single constant `B`:
each face map is continuous and is only ever evaluated on the compact cube (the clamp
`clampUnit` lands in `Icc 0 1`), so its range is bounded; take the supremum over the finitely
many faces. This is the boundedness hypothesis feeding `lipschitzWith_liftToMixed`. -/
theorem exists_bound_frontierCoverFamily :
    ∃ B : ℝ, ∀ s c, ‖frontierCoverFamily K s c‖ ≤ B := by
  classical
  have hbd : ∀ (g : ({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K),
      Continuous g → ∃ B : ℝ, ∀ c, ‖g (clampUnit _ (cubeRelabel K c))‖ ≤ B := by
    intro g hg
    obtain ⟨B, hB⟩ := (isCompact_Icc.image hg).isBounded.subset_closedBall 0
    refine ⟨B, fun c ↦ ?_⟩
    have := hB (mem_image_of_mem g (clampUnit_mem_Icc _ (cubeRelabel K c)))
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  obtain ⟨B₀, hB₀⟩ := hbd _ (contDiff_faceMapZero K).continuous
  choose Bs hBs using fun p : {w : InfinitePlace K // w ≠ w₀} × Bool ↦
    hbd _ (contDiff_faceMapSide K p.1 (if p.2 then 1 else 0)).continuous
  refine ⟨↑(B₀.toNNReal ⊔ Finset.univ.sup fun p ↦ (Bs p).toNNReal), fun s c ↦ ?_⟩
  rcases s with _ | _ | p
  · simp only [frontierCoverFamily, Sum.elim_inl, norm_zero]
    positivity
  · refine (hB₀ c).trans <| (Real.le_coe_toNNReal B₀).trans ?_
    exact_mod_cast le_sup_left
  · refine (hBs p c).trans <| (Real.le_coe_toNNReal (Bs p)).trans ?_
    exact_mod_cast le_sup_of_le_right (Finset.le_sup (f := fun q ↦ (Bs q).toNNReal)
      (Finset.mem_univ p))

/-- **Fibre covering.** If a point `y` of the `realSpace` frontier cover is `normAtAllPlaces x`,
then `x` lies in the cube image of `liftToMixed K ψ ε` for the sign pattern `ε` reading off the
signs of the real coordinates of `x`: the modulus coordinates `(ψ ·) w = normAtPlace w x` are the
absolute values / norms of the coordinates of `x`, and the phases come from the polar form of the
complex coordinates (`exists_phase_mem_Icc_mul_exp`). -/
theorem mem_iUnion_image_liftToMixed_of_eq
    {ψ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K}
    {c' : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ} (hc' : c' ∈ Icc (0 : _) 1)
    {x : mixedSpace K} (hx : normAtAllPlaces x = ψ c') :
    x ∈ ⋃ ε : {w : InfinitePlace K // IsReal w} → Bool, liftToMixed K ψ ε '' Icc 0 1 := by
  choose θ hθmem hθeq using fun w : {w : InfinitePlace K // IsComplex w} ↦
    exists_phase_mem_Icc_mul_exp (x.2 w)
  set ε : {w : InfinitePlace K // IsReal w} → Bool := fun w ↦ decide (0 ≤ x.1 w) with hε
  set c : Fin (Module.finrank ℚ K - 1) → ℝ :=
    fun k ↦ Sum.elim c' θ (mixedCubeEquiv K k) with hc
  have hproj : (fun i ↦ c ((mixedCubeEquiv K).symm (Sum.inl i))) = c' := by
    funext i
    simp [hc]
  have hck : ∀ k, c k ∈ Icc (0 : ℝ) 1 := fun k ↦ by
    change Sum.elim c' θ (mixedCubeEquiv K k) ∈ Icc (0 : ℝ) 1
    rcases mixedCubeEquiv K k with i | w
    · exact ⟨hc'.1 i, hc'.2 i⟩
    · exact hθmem w
  refine Set.mem_iUnion.mpr ⟨ε, c, ⟨fun k ↦ (hck k).1, fun k ↦ (hck k).2⟩, ?_⟩
  rw [liftToMixed, hproj]
  have hcph : ∀ w : {w : InfinitePlace K // IsComplex w},
      c ((mixedCubeEquiv K).symm (Sum.inr w)) = θ w := fun w ↦ by rw [hc]; simp
  have hmodreal : ∀ w : {w : InfinitePlace K // IsReal w}, ψ c' w.1 = |x.1 w| := fun w ↦ by
    rw [← hx, normAtAllPlaces_apply, normAtPlace_apply_of_isReal w.2, ← Real.norm_eq_abs]
  have hmodcplx : ∀ w : {w : InfinitePlace K // IsComplex w}, ψ c' w.1 = ‖x.2 w‖ :=
    fun w ↦ by rw [← hx, normAtAllPlaces_apply, normAtPlace_apply_of_isComplex w.2]
  refine Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_)
  · simp only [hε, hmodreal w]
    by_cases hpos : 0 ≤ x.1 w
    · rw [decide_eq_true hpos, if_pos rfl, one_mul, abs_of_nonneg hpos]
    · rw [decide_eq_false hpos, if_neg (by simp), abs_of_neg (not_le.mp hpos)]
      ring
  · simp only [hcph w, hmodcplx w]
    exact hθeq w

/-- The frontier of `normLeOne K` in `mixedSpace K` is contained in the `normAtAllPlaces`-preimage
of the frontier of its `realSpace` image: `normLeOne K` is the preimage of its image
(`normLeOne_eq_preimage_image`), and `normAtAllPlaces` is continuous, so
`frontier (f ⁻¹' s) ⊆ f ⁻¹' (frontier s)` (`Continuous.frontier_preimage_subset`). -/
theorem frontier_normLeOne_subset_preimage :
    frontier (normLeOne K) ⊆
      normAtAllPlaces ⁻¹' frontier (normAtAllPlaces '' normLeOne K) := by
  conv_lhs => rw [normLeOne_eq_preimage_image K]
  exact (continuous_normAtAllPlaces K).frontier_preimage_subset _

open scoped Classical in
private theorem frontier_normLeOne_subset_iUnion_image_liftToMixed_aux :
    frontier (normLeOne K) ⊆
      ⋃ p : (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) ×
        ({w : InfinitePlace K // IsReal w} → Bool),
        liftToMixed K (frontierCoverFamily K p.1) p.2 '' Icc 0 1 := by
  refine (frontier_normLeOne_subset_preimage K).trans ?_
  refine (Set.preimage_mono (frontier_subset_frontierCoverFamily K)).trans ?_
  rw [Set.preimage_iUnion]
  refine Set.iUnion_subset fun s ↦ ?_
  rintro x ⟨c', hc', hxeq⟩
  obtain ⟨ε, hε⟩ := Set.mem_iUnion.mp
    (mem_iUnion_image_liftToMixed_of_eq (ψ := frontierCoverFamily K s) (c' := c')
      (hc' := hc') (x := x) (hx := hxeq.symm))
  exact Set.mem_iUnion.mpr ⟨(s, ε), hε⟩

open scoped Classical in
/-- **The Lipschitz cover of the frontier of `normLeOne K` in `mixedSpace K`.** Lifting the
`realSpace` frontier cover (`normLeOne_frontier_lipschitz_cover`) along the fibres of
`normAtAllPlaces`: the real-place signs are folded into a finite index together with the existing
faces, and the complex-place phases supply the extra `r₂` cube coordinates, giving
`(r − 1) + r₂ = d − 1` coordinates (`d = finrank ℚ K`). This is the `mixedSpace`-level boundary
regularity needed for the lattice-point count in the mixed embedding. -/
theorem normLeOne_frontier_lipschitz_cover_mixedSpace :
    ∃ (m : ℕ) (M : ℝ≥0)
      (φ : Fin m → (Fin (Module.finrank ℚ K - 1) → ℝ) → mixedSpace K),
      (∀ j, LipschitzWith M (φ j)) ∧
        frontier (normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1 := by
  obtain ⟨M₀, hM₀⟩ := exists_lipschitzWith_frontierCoverFamily K
  obtain ⟨B, hB⟩ := exists_bound_frontierCoverFamily K
  set S := (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) ×
    ({w : InfinitePlace K // IsReal w} → Bool)
  set Φ : S → (Fin (Module.finrank ℚ K - 1) → ℝ) → mixedSpace K :=
    fun p ↦ liftToMixed K (frontierCoverFamily K p.1) p.2
  set e := Fintype.equivFin S
  refine ⟨_, M₀ + (B * (2 * Real.pi)).toNNReal, fun j ↦ Φ (e.symm j),
    fun j ↦ lipschitzWith_liftToMixed (hψ := hM₀ _) (hB := hB _) (ε := _), ?_⟩
  rw [e.symm.surjective.iUnion_comp fun p ↦ Φ p '' Icc 0 1]
  exact frontier_normLeOne_subset_iUnion_image_liftToMixed_aux K

open scoped Classical in
/-- **The Lipschitz frontier cover of `normLeOne K`, transported to `index K → ℝ`.** The frontier
of the `stdBasis`-coordinate image `Φ '' normLeOne K` (with `Φ = (stdBasis K).equivFunL`) is
covered by finitely many Lipschitz images of the unit cube `[0,1]^{#(index K) − 1}`. This is the
exact `hlip` regularity hypothesis of `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` with
`ι = index K`, obtained from `normLeOne_frontier_lipschitz_cover_mixedSpace` by post-composing the
charts with the continuous-linear `Φ` (Lipschitz, frontier-preserving as a homeomorphism) and
relabelling the cube dimension via `Fintype.card (index K) − 1 = finrank ℚ K − 1`. -/
theorem normLeOne_frontier_lipschitz_cover_index :
    ∃ (m : ℕ) (M : ℝ≥0)
      (φ : Fin m → (Fin (Fintype.card (index K) - 1) → ℝ) → (index K → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧
        frontier ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K)) ⊆
          ⋃ j, φ j '' Icc 0 1 := by
  obtain ⟨m, M, φ, hφ, hcov⟩ := normLeOne_frontier_lipschitz_cover_mixedSpace K
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL
  set g : Fin (Fintype.card (index K) - 1) ≃ Fin (Module.finrank ℚ K - 1) := finCongr (by
    rw [← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K), mixedEmbedding.finrank])
  refine ⟨m, ‖(Φ : mixedSpace K →L[ℝ] (index K → ℝ))‖₊ * (M * 1),
    fun j c ↦ Φ (φ j (fun a ↦ c (g.symm a))),
    fun j ↦ Φ.lipschitz.comp ((hφ j).comp
      (IsometryEquiv.piCongrLeft' (Y := fun _ ↦ ℝ) g).isometry.lipschitz), ?_⟩
  rw [← Φ.coe_toHomeomorph, ← Φ.toHomeomorph.image_frontier]
  refine (Set.image_mono hcov).trans ?_
  rw [Set.image_iUnion]
  refine Set.iUnion_subset fun j ↦ ?_
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  exact Set.mem_iUnion.mpr ⟨j, ⟨fun a ↦ c (g a), ⟨fun a ↦ hc.1 _, fun a ↦ hc.2 _⟩, by
    simp⟩⟩

end Chebotarev
