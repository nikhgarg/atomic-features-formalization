import PKG26AtomicFeatures.SparseCodeGeometry

/-!
# Stable intersections of sparse support spaces

The coordinate-deletion argument in
`docs/STABLE_SPARSE_TAIL_AND_SUBSPACE_RECOVERY.md`, equations (8) and (9).
The error bound depends on the sparsity order and decoding margin, but not
on the number of supports being intersected.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators

/-- The coordinates common to every member of an indexed finite support
family. The empty family has the full coordinate set as its intersection. -/
noncomputable def supportFamilyIntersection {ι : Type*} {M : ℕ}
    (supports : ι → Finset (Fin M)) (family : Finset ι) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter fun i => ∀ s ∈ family, i ∈ supports s

@[simp] theorem mem_supportFamilyIntersection {ι : Type*} {M : ℕ}
    (supports : ι → Finset (Fin M)) (family : Finset ι) (i : Fin M) :
    i ∈ supportFamilyIntersection supports family ↔
      ∀ s ∈ family, i ∈ supports s := by
  classical
  simp [supportFamilyIntersection]

/-- If a point has a reconstruction of error at most `δ` on each of a
nonempty family of supports of size at most `K`, it has a reconstruction on
their intersection with error at most `(1 + 2K/γ)δ`. The proof compares all
codes to one fixed code and deletes its coordinates outside the intersection.
In particular, there is no factor depending on the number of supports. -/
theorem exists_code_on_support_intersection_of_residuals
    {ι : Type*} {d M K : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ δ : ℝ)
    (hunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hstable : SparseLowerStable B γ (2 * K)) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (supports : ι → Finset (Fin M)) (family : Finset ι)
    (hne : family.Nonempty) (hcard : ∀ s ∈ family, (supports s).card ≤ K)
    (x : EuclideanRepresentation d)
    (hcodes : ∀ s ∈ family, ∃ u : FeatureVector M,
      nonzeroSupport u ⊆ supports s ∧
        ‖x - representationToEuclidean d (B.mulVec u)‖ ≤ δ) :
    ∃ v : FeatureVector M,
      nonzeroSupport v ⊆ supportFamilyIntersection supports family ∧
        ‖x - representationToEuclidean d (B.mulVec v)‖ ≤
          (1 + 2 * (K : ℝ) / γ) * δ := by
  classical
  obtain ⟨s₀, hs₀⟩ := hne
  obtain ⟨u₀, hu₀, herr₀⟩ := hcodes s₀ hs₀
  have hu₀card : (nonzeroSupport u₀).card ≤ K :=
    (Finset.card_le_card hu₀).trans (hcard s₀ hs₀)
  let I := supportFamilyIntersection supports family
  have hsmall : ∀ i, i ∉ I → |u₀ i| ≤ 2 * δ / γ := by
    intro i hi
    have hout : ¬ ∀ s ∈ family, i ∈ supports s := by
      simpa only [I, mem_supportFamilyIntersection] using hi
    push Not at hout
    obtain ⟨s, hs, his⟩ := hout
    obtain ⟨u, hu, herr⟩ := hcodes s hs
    have hui : u i = 0 := by
      by_contra hn
      exact his (hu ((mem_nonzeroSupport_iff u i).mpr hn))
    have hucard : (nonzeroSupport u).card ≤ K :=
      (Finset.card_le_card hu).trans (hcard s hs)
    have hdist : γ * ‖representationToEuclidean M (u₀ - u)‖ ≤ 2 * δ := by
      calc
        _ ≤ ‖representationToEuclidean d (B.mulVec u₀) -
            representationToEuclidean d (B.mulVec u)‖ := by
          simpa only [map_sub] using hstable.code_distance u₀ u hu₀card hucard
        _ ≤ ‖representationToEuclidean d (B.mulVec u₀) - x‖ +
            ‖x - representationToEuclidean d (B.mulVec u)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ δ + δ := add_le_add (by simpa only [norm_sub_rev] using herr₀) herr
        _ = 2 * δ := by ring
    have hcoordinate := abs_coordinate_sub_le_euclidean_norm u₀ u i
    rw [hui, sub_zero] at hcoordinate
    apply (le_div_iff₀ hγ).mpr
    nlinarith
  let v : FeatureVector M := fun i => if i ∈ I then u₀ i else 0
  have hv : nonzeroSupport v ⊆ I := by
    intro i hi
    by_contra hn
    exact (mem_nonzeroSupport_iff v i).mp hi (by simp [v, hn])
  have hdeleted : nonzeroSupport (u₀ - v) ⊆ nonzeroSupport u₀ := by
    intro i hi
    apply (mem_nonzeroSupport_iff u₀ i).mpr
    intro hz
    exact (mem_nonzeroSupport_iff (u₀ - v) i).mp hi (by simp [v, hz])
  have hdeleted_card : (nonzeroSupport (u₀ - v)).card ≤ K :=
    (Finset.card_le_card hdeleted).trans hu₀card
  have hdeleted_bound : ∀ i, |(u₀ - v) i| ≤ 2 * δ / γ := by
    intro i
    by_cases hi : i ∈ I
    · simp only [Pi.sub_apply, v, if_pos hi, sub_self, abs_zero]
      positivity
    · simpa only [Pi.sub_apply, v, if_neg hi, sub_zero] using hsmall i hi
  have hsum : (∑ i ∈ nonzeroSupport (u₀ - v), |(u₀ - v) i|) ≤
      (K : ℝ) * (2 * δ / γ) := by
    calc
      _ ≤ ∑ _i ∈ nonzeroSupport (u₀ - v), 2 * δ / γ :=
        Finset.sum_le_sum fun i _ => hdeleted_bound i
      _ = ((nonzeroSupport (u₀ - v)).card : ℝ) * (2 * δ / γ) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hdeleted_card) (by positivity)
  have hsynthesis := (euclidean_mulVec_norm_le_sum_abs B hunit (u₀ - v)).trans hsum
  refine ⟨v, hv, ?_⟩
  calc
    _ ≤ ‖x - representationToEuclidean d (B.mulVec u₀)‖ +
        ‖representationToEuclidean d (B.mulVec u₀) -
          representationToEuclidean d (B.mulVec v)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ + (K : ℝ) * (2 * δ / γ) := add_le_add herr₀ (by
      simpa only [Matrix.mulVec_sub, map_sub] using hsynthesis)
    _ = (1 + 2 * (K : ℝ) / γ) * δ := by ring

/-- A vector belongs to a selected Euclidean column span exactly when it
has a coefficient representation supported on the selected coordinates. -/
theorem mem_euclideanColumnSpan_iff_exists_code {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (support : Finset (Fin M))
    (x : EuclideanRepresentation d) :
    x ∈ euclideanColumnSpan B support ↔
      ∃ u : FeatureVector M, nonzeroSupport u ⊆ support ∧
        representationToEuclidean d (B.mulVec u) = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← map_mulVecLin_coordinateSpan_eq_columnSpan] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact ⟨u, nonzeroSupport_subset_of_mem_coordinateSpan hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨B.mulVec u,
      columnSpan_mono B hu (mulVec_mem_columnSpan_nonzeroSupport B u), rfl⟩

/-- Enlarging a support enlarges its Euclidean column span. -/
theorem euclideanColumnSpan_mono {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) {S T : Finset (Fin M)} (hST : S ⊆ T) :
    euclideanColumnSpan B S ≤ euclideanColumnSpan B T :=
  Submodule.map_mono (columnSpan_mono B hST)

/-- The same intersection bound stated directly in terms of nearby points
in the individual column spans. The supported codes are derived from span
membership, so they are not extra assumptions. -/
theorem exists_mem_intersection_span_of_approximations
    {ι : Type*} {d M K : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ δ : ℝ)
    (hunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hstable : SparseLowerStable B γ (2 * K)) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (supports : ι → Finset (Fin M)) (family : Finset ι)
    (hne : family.Nonempty) (hcard : ∀ s ∈ family, (supports s).card ≤ K)
    (x : EuclideanRepresentation d)
    (hnear : ∀ s ∈ family, ∃ y ∈ euclideanColumnSpan B (supports s),
      ‖x - y‖ ≤ δ) :
    ∃ y ∈ euclideanColumnSpan B (supportFamilyIntersection supports family),
      ‖x - y‖ ≤ (1 + 2 * (K : ℝ) / γ) * δ := by
  have hcodes : ∀ s ∈ family, ∃ u : FeatureVector M,
      nonzeroSupport u ⊆ supports s ∧
        ‖x - representationToEuclidean d (B.mulVec u)‖ ≤ δ := by
    intro s hs
    obtain ⟨y, hy, herr⟩ := hnear s hs
    obtain ⟨u, hu, rfl⟩ := (mem_euclideanColumnSpan_iff_exists_code B (supports s) y).mp hy
    exact ⟨u, hu, herr⟩
  obtain ⟨u, hu, herr⟩ := exists_code_on_support_intersection_of_residuals
    B γ δ hunit hstable hγ hδ supports family hne hcard x hcodes
  exact ⟨_, (mem_euclideanColumnSpan_iff_exists_code B _ _).mpr ⟨u, hu, rfl⟩, herr⟩

/-- A directed gap for each matched pair of support spans gives a directed
gap for their intersections. The target dictionary's stability is sufficient
for this direction. -/
theorem support_intersection_directed_approximation
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (γ δ : ℝ)
    (hunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hstable : SparseLowerStable B γ (2 * K)) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m)) (family : Finset ι)
    (hne : family.Nonempty) (hcard : ∀ s ∈ family, (T s).card ≤ K)
    (hgap : ∀ s ∈ family, ∀ x ∈ euclideanColumnSpan A (S s),
      ∃ y ∈ euclideanColumnSpan B (T s), ‖x - y‖ ≤ δ * ‖x‖)
    (x : EuclideanRepresentation d)
    (hx : x ∈ euclideanColumnSpan A (supportFamilyIntersection S family)) :
    ∃ y ∈ euclideanColumnSpan B (supportFamilyIntersection T family),
      ‖x - y‖ ≤ ((1 + 2 * (K : ℝ) / γ) * δ) * ‖x‖ := by
  have hnear : ∀ s ∈ family, ∃ y ∈ euclideanColumnSpan B (T s),
      ‖x - y‖ ≤ δ * ‖x‖ := by
    intro s hs
    apply hgap s hs x
    apply euclideanColumnSpan_mono A (fun i hi => ?_) hx
    exact (mem_supportFamilyIntersection S family i).mp hi s hs
  simpa only [mul_assoc] using exists_mem_intersection_span_of_approximations
    B γ (δ * ‖x‖) hunit hstable hγ (mul_nonneg hδ (norm_nonneg _))
    T family hne hcard x hnear

/-- A uniform directed subspace approximation with factor strictly below
one makes the orthogonal projection injective on the source subspace. -/
theorem projection_injective_of_directed_subspace_approximation {d : ℕ}
    (U V : Submodule ℝ (EuclideanRepresentation d)) (ε : ℝ) (hε : ε < 1)
    (hgap : ∀ x ∈ U, ∃ y ∈ V, ‖x - y‖ ≤ ε * ‖x‖) :
    Function.Injective (V.orthogonalProjection.toLinearMap.comp U.subtype) := by
  let L : U →ₗ[ℝ] V := V.orthogonalProjection.toLinearMap.comp U.subtype
  have hker : ∀ x : U, L x = 0 → x = 0 := by
    intro x hx
    have hproj : V.starProjection (x : EuclideanRepresentation d) = 0 := by
      exact congrArg Subtype.val hx
    obtain ⟨y, hy, herr⟩ := hgap x x.property
    have hmin : ‖(x : EuclideanRepresentation d)‖ ≤ ‖(x : EuclideanRepresentation d) - y‖ := by
      have h := Submodule.starProjection_minimal (U := V) (x : EuclideanRepresentation d)
      rw [hproj, sub_zero] at h
      rw [h]
      apply ciInf_le _ (⟨y, hy⟩ : V)
      exact ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩
    have hz : ‖(x : EuclideanRepresentation d)‖ = 0 := by
      nlinarith [norm_nonneg (x : EuclideanRepresentation d)]
    apply Subtype.ext
    exact norm_eq_zero.mp hz
  have hinj : Function.Injective L := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hxy, sub_self]
  exact hinj

/-- A directed approximation factor below one forces the source dimension
to be no larger than the target dimension. -/
theorem finrank_le_of_directed_subspace_approximation {d : ℕ}
    (U V : Submodule ℝ (EuclideanRepresentation d)) (ε : ℝ) (hε : ε < 1)
    (hgap : ∀ x ∈ U, ∃ y ∈ V, ‖x - y‖ ≤ ε * ‖x‖) :
    Module.finrank ℝ U ≤ Module.finrank ℝ V :=
  LinearMap.finrank_le_finrank_of_injective
    (projection_injective_of_directed_subspace_approximation U V ε hε hgap)

/-- Independence of selected columns identifies the Euclidean span dimension
with the number of selected coordinates. -/
theorem finrank_euclideanColumnSpan_eq_card {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (support : Finset (Fin M))
    (hlin : LinearIndependent ℝ (selectedColumns B support)) :
    Module.finrank ℝ (euclideanColumnSpan B support) = support.card := by
  rw [euclideanColumnSpan, (representationToEuclidean d).toLinearEquiv.finrank_map_eq]
  exact finrank_columnSpan_eq_card B support hlin

/-- A bound on the difference of orthogonal projectors supplies actual
nearby points in the target subspace, with error proportional to the norm
of the source point. -/
theorem directed_subspace_approximation_of_projector_bound {d : ℕ}
    (U V : Submodule ℝ (EuclideanRepresentation d)) (δ : ℝ)
    (hgap : ‖U.starProjection - V.starProjection‖ ≤ δ)
    (x : EuclideanRepresentation d) (hx : x ∈ U) :
    ∃ y ∈ V, ‖x - y‖ ≤ δ * ‖x‖ := by
  refine ⟨V.starProjection x, (V.orthogonalProjection x).property, ?_⟩
  calc
    _ = ‖(U.starProjection - V.starProjection) x‖ := by
      rw [ContinuousLinearMap.sub_apply, U.starProjection_eq_self_iff.mpr hx]
    _ ≤ ‖U.starProjection - V.starProjection‖ * ‖x‖ :=
      (U.starProjection - V.starProjection).le_opNorm x
    _ ≤ δ * ‖x‖ := mul_le_mul_of_nonneg_right hgap (norm_nonneg _)

/-- Orthogonal projection is at least as good as any point selected by a
directed subspace approximation. -/
private theorem norm_projection_residual_le_of_approximation {d : ℕ}
    (V : Submodule ℝ (EuclideanRepresentation d))
    (x : EuclideanRepresentation d) (r : ℝ)
    (hnear : ∃ y ∈ V, ‖x - y‖ ≤ r) :
    ‖x - V.starProjection x‖ ≤ r := by
  obtain ⟨y, hy, herr⟩ := hnear
  apply le_trans _ herr
  rw [Submodule.starProjection_minimal]
  apply ciInf_le _ (⟨y, hy⟩ : V)
  exact ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩

/-- The directed approximation from `U` to `V` also bounds the projection
onto `U` of a vector perpendicular to `V`. This is the adjoint half of the
projection-gap argument, proved directly by the real inner product. -/
private theorem norm_projection_of_mem_orthogonal_le {d : ℕ}
    (U V : Submodule ℝ (EuclideanRepresentation d)) (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ x ∈ U, ∃ y ∈ V, ‖x - y‖ ≤ ε * ‖x‖)
    (z : EuclideanRepresentation d) (hz : z ∈ Vᗮ) :
    ‖U.starProjection z‖ ≤ ε * ‖z‖ := by
  let p := U.starProjection z
  have hp : p ∈ U := U.starProjection_apply_mem z
  obtain ⟨y, hy, herr⟩ := hgap p hp
  have hzy : inner ℝ z y = 0 := (V.mem_orthogonal' z).mp hz y hy
  have hzp : inner ℝ z p = ‖p‖ ^ 2 := by
    have h := U.starProjection_inner_eq_zero z p hp
    change inner ℝ (z - p) p = 0 at h
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
    linarith
  have hinner := real_inner_le_norm z (p - y)
  rw [inner_sub_right, hzy, sub_zero, hzp] at hinner
  have hbound : ‖p‖ ^ 2 ≤ ‖z‖ * (ε * ‖p‖) :=
    hinner.trans (mul_le_mul_of_nonneg_left herr (norm_nonneg _))
  change ‖p‖ ≤ ε * ‖z‖
  by_cases hpzero : ‖p‖ = 0
  · rw [hpzero]
    exact mul_nonneg hε (norm_nonneg _)
  · have hppos : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hpzero)
    nlinarith

/-- Uniform approximation in both directions bounds the operator norm of
the difference of orthogonal projectors by the same constant. Pythagoras
combines the two directions without introducing a factor of two. -/
theorem projector_bound_of_directed_subspace_approximations {d : ℕ}
    (U V : Submodule ℝ (EuclideanRepresentation d)) (ε : ℝ) (hε : 0 ≤ ε)
    (hforward : ∀ x ∈ U, ∃ y ∈ V, ‖x - y‖ ≤ ε * ‖x‖)
    (hbackward : ∀ y ∈ V, ∃ x ∈ U, ‖y - x‖ ≤ ε * ‖y‖) :
    ‖U.starProjection - V.starProjection‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro x
  let q := V.starProjection x
  let r := Vᗮ.starProjection x
  have hq : q ∈ V := V.starProjection_apply_mem x
  have hr : r ∈ Vᗮ := Vᗮ.starProjection_apply_mem x
  have hU : ‖U.starProjection r‖ ≤ ε * ‖r‖ :=
    norm_projection_of_mem_orthogonal_le U V ε hε hforward r hr
  have hUperp : ‖Uᗮ.starProjection q‖ ≤ ε * ‖q‖ := by
    rw [Submodule.starProjection_orthogonal_val]
    exact norm_projection_residual_le_of_approximation U q _ (hbackward q hq)
  have hsplit : (U.starProjection - V.starProjection) x =
      U.starProjection r - Uᗮ.starProjection q := by
    dsimp only [r, q]
    rw [ContinuousLinearMap.sub_apply, Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_orthogonal_val, map_sub]
    abel
  have horth : inner ℝ (U.starProjection r) (Uᗮ.starProjection q) = 0 :=
    (U.mem_orthogonal _).mp (Uᗮ.starProjection_apply_mem q) _
      (U.starProjection_apply_mem r)
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection x V
  change ‖x‖ ^ 2 = ‖q‖ ^ 2 + ‖r‖ ^ 2 at hpyth
  have hUsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))).mpr hU
  have hUperpsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))).mpr hUperp
  rw [hsplit]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))).mp
  rw [norm_sub_sq_real, horth]
  nlinarith [sq_nonneg ε]

/-- A one-sided approximation with error at most one half determines the
dimension and gives a two-sided projector estimate whenever the target has
no more dimensions than the source. The factor two is a convenient bound
obtained by inverting the restricted orthogonal projection. -/
theorem projector_bound_of_one_sided_approximation {d : ℕ}
    (U V : Submodule ℝ (EuclideanRepresentation d)) (ε : ℝ)
    (hε : 0 ≤ ε) (hhalf : ε ≤ 1 / 2)
    (hdim : Module.finrank ℝ V ≤ Module.finrank ℝ U)
    (hgap : ∀ x ∈ U, ∃ y ∈ V, ‖x - y‖ ≤ ε * ‖x‖) :
    Module.finrank ℝ U = Module.finrank ℝ V ∧
      ‖U.starProjection - V.starProjection‖ ≤ 2 * ε := by
  have hsmall : ε < 1 := by linarith
  have heq : Module.finrank ℝ U = Module.finrank ℝ V :=
    le_antisymm (finrank_le_of_directed_subspace_approximation U V ε hsmall hgap) hdim
  refine ⟨heq, ?_⟩
  let L : U →ₗ[ℝ] V := V.orthogonalProjection.toLinearMap.comp U.subtype
  have hinj : Function.Injective L :=
    projection_injective_of_directed_subspace_approximation U V ε hsmall hgap
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hinj
  apply projector_bound_of_directed_subspace_approximations U V (2 * ε) (by positivity)
  · intro x hx
    obtain ⟨y, hy, herr⟩ := hgap x hx
    exact ⟨y, hy, herr.trans
      (mul_le_mul_of_nonneg_right (by linarith : ε ≤ 2 * ε) (norm_nonneg _))⟩
  · intro y hy
    obtain ⟨x, hxy⟩ := hsurj ⟨y, hy⟩
    have hproj : V.starProjection (x : EuclideanRepresentation d) = y :=
      congrArg Subtype.val hxy
    have herr : ‖(x : EuclideanRepresentation d) - y‖ ≤ ε * ‖(x : EuclideanRepresentation d)‖ := by
      rw [← hproj]
      exact norm_projection_residual_le_of_approximation V x _ (hgap x x.property)
    have hnorm : ‖(x : EuclideanRepresentation d)‖ ≤ 2 * ‖y‖ := by
      have htriangle := norm_add_le ((x : EuclideanRepresentation d) - y) y
      rw [sub_add_cancel] at htriangle
      have hmul := mul_le_mul_of_nonneg_right hhalf (norm_nonneg (x : EuclideanRepresentation d))
      linarith
    refine ⟨x, x.property, ?_⟩
    calc
      ‖y - (x : EuclideanRepresentation d)‖ = ‖(x : EuclideanRepresentation d) - y‖ := norm_sub_rev _ _
      _ ≤ ε * ‖(x : EuclideanRepresentation d)‖ := herr
      _ ≤ ε * (2 * ‖y‖) := mul_le_mul_of_nonneg_left hnorm hε
      _ = (2 * ε) * ‖y‖ := by ring

/-- Two-sided approximation of the matched support spans preserves every
nonempty intersection cardinality as soon as both amplified errors are below
one. No matching or equality of dimensions is assumed in this theorem. -/
theorem support_intersection_card_eq_of_directed_approximations
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (α γ δ : ℝ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A α (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hα : 0 < α) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hsmallA : (1 + 2 * (K : ℝ) / α) * δ < 1)
    (hsmallB : (1 + 2 * (K : ℝ) / γ) * δ < 1)
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m)) (family : Finset ι)
    (hne : family.Nonempty)
    (hScard : ∀ s ∈ family, (S s).card ≤ K)
    (hTcard : ∀ s ∈ family, (T s).card ≤ K)
    (hforward : ∀ s ∈ family, ∀ x ∈ euclideanColumnSpan A (S s),
      ∃ y ∈ euclideanColumnSpan B (T s), ‖x - y‖ ≤ δ * ‖x‖)
    (hbackward : ∀ s ∈ family, ∀ y ∈ euclideanColumnSpan B (T s),
      ∃ x ∈ euclideanColumnSpan A (S s), ‖y - x‖ ≤ δ * ‖y‖) :
    (supportFamilyIntersection S family).card =
      (supportFamilyIntersection T family).card := by
  have hforward' := support_intersection_directed_approximation A B γ δ
    hBunit hBstable hγ hδ S T family hne hTcard hforward
  have hbackward' := support_intersection_directed_approximation B A α δ
    hAunit hAstable hα hδ T S family hne hScard hbackward
  have hdim := le_antisymm
    (finrank_le_of_directed_subspace_approximation _ _ _ hsmallB hforward')
    (finrank_le_of_directed_subspace_approximation _ _ _ hsmallA hbackward')
  obtain ⟨s, hs⟩ := hne
  have hSI : (supportFamilyIntersection S family).card ≤ 2 * K := by
    have hsub : supportFamilyIntersection S family ⊆ S s :=
      fun i hi => (mem_supportFamilyIntersection S family i).mp hi s hs
    exact ((Finset.card_le_card hsub).trans (hScard s hs)).trans (by omega)
  have hTI : (supportFamilyIntersection T family).card ≤ 2 * K := by
    have hsub : supportFamilyIntersection T family ⊆ T s :=
      fun i hi => (mem_supportFamilyIntersection T family i).mp hi s hs
    exact ((Finset.card_le_card hsub).trans (hTcard s hs)).trans (by omega)
  rwa [finrank_euclideanColumnSpan_eq_card A _ (hAstable.linearIndependent hα _ hSI),
    finrank_euclideanColumnSpan_eq_card B _ (hBstable.linearIndependent hγ _ hTI)] at hdim

/-- In particular, a uniform operator-norm bound on the matched projectors
implies equality of all nonempty intersection cardinalities under the stated
source and learned decoding margins. -/
theorem support_intersection_card_eq_of_projector_bounds
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (α γ δ : ℝ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A α (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hα : 0 < α) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hsmallA : (1 + 2 * (K : ℝ) / α) * δ < 1)
    (hsmallB : (1 + 2 * (K : ℝ) / γ) * δ < 1)
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m)) (family : Finset ι)
    (hne : family.Nonempty)
    (hScard : ∀ s ∈ family, (S s).card ≤ K)
    (hTcard : ∀ s ∈ family, (T s).card ≤ K)
    (hgap : ∀ s ∈ family,
      ‖(euclideanColumnSpan A (S s)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤ δ) :
    (supportFamilyIntersection S family).card =
      (supportFamilyIntersection T family).card := by
  apply support_intersection_card_eq_of_directed_approximations A B α γ δ
    hAunit hBunit hAstable hBstable hα hγ hδ hsmallA hsmallB
    S T family hne hScard hTcard
  · intro s hs x hx
    exact directed_subspace_approximation_of_projector_bound _ _ δ (hgap s hs) x hx
  · intro s hs y hy
    apply directed_subspace_approximation_of_projector_bound _ _ δ _ y hy
    simpa only [norm_sub_rev] using hgap s hs

/-- The quantitative operator-norm estimate on intersections uses the larger
of the two directed errors. It does not require an a priori dimension match
or a smallness assumption on the original support-span error. -/
theorem support_intersection_projector_bound
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (α γ δ : ℝ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A α (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hα : 0 < α) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m)) (family : Finset ι)
    (hne : family.Nonempty)
    (hScard : ∀ s ∈ family, (S s).card ≤ K)
    (hTcard : ∀ s ∈ family, (T s).card ≤ K)
    (hgap : ∀ s ∈ family,
      ‖(euclideanColumnSpan A (S s)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤ δ) :
    ‖(euclideanColumnSpan A (supportFamilyIntersection S family)).starProjection -
        (euclideanColumnSpan B (supportFamilyIntersection T family)).starProjection‖ ≤
      max ((1 + 2 * (K : ℝ) / α) * δ) ((1 + 2 * (K : ℝ) / γ) * δ) := by
  have hforward : ∀ s ∈ family, ∀ x ∈ euclideanColumnSpan A (S s),
      ∃ y ∈ euclideanColumnSpan B (T s), ‖x - y‖ ≤ δ * ‖x‖ := by
    intro s hs x hx
    exact directed_subspace_approximation_of_projector_bound _ _ δ (hgap s hs) x hx
  have hbackward : ∀ s ∈ family, ∀ y ∈ euclideanColumnSpan B (T s),
      ∃ x ∈ euclideanColumnSpan A (S s), ‖y - x‖ ≤ δ * ‖y‖ := by
    intro s hs y hy
    apply directed_subspace_approximation_of_projector_bound _ _ δ _ y hy
    simpa only [norm_sub_rev] using hgap s hs
  apply projector_bound_of_directed_subspace_approximations _ _ _ (by positivity)
  · intro x hx
    obtain ⟨y, hy, herr⟩ := support_intersection_directed_approximation A B γ δ
      hBunit hBstable hγ hδ S T family hne hTcard hforward x hx
    exact ⟨y, hy, herr.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩
  · intro y hy
    obtain ⟨x, hx, herr⟩ := support_intersection_directed_approximation B A α δ
      hAunit hAstable hα hδ T S family hne hScard hbackward y hy
    exact ⟨x, hx, herr.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩

/-- With the handwritten proof's choice
`δ = η / (2 * (1 + 2K / min α γ))`, every nonempty matched support
intersection has equal cardinality and projector distance at most `η/2`.
Both conclusions are derived from the original matched support-projector
bounds and the two dictionaries' sparse stability assumptions. -/
theorem stable_support_intersections
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (α γ η : ℝ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A α (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hα : 0 < α) (hγ : 0 < γ) (hη : 0 < η) (hηone : η < 1)
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m)) (family : Finset ι)
    (hne : family.Nonempty)
    (hScard : ∀ s ∈ family, (S s).card ≤ K)
    (hTcard : ∀ s ∈ family, (T s).card ≤ K)
    (hgap : ∀ s ∈ family,
      ‖(euclideanColumnSpan A (S s)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤
          η / (2 * (1 + 2 * (K : ℝ) / min α γ))) :
    (supportFamilyIntersection S family).card =
        (supportFamilyIntersection T family).card ∧
      ‖(euclideanColumnSpan A (supportFamilyIntersection S family)).starProjection -
        (euclideanColumnSpan B (supportFamilyIntersection T family)).starProjection‖ ≤
          η / 2 := by
  let c := 1 + 2 * (K : ℝ) / min α γ
  let δ := η / (2 * c)
  have hmin : 0 < min α γ := lt_min hα hγ
  have hc : 0 < c := by dsimp [c]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hcancel : c * δ = η / 2 := by
    dsimp only [δ]
    field_simp
  have hfactorA : 1 + 2 * (K : ℝ) / α ≤ c := by
    dsimp only [c]
    have hnum : 0 ≤ 2 * (K : ℝ) := by positivity
    linarith [div_le_div_of_nonneg_left hnum hmin (min_le_left α γ)]
  have hfactorB : 1 + 2 * (K : ℝ) / γ ≤ c := by
    dsimp only [c]
    have hnum : 0 ≤ 2 * (K : ℝ) := by positivity
    linarith [div_le_div_of_nonneg_left hnum hmin (min_le_right α γ)]
  have hboundA : (1 + 2 * (K : ℝ) / α) * δ ≤ η / 2 :=
    (mul_le_mul_of_nonneg_right hfactorA hδ).trans_eq hcancel
  have hboundB : (1 + 2 * (K : ℝ) / γ) * δ ≤ η / 2 :=
    (mul_le_mul_of_nonneg_right hfactorB hδ).trans_eq hcancel
  have hhalf : η / 2 < 1 := by linarith
  constructor
  · exact support_intersection_card_eq_of_projector_bounds A B α γ δ
      hAunit hBunit hAstable hBstable hα hγ hδ
      (hboundA.trans_lt hhalf) (hboundB.trans_lt hhalf)
      S T family hne hScard hTcard hgap
  · exact (support_intersection_projector_bound A B α γ δ
      hAunit hBunit hAstable hBstable hα hγ hδ S T family hne hScard hTcard hgap).trans
        (max_le hboundA hboundB)

end PKG26AtomicFeatures
