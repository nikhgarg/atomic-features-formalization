import PKG26AtomicFeatures.ProjectedCoefficientCodes

/-!
# Coordinates of projections onto sparse source spans

A stable source dictionary gives a continuous coordinate map for projection
onto any support of size at most `K`. Its norm is bounded by the inverse
decoding margin. If a vector is close to two sparse spans, every coordinate
absent from the second support is small in its projection onto the first.
These estimates require neither orthogonal atoms nor a coefficient density.
-/

namespace PKG26AtomicFeatures

/-- The projected source coordinates exist on the entire ambient space;
the ambient dimension is independent of the sparsity order. -/
theorem exists_ambient_projected_support_coefficient_map {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (S : Finset (Fin M))
    (γ : ℝ) (hγ : 0 < γ) (hstable : SparseLowerStable A γ (2 * K))
    (hS : S.card ≤ K) :
    ∃ C : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation M,
      (∀ x, nonzeroSupport ((representationToEuclidean M).symm (C x)) ⊆ S) ∧
      ∀ x, representationToEuclidean d
        (A.mulVec ((representationToEuclidean M).symm (C x))) =
          (euclideanColumnSpan A S).starProjection x := by
  let e := LinearEquiv.ofBijective (supportedSynthesisLinearMap A S)
    (supportedSynthesisLinearMap_bijective A S γ hγ hstable hS)
  let D : EuclideanRepresentation d →ₗ[ℝ] coordinateSpan S :=
    e.symm.toLinearMap.comp (euclideanColumnSpan A S).orthogonalProjection.toLinearMap
  let C : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation M :=
    ((representationToEuclidean M).toLinearMap.comp
      ((coordinateSpan S).subtype.comp D)).toContinuousLinearMap
  have hC (x) : (representationToEuclidean M).symm (C x) = (D x).1 :=
    (representationToEuclidean M).symm_apply_apply _
  refine ⟨C, fun x => ?_, fun x => ?_⟩
  · rw [hC]
    exact nonzeroSupport_subset_of_mem_coordinateSpan (D x).2
  · rw [hC]
    exact congrArg Subtype.val
      (e.apply_symm_apply ((euclideanColumnSpan A S).orthogonalProjection x))

/-- Projection contracts norms and sparse decoding bounds the coordinates. -/
theorem projected_support_coefficient_norm_le {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (S : Finset (Fin M))
    (C : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation M)
    (γ : ℝ) (hγ : 0 < γ) (hstable : SparseLowerStable A γ (2 * K))
    (hS : S.card ≤ K)
    (hsupport : ∀ x, nonzeroSupport ((representationToEuclidean M).symm (C x)) ⊆ S)
    (hC : ∀ x, representationToEuclidean d
      (A.mulVec ((representationToEuclidean M).symm (C x))) =
        (euclideanColumnSpan A S).starProjection x)
    (x : EuclideanRepresentation d) : ‖C x‖ ≤ ‖x‖ / γ := by
  have h := hstable ((representationToEuclidean M).symm (C x))
    (((Finset.card_le_card (hsupport x)).trans hS).trans (by omega))
  rw [(representationToEuclidean M).apply_symm_apply, hC] at h
  apply (le_div_iff₀ hγ).mpr
  simpa only [mul_comm] using h.trans ((euclideanColumnSpan A S).norm_starProjection_apply_le x)

/-- Each source-coordinate functional has norm at most the inverse margin. -/
theorem projected_support_coordinate_norm_le {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (S : Finset (Fin M))
    (C : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation M)
    (γ : ℝ) (hγ : 0 < γ) (hstable : SparseLowerStable A γ (2 * K))
    (hS : S.card ≤ K)
    (hsupport : ∀ x, nonzeroSupport ((representationToEuclidean M).symm (C x)) ⊆ S)
    (hC : ∀ x, representationToEuclidean d
      (A.mulVec ((representationToEuclidean M).symm (C x))) =
        (euclideanColumnSpan A S).starProjection x)
    (i : Fin M) : ‖(PiLp.proj 2 (fun _ : Fin M => ℝ) i).comp C‖ ≤ 1 / γ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have h := (PiLp.norm_apply_le (C x) i).trans
    (projected_support_coefficient_norm_le A S C γ hγ hstable hS hsupport hC x)
  simpa only [ContinuousLinearMap.comp_apply, PiLp.proj_apply, one_div_mul_eq_div] using h

/-- Projected coordinates agree with every code already supported on the
selected source span. In particular, the source columns have their usual
unit coordinate vectors. -/
theorem projected_support_coefficient_of_supported_code {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (S : Finset (Fin M))
    (C : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation M)
    (γ : ℝ) (hγ : 0 < γ) (hstable : SparseLowerStable A γ (2 * K))
    (hS : S.card ≤ K)
    (hsupport : ∀ x, nonzeroSupport ((representationToEuclidean M).symm (C x)) ⊆ S)
    (hC : ∀ x, representationToEuclidean d
      (A.mulVec ((representationToEuclidean M).symm (C x))) =
        (euclideanColumnSpan A S).starProjection x)
    (u : FeatureVector M) (hu : nonzeroSupport u ⊆ S) :
    C (representationToEuclidean d (A.mulVec u)) = representationToEuclidean M u := by
  have hmem : representationToEuclidean d (A.mulVec u) ∈ euclideanColumnSpan A S :=
    (mem_euclideanColumnSpan_iff_exists_code A S _).mpr ⟨u, hu, rfl⟩
  have heq := hC (representationToEuclidean d (A.mulVec u))
  rw [Submodule.starProjection_eq_self_iff.mpr hmem] at heq
  have hu' := hstable.sparseInjective hγ _ u
    ((Finset.card_le_card (hsupport _)).trans hS)
    ((Finset.card_le_card hu).trans hS)
    ((representationToEuclidean d).injective heq)
  simpa only [(representationToEuclidean M).apply_symm_apply] using
    congrArg (representationToEuclidean M) hu'

/-- A coordinate missing from a second sparse support is bounded by the
sum of the two projection errors divided by the decoding margin. -/
theorem projected_support_coordinate_le_of_two_residuals {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (S T : Finset (Fin M))
    (C : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation M)
    (γ : ℝ) (hγ : 0 < γ) (hstable : SparseLowerStable A γ (2 * K))
    (hS : S.card ≤ K) (hT : T.card ≤ K)
    (hsupport : ∀ x, nonzeroSupport ((representationToEuclidean M).symm (C x)) ⊆ S)
    (hC : ∀ x, representationToEuclidean d
      (A.mulVec ((representationToEuclidean M).symm (C x))) =
        (euclideanColumnSpan A S).starProjection x)
    (x : EuclideanRepresentation d) (δS δT : ℝ)
    (hnearS : ‖x - (euclideanColumnSpan A S).starProjection x‖ ≤ δS)
    (hnearT : ‖x - (euclideanColumnSpan A T).starProjection x‖ ≤ δT)
    (i : Fin M) (hi : i ∉ T) : |(C x) i| ≤ (δS + δT) / γ := by
  obtain ⟨v, hv, hAv⟩ := (mem_euclideanColumnSpan_iff_exists_code A T _).mp
    ((euclideanColumnSpan A T).starProjection_apply_mem x)
  have hvi : v i = 0 := by
    by_contra hn
    exact hi (hv ((mem_nonzeroSupport_iff v i).mpr hn))
  let u := (representationToEuclidean M).symm (C x)
  have hdist := hstable.code_distance u v
    ((Finset.card_le_card (hsupport x)).trans hS) ((Finset.card_le_card hv).trans hT)
  have hsyn : representationToEuclidean d (A.mulVec u) =
      (euclideanColumnSpan A S).starProjection x := hC x
  have hbound : γ * ‖representationToEuclidean M (u - v)‖ ≤ δS + δT := by
    calc
      _ ≤ ‖representationToEuclidean d (A.mulVec u) -
          representationToEuclidean d (A.mulVec v)‖ := by simpa only [map_sub] using hdist
      _ ≤ ‖representationToEuclidean d (A.mulVec u) - x‖ +
          ‖x - representationToEuclidean d (A.mulVec v)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δS + δT := by rw [hsyn, hAv]; exact add_le_add (by simpa only [norm_sub_rev] using hnearS) hnearT
  have hcoord := abs_coordinate_sub_le_euclidean_norm u v i
  have hui : u i = (C x) i := rfl
  rw [hvi, sub_zero, hui] at hcoord
  apply (le_div_iff₀ hγ).mpr
  nlinarith

/-- A source column has its unit coordinate vector under projection onto
any selected source support containing that column. -/
theorem projected_support_coefficient_on_source_column {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (S : Finset (Fin M))
    (C : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation M)
    (γ : ℝ) (hγ : 0 < γ) (hstable : SparseLowerStable A γ (2 * K))
    (hS : S.card ≤ K)
    (hsupport : ∀ x, nonzeroSupport ((representationToEuclidean M).symm (C x)) ⊆ S)
    (hC : ∀ x, representationToEuclidean d
      (A.mulVec ((representationToEuclidean M).symm (C x))) =
        (euclideanColumnSpan A S).starProjection x)
    (i : Fin M) (hi : i ∈ S) :
    C (representationToEuclidean d (A.col i)) =
      representationToEuclidean M (Pi.single i 1 : FeatureVector M) := by
  simpa only [Matrix.mulVec_single_one] using
    projected_support_coefficient_of_supported_code A S C γ hγ hstable hS hsupport hC
      (Pi.single i 1) (nonzeroSupport_subset_of_mem_coordinateSpan
        (canonicalVector_mem_coordinateSpan S hi))

/-- Proximity to a signed source column controls its corresponding source
coordinate. The estimate includes either sign without a density hypothesis. -/
theorem projected_support_coordinate_deviation_le {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (S : Finset (Fin M))
    (C : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation M)
    (γ : ℝ) (hγ : 0 < γ) (hstable : SparseLowerStable A γ (2 * K))
    (hS : S.card ≤ K)
    (hsupport : ∀ x, nonzeroSupport ((representationToEuclidean M).symm (C x)) ⊆ S)
    (hC : ∀ x, representationToEuclidean d
      (A.mulVec ((representationToEuclidean M).symm (C x))) =
        (euclideanColumnSpan A S).starProjection x)
    (i : Fin M) (hi : i ∈ S) (x : EuclideanRepresentation d) (σ q : ℝ)
    (hnear : ‖x - σ • representationToEuclidean d (A.col i)‖ ≤ q) :
    |(C x) i - σ| ≤ q / γ := by
  have hdiag := projected_support_coefficient_on_source_column A S C γ hγ hstable
    hS hsupport hC i hi
  have hcoord := PiLp.norm_apply_le
    (C (x - σ • representationToEuclidean d (A.col i))) i
  have hnorm := projected_support_coefficient_norm_le A S C γ hγ hstable hS hsupport hC
    (x - σ • representationToEuclidean d (A.col i))
  have heval : (C (x - σ • representationToEuclidean d (A.col i))) i = (C x) i - σ := by
    rw [map_sub, map_smul, hdiag]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, representationToEuclidean,
      PiLp.continuousLinearEquiv_symm_apply, Pi.single_eq_same, mul_one]
  rw [heval, Real.norm_eq_abs] at hcoord
  exact (hcoord.trans hnorm).trans (div_le_div_of_nonneg_right hnear hγ.le)

/-- The projector gap directly bounds the projection error of a vector
already in the other subspace. -/
theorem projection_residual_le_of_mem_projector_bound {d : ℕ}
    (U V : Submodule ℝ (EuclideanRepresentation d)) (δ : ℝ)
    (hgap : ‖U.starProjection - V.starProjection‖ ≤ δ)
    (x : EuclideanRepresentation d) (hx : x ∈ V) :
    ‖x - U.starProjection x‖ ≤ δ * ‖x‖ := by
  calc
    _ = ‖(U.starProjection - V.starProjection) x‖ := by
      rw [ContinuousLinearMap.sub_apply, V.starProjection_eq_self_iff.mpr hx, norm_sub_rev]
    _ ≤ ‖U.starProjection - V.starProjection‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hgap (norm_nonneg _)

end PKG26AtomicFeatures
