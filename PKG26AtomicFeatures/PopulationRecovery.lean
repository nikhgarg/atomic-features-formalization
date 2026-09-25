import PKG26AtomicFeatures.DimensionCounterexample
import PKG26AtomicFeatures.EqualSizeIdentifiability
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Full-budget recovery from population reconstruction loss

This module gives a precise full-budget population theorem related to the
paper's recovery-principle discussion.  The data domain contains every
`K`-sparse source coefficient vector.  Its probability law is required to be
positive on every nonempty open set in the domain's relative topology.  The
objective is the population squared Euclidean distance to the finite union of
all alternative column spans using at most `K` columns.

The source matrix attains zero loss.  Hence every global minimizer also has
zero loss.  The pointwise error is continuous, so full topological support
upgrades its almost-everywhere vanishing to vanishing everywhere.  Closedness
of the finite union then supplies an exact `K`-sparse alternative code on the
universal domain, and the existing equal-size identifiability theorem recovers
the alternative columns.  No spark assumption is imposed on the alternative.

The use of `EuclideanSpace` is material: the paper's squared reconstruction
error is the sum-of-squares norm, whereas the default norm on the underlying
function type `Fin d → ℝ` is the sup norm.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Topology
open scoped BigOperators

/-- The representation space equipped with its genuine Euclidean (`ℓ²`)
metric. -/
abbrev EuclideanRepresentation (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The canonical continuous linear identification from the paper's
coordinate representation type to the Euclidean copy of that type. -/
noncomputable def representationToEuclidean (d : ℕ) :
    RepresentationVector d ≃L[ℝ] EuclideanRepresentation d :=
  (PiLp.continuousLinearEquiv (ι := Fin d) 2 ℝ (fun _ => ℝ)).symm

/-- A selected column span transported to the Euclidean representation
space. -/
noncomputable def euclideanColumnSpan
    {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (coordinates : Finset (Fin M)) :
    Submodule ℝ (EuclideanRepresentation d) :=
  Submodule.map (representationToEuclidean d).toLinearMap
    (columnSpan matrix coordinates)

/-- All outputs representable using at most `K` columns of `matrix`, viewed
inside the genuine Euclidean representation space. -/
noncomputable def euclideanSparseRepresentationSet
    {d M : ℕ} (K : ℕ) (matrix : Matrix (Fin d) (Fin M) ℝ) :
    Set (EuclideanRepresentation d) :=
  ⋃ support : {coordinates : Finset (Fin M) // coordinates.card ≤ K},
    (euclideanColumnSpan matrix support.1 : Set (EuclideanRepresentation d))

/-- The finite union of at-most-`K` Euclidean column spans is closed. -/
theorem isClosed_euclideanSparseRepresentationSet
    {d M : ℕ} (K : ℕ) (matrix : Matrix (Fin d) (Fin M) ℝ) :
    IsClosed (euclideanSparseRepresentationSet K matrix) := by
  exact isClosed_iUnion_of_finite fun support =>
    (euclideanColumnSpan matrix support.1).closed_of_finiteDimensional

/-- The sparse representation set always contains zero. -/
theorem euclideanSparseRepresentationSet_nonempty
    {d M : ℕ} (K : ℕ) (matrix : Matrix (Fin d) (Fin M) ℝ) :
    (euclideanSparseRepresentationSet K matrix).Nonempty := by
  refine ⟨0, ?_⟩
  rw [euclideanSparseRepresentationSet, Set.mem_iUnion]
  exact ⟨⟨∅, by simp⟩, (euclideanColumnSpan matrix ∅).zero_mem⟩

/-- Pointwise squared Euclidean best-`K`-sparse reconstruction error.  The
codomain `ℝ≥0∞` makes the population objective meaningful without a separate
integrability assumption. -/
noncomputable def bestKSparseSquaredError
    {d M m : ℕ} (K : ℕ)
    (source : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin m) ℝ)
    (code : FeatureVector M) : ENNReal :=
  ENNReal.ofReal
    ((Metric.infDist
      (representationToEuclidean d (source.mulVec code))
      (euclideanSparseRepresentationSet K alternative)) ^ 2)

/-- The literal squared Euclidean reconstruction error of one real source
code by one real alternative code. -/
noncomputable def squaredEuclideanReconstructionError
    {d M m : ℕ}
    (source : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin m) ℝ)
    (sourceCode : FeatureVector M) (alternativeCode : FeatureVector m) : ℝ :=
  (dist
    (representationToEuclidean d (source.mulVec sourceCode))
    (representationToEuclidean d (alternative.mulVec alternativeCode))) ^ 2

/-- The genuine population squared reconstruction loss. -/
noncomputable def populationBestKSparseLoss
    {d M m : ℕ} (μ : Measure (UniversalSparseDomain M K))
    (source : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin m) ℝ) : ENNReal :=
  ∫⁻ code,
    bestKSparseSquaredError K source alternative code.1 ∂μ

/-- A matrix globally minimizes the population best-sparse objective among
all matrices with the same learned width. -/
def IsGlobalPopulationBestKSparseMinimizer
    {d M m : ℕ} (μ : Measure (UniversalSparseDomain M K))
    (source : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin m) ℝ) : Prop :=
  ∀ competitor : Matrix (Fin d) (Fin m) ℝ,
    populationBestKSparseLoss μ source alternative ≤
      populationBestKSparseLoss μ source competitor

/-- Every matrix column has unit norm in the genuine Euclidean representation
metric. -/
noncomputable def HasUnitEuclideanColumns
    {d m : ℕ} (matrix : Matrix (Fin d) (Fin m) ℝ) : Prop :=
  ∀ column,
    ‖representationToEuclidean d (matrix.col column)‖ = 1

/-- A unit-column matrix globally minimizes the population best-sparse
objective among all unit-column matrices of the same learned width. -/
noncomputable def IsGlobalUnitColumnPopulationBestKSparseMinimizer
    {d M m : ℕ} (μ : Measure (UniversalSparseDomain M K))
    (source : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin m) ℝ) : Prop :=
  HasUnitEuclideanColumns alternative ∧
    ∀ competitor : Matrix (Fin d) (Fin m) ℝ,
      HasUnitEuclideanColumns competitor →
        populationBestKSparseLoss μ source alternative ≤
          populationBestKSparseLoss μ source competitor

/-- Pointwise population error is continuous on the universal sparse domain
with its relative topology. -/
theorem continuous_bestKSparseSquaredError
    {d M m K : ℕ}
    (source : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin m) ℝ) :
    Continuous (fun code : UniversalSparseDomain M K =>
      bestKSparseSquaredError K source alternative code.1) := by
  have hsource : Continuous (fun code : UniversalSparseDomain M K =>
      representationToEuclidean d (source.mulVec code.1)) :=
    (representationToEuclidean d).continuous.comp
      ((LinearMap.continuous_of_finiteDimensional source.mulVecLin).comp
        continuous_subtype_val)
  exact ENNReal.continuous_ofReal.comp
    (((Metric.continuous_infDist_pt
      (euclideanSparseRepresentationSet K alternative)).comp hsource).pow 2)

/-- Every universal source sample is represented exactly by the source
matrix inside its Euclidean sparse representation set. -/
theorem source_mem_euclideanSparseRepresentationSet
    {d M K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (code : UniversalSparseDomain M K) :
    representationToEuclidean d (matrix.mulVec code.1) ∈
      euclideanSparseRepresentationSet K matrix := by
  rw [euclideanSparseRepresentationSet, Set.mem_iUnion]
  let support : {coordinates : Finset (Fin M) // coordinates.card ≤ K} :=
    ⟨nonzeroSupport code.1, code.2⟩
  refine ⟨support, ?_⟩
  exact ⟨matrix.mulVec code.1,
    mulVec_mem_columnSpan_nonzeroSupport matrix code.1, rfl⟩

/-- Every genuinely `K`-sparse real code produces a point of the sparse
representation set. -/
theorem sparse_mulVec_mem_euclideanSparseRepresentationSet
    {d m K : ℕ} (matrix : Matrix (Fin d) (Fin m) ℝ)
    (code : FeatureVector m)
    (hsparse : (nonzeroSupport code).card ≤ K) :
    representationToEuclidean d (matrix.mulVec code) ∈
      euclideanSparseRepresentationSet K matrix := by
  rw [euclideanSparseRepresentationSet, Set.mem_iUnion]
  let support : {coordinates : Finset (Fin m) // coordinates.card ≤ K} :=
    ⟨nonzeroSupport code, hsparse⟩
  refine ⟨support, ?_⟩
  exact ⟨matrix.mulVec code,
    mulVec_mem_columnSpan_nonzeroSupport matrix code, rfl⟩

/-- The distance-based best-sparse error lower-bounds the squared Euclidean
error of every actual real `K`-sparse alternative code. -/
theorem bestKSparseSquaredError_le_reconstructionError
    {d M m K : ℕ}
    (source : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin m) ℝ)
    (sourceCode : FeatureVector M) (alternativeCode : FeatureVector m)
    (halternativeSparse : (nonzeroSupport alternativeCode).card ≤ K) :
    bestKSparseSquaredError K source alternative sourceCode ≤
      ENNReal.ofReal
        (squaredEuclideanReconstructionError source alternative
          sourceCode alternativeCode) := by
  apply ENNReal.ofReal_le_ofReal
  dsimp [squaredEuclideanReconstructionError]
  have hdistance_le :
      Metric.infDist
        (representationToEuclidean d (source.mulVec sourceCode))
        (euclideanSparseRepresentationSet K alternative) ≤
      dist
        (representationToEuclidean d (source.mulVec sourceCode))
        (representationToEuclidean d
          (alternative.mulVec alternativeCode)) :=
    Metric.infDist_le_dist_of_mem
      (sparse_mulVec_mem_euclideanSparseRepresentationSet alternative
        alternativeCode halternativeSparse)
  have hinf_nonneg : 0 ≤
      Metric.infDist
        (representationToEuclidean d (source.mulVec sourceCode))
        (euclideanSparseRepresentationSet K alternative) :=
    Metric.infDist_nonneg
  have hdist_nonneg : 0 ≤
      dist
        (representationToEuclidean d (source.mulVec sourceCode))
        (representationToEuclidean d
          (alternative.mulVec alternativeCode)) :=
    dist_nonneg
  nlinarith

/-- The ground-truth matrix has exactly zero population best-sparse loss for
every measure on the universal sparse domain. -/
theorem populationBestKSparseLoss_self_eq_zero
    {d M K : ℕ} (μ : Measure (UniversalSparseDomain M K))
    (matrix : Matrix (Fin d) (Fin M) ℝ) :
    populationBestKSparseLoss μ matrix matrix = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards with code
  rw [bestKSparseSquaredError,
    Metric.infDist_zero_of_mem
      (source_mem_euclideanSparseRepresentationSet matrix code)]
  simp

/-- Zero population loss under a full-support law forces exact sparse
representation at every point of the universal sparse domain. -/
theorem exact_sparse_representation_of_populationBestKSparseLoss_eq_zero
    {d M m K : ℕ} (μ : Measure (UniversalSparseDomain M K))
    [μ.IsOpenPosMeasure]
    (source : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin m) ℝ)
    (hloss : populationBestKSparseLoss μ source alternative = 0) :
    ∀ code : UniversalSparseDomain M K,
      representationToEuclidean d (source.mulVec code.1) ∈
        euclideanSparseRepresentationSet K alternative := by
  have hcontinuous :=
    continuous_bestKSparseSquaredError (K := K) source alternative
  have hmeasurable : AEMeasurable
      (fun code : UniversalSparseDomain M K =>
        bestKSparseSquaredError K source alternative code.1) μ :=
    hcontinuous.aemeasurable
  have hae_zero :
      (fun code : UniversalSparseDomain M K =>
        bestKSparseSquaredError K source alternative code.1) =ᵐ[μ] 0 :=
    (lintegral_eq_zero_iff' hmeasurable).mp hloss
  have heverywhere_zero :
      (fun code : UniversalSparseDomain M K =>
        bestKSparseSquaredError K source alternative code.1) = 0 :=
    (hcontinuous.ae_eq_iff_eq μ continuous_const).mp hae_zero
  intro code
  apply
    (isClosed_euclideanSparseRepresentationSet K alternative).mem_iff_infDist_zero
      (euclideanSparseRepresentationSet_nonempty K alternative) |>.2
  have herror_zero := congrFun heverywhere_zero code
  have hsquare_nonpos :
      (Metric.infDist
        (representationToEuclidean d (source.mulVec code.1))
        (euclideanSparseRepresentationSet K alternative)) ^ 2 ≤ 0 := by
    exact ENNReal.ofReal_eq_zero.mp herror_zero
  have hsquare_zero :
      (Metric.infDist
        (representationToEuclidean d (source.mulVec code.1))
        (euclideanSparseRepresentationSet K alternative)) ^ 2 = 0 :=
    le_antisymm hsquare_nonpos (sq_nonneg _)
  exact (sq_eq_zero_iff).mp hsquare_zero

/-- Membership in an alternative sparse representation set yields an actual
at-most-`K` coefficient vector in the paper's original coordinates. -/
theorem exists_sparse_code_of_mem_euclideanSparseRepresentationSet
    {d m K : ℕ} (alternative : Matrix (Fin d) (Fin m) ℝ)
    (output : RepresentationVector d)
    (houtput : representationToEuclidean d output ∈
      euclideanSparseRepresentationSet K alternative) :
    ∃ code : FeatureVector m,
      (nonzeroSupport code).card ≤ K ∧
        output = alternative.mulVec code := by
  rw [euclideanSparseRepresentationSet, Set.mem_iUnion] at houtput
  obtain ⟨support, houtput⟩ := houtput
  obtain ⟨represented, hrepresented, hequal⟩ := houtput
  rw [← map_mulVecLin_coordinateSpan_eq_columnSpan] at hrepresented
  obtain ⟨code, hcode_span, hcode_eq⟩ := hrepresented
  refine ⟨code, ?_, ?_⟩
  · exact (Finset.card_le_card
      (nonzeroSupport_subset_of_mem_coordinateSpan hcode_span)).trans support.2
  · apply (representationToEuclidean d).injective
    calc
      representationToEuclidean d output =
          representationToEuclidean d represented := hequal.symm
      _ = representationToEuclidean d (alternative.mulVec code) :=
        congrArg (representationToEuclidean d) hcode_eq.symm

/-- The distance-based best-sparse error is attained by an actual real
`K`-sparse code.  Together with
`bestKSparseSquaredError_le_reconstructionError`, this identifies the metric
definition with minimization over the paper's coefficient vectors. -/
theorem exists_sparse_code_attaining_bestKSparseSquaredError
    {d M m K : ℕ}
    (source : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin m) ℝ)
    (sourceCode : FeatureVector M) :
    ∃ alternativeCode : FeatureVector m,
      (nonzeroSupport alternativeCode).card ≤ K ∧
      bestKSparseSquaredError K source alternative sourceCode =
        ENNReal.ofReal
          (squaredEuclideanReconstructionError source alternative
            sourceCode alternativeCode) := by
  let target := euclideanSparseRepresentationSet K alternative
  let sourceOutput := representationToEuclidean d (source.mulVec sourceCode)
  obtain ⟨nearest, hnearest_mem, hnearest_dist⟩ :=
    (isClosed_euclideanSparseRepresentationSet K alternative).exists_infDist_eq_dist
      (euclideanSparseRepresentationSet_nonempty K alternative) sourceOutput
  let output : RepresentationVector d :=
    (representationToEuclidean d).symm nearest
  have houtput_mem : representationToEuclidean d output ∈
      euclideanSparseRepresentationSet K alternative := by
    simpa [output] using hnearest_mem
  obtain ⟨alternativeCode, halternativeSparse, hrepresentation⟩ :=
    exists_sparse_code_of_mem_euclideanSparseRepresentationSet
      alternative output houtput_mem
  refine ⟨alternativeCode, halternativeSparse, ?_⟩
  rw [bestKSparseSquaredError, squaredEuclideanReconstructionError]
  congr 2
  rw [hnearest_dist]
  congr 1
  calc
    nearest = representationToEuclidean d output := by simp [output]
    _ = representationToEuclidean d (alternative.mulVec alternativeCode) :=
      congrArg (representationToEuclidean d) hrepresentation

/-- Zero population loss under a full-support law recovers the source atoms
when `0 < K < M` and the source meets the sharp finite-column cutoff for
sparse-code injectivity. This common endpoint is used by both unrestricted
and unit-column optimizer theorems. The cutoff's sharpness concerns code
injectivity, rather than necessity for every possible column-recovery model.

The measure lives directly on `UniversalSparseDomain M K`; therefore
`IsOpenPosMeasure` means positivity on each nonempty relatively open subset of
the sparse union.  No alternative-side spark or injectivity premise is used. -/
theorem columnsEquivalent_of_populationBestKSparseLoss_eq_zero_of_min_lt_spark
    {d M K : ℕ} (μ : Measure (UniversalSparseDomain M K))
    [μ.IsOpenPosMeasure]
    (source alternative : Matrix (Fin d) (Fin M) ℝ)
    (hKpos : 0 < K)
    (hK_lt_M : K < M)
    (hmin_lt_spark : min (2 * K) M < spark source)
    (hloss : populationBestKSparseLoss μ source alternative = 0) :
    ColumnsEquivalentUpToPermutationAndScaling source alternative := by
  have hexact : ∀ x : UniversalSparseDomain M K,
      ∃ code : FeatureVector M,
        (nonzeroSupport code).card ≤ K ∧
          universalSparseRepresentation source x = alternative.mulVec code := by
    intro x
    apply exists_sparse_code_of_mem_euclideanSparseRepresentationSet alternative
    exact exact_sparse_representation_of_populationBestKSparseLoss_eq_zero
      μ source alternative hloss x
  let alternativeCode : UniversalSparseDomain M K → FeatureVector M :=
    fun x => Classical.choose (hexact x)
  have halternativeSparse : KSparse (K := K) alternativeCode :=
    fun x => (Classical.choose_spec (hexact x)).1
  have halternativeFactors : ∀ x,
      universalSparseRepresentation source x =
        alternative.mulVec (alternativeCode x) :=
    fun x => (Classical.choose_spec (hexact x)).2
  exact equal_size_columnsEquivalent_of_kRich_and_factorizations_of_min_lt_spark
    source universalSparseCode (universalSparseRepresentation source)
    alternative alternativeCode hKpos hK_lt_M hmin_lt_spark
    universalSparseCode_rich (fun _ => rfl)
    halternativeSparse halternativeFactors

/-- Every unrestricted full-width global minimizer under a full-support
probability law recovers the source atoms when `0 < K < M` and the source
meets the sharp sparse-code-injectivity cutoff. -/
theorem global_populationBestKSparseMinimizer_recovers_columns_of_min_lt_spark
    {d M K : ℕ} (μ : Measure (UniversalSparseDomain M K))
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (source alternative : Matrix (Fin d) (Fin M) ℝ)
    (hKpos : 0 < K)
    (hK_lt_M : K < M)
    (hmin_lt_spark : min (2 * K) M < spark source)
    (hoptimal :
      IsGlobalPopulationBestKSparseMinimizer μ source alternative) :
    ColumnsEquivalentUpToPermutationAndScaling source alternative := by
  apply
    columnsEquivalent_of_populationBestKSparseLoss_eq_zero_of_min_lt_spark
      μ source alternative hKpos hK_lt_M hmin_lt_spark
  apply le_antisymm
  · exact (hoptimal source).trans_eq
      (populationBestKSparseLoss_self_eq_zero μ source)
  · exact bot_le

/-- Every full-width unit-column global minimizer under a full-support
probability law recovers a unit-column source when `0 < K < M` and the source
meets the sharp sparse-code-injectivity cutoff. Normalization uses the actual
Euclidean column norm of the population objective. -/
theorem global_unitColumnPopulationBestKSparseMinimizer_recovers_columns_of_min_lt_spark
    {d M K : ℕ} (μ : Measure (UniversalSparseDomain M K))
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (source alternative : Matrix (Fin d) (Fin M) ℝ)
    (hsourceUnit : HasUnitEuclideanColumns source)
    (hKpos : 0 < K)
    (hK_lt_M : K < M)
    (hmin_lt_spark : min (2 * K) M < spark source)
    (hoptimal :
      IsGlobalUnitColumnPopulationBestKSparseMinimizer μ source alternative) :
    ColumnsEquivalentUpToPermutationAndScaling source alternative := by
  apply
    columnsEquivalent_of_populationBestKSparseLoss_eq_zero_of_min_lt_spark
      μ source alternative hKpos hK_lt_M hmin_lt_spark
  apply le_antisymm
  · exact (hoptimal.2 source hsourceUnit).trans_eq
      (populationBestKSparseLoss_self_eq_zero μ source)
  · exact bot_le

/-- Familiar sufficient specialization of full-width population recovery
under `2*K < spark(source)`. -/
theorem global_populationBestKSparseMinimizer_recovers_columns
    {d M K : ℕ} (μ : Measure (UniversalSparseDomain M K))
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (source alternative : Matrix (Fin d) (Fin M) ℝ)
    (hKpos : 0 < K)
    (h2K_lt_spark : 2 * K < spark source)
    (hoptimal :
      IsGlobalPopulationBestKSparseMinimizer μ source alternative) :
    ColumnsEquivalentUpToPermutationAndScaling source alternative := by
  have hK_lt_M : K < M := by
    have hspark_le := spark_le_column_count_succ source
    omega
  exact
    global_populationBestKSparseMinimizer_recovers_columns_of_min_lt_spark
      μ source alternative hKpos hK_lt_M
      ((Nat.min_le_left (2 * K) M).trans_lt h2K_lt_spark) hoptimal

/-! ## An explicit full-support mixture law -/

/-- The canonical inclusion of one exact-`K` coordinate subspace into the
universal at-most-`K` sparse domain. -/
noncomputable def exactSupportInclusion
    {M K : ℕ} (support : CardSubset (Fin M) K) :
    coordinateSpan support.1 → UniversalSparseDomain M K :=
  fun code =>
    ⟨code.1,
      (Finset.card_le_card
        (nonzeroSupport_subset_of_mem_coordinateSpan code.2)).trans_eq support.2⟩

/-- Each exact-support inclusion is continuous for the relative topologies on
the coordinate subspace and universal sparse domain. -/
theorem continuous_exactSupportInclusion
    {M K : ℕ} (support : CardSubset (Fin M) K) :
    Continuous (exactSupportInclusion support) := by
  exact continuous_subtype_val.subtype_mk _

/-- A finite mixture of conditional coefficient laws, one on every exact-`K`
coordinate subspace. -/
noncomputable def universalSparseSupportMixture
    {M K : ℕ}
    (weights : CardSubset (Fin M) K → ENNReal)
    (conditional : ∀ support : CardSubset (Fin M) K,
      Measure (coordinateSpan support.1)) :
    Measure (UniversalSparseDomain M K) :=
  ∑ support,
    weights support •
      Measure.map (exactSupportInclusion support) (conditional support)

/-- Probability conditionals and weights summing to one make the explicit
support mixture a probability measure. -/
theorem universalSparseSupportMixture_isProbabilityMeasure
    {M K : ℕ}
    (weights : CardSubset (Fin M) K → ENNReal)
    (conditional : ∀ support : CardSubset (Fin M) K,
      Measure (coordinateSpan support.1))
    (hconditionalProbability : ∀ support,
      IsProbabilityMeasure (conditional support))
    (hweights : ∑ support, weights support = 1) :
    IsProbabilityMeasure
      (universalSparseSupportMixture weights conditional) := by
  constructor
  rw [universalSparseSupportMixture, Measure.finset_sum_apply]
  calc
    (∑ support,
      (weights support •
        Measure.map (exactSupportInclusion support)
          (conditional support)) Set.univ) =
        ∑ support, weights support := by
      apply Finset.sum_congr rfl
      intro support _hsupport
      rw [Measure.smul_apply, smul_eq_mul,
        Measure.map_apply
          (continuous_exactSupportInclusion support).measurable
          MeasurableSet.univ,
        Set.preimage_univ, (hconditionalProbability support).measure_univ,
        mul_one]
    _ = 1 := hweights

/-- If `K ≤ M`, positive mixture weights and relatively open-positive
conditional laws make the explicit support mixture positive on every
nonempty relatively open subset of `UniversalSparseDomain M K`.

This is the promised concrete full-support distribution bridge.  It does not
assume full support of the mixture itself. -/
theorem universalSparseSupportMixture_isOpenPosMeasure
    {M K : ℕ}
    (weights : CardSubset (Fin M) K → ENNReal)
    (conditional : ∀ support : CardSubset (Fin M) K,
      Measure (coordinateSpan support.1))
    (hK_le_M : K ≤ M)
    (hweightsPositive : ∀ support, weights support ≠ 0)
    (hconditionalOpenPos : ∀ support,
      (conditional support).IsOpenPosMeasure) :
    (universalSparseSupportMixture weights conditional).IsOpenPosMeasure := by
  constructor
  intro U hU hU_nonempty
  obtain ⟨x, hxU⟩ := hU_nonempty
  obtain ⟨coordinates, hsupport_subset, _hcoordinates_subset, hcoordinates_card⟩ :=
    Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (nonzeroSupport x.1)) x.2
      (by simpa using hK_le_M)
  let support : CardSubset (Fin M) K :=
    ⟨coordinates, hcoordinates_card⟩
  have hx_span : x.1 ∈ coordinateSpan support.1 :=
    mem_coordinateSpan_of_nonzeroSupport_subset hsupport_subset
  let supportPoint : coordinateSpan support.1 := ⟨x.1, hx_span⟩
  have hinclusion_point : exactSupportInclusion support supportPoint = x := by
    apply Subtype.ext
    rfl
  have hpreimage_open :
      IsOpen (exactSupportInclusion support ⁻¹' U) :=
    hU.preimage (continuous_exactSupportInclusion support)
  have hpreimage_nonempty :
      (exactSupportInclusion support ⁻¹' U).Nonempty := by
    refine ⟨supportPoint, ?_⟩
    change exactSupportInclusion support supportPoint ∈ U
    rwa [hinclusion_point]
  have hconditional_ne_zero :
      conditional support (exactSupportInclusion support ⁻¹' U) ≠ 0 :=
    (hconditionalOpenPos support).open_pos _ hpreimage_open hpreimage_nonempty
  have hmap_ne_zero :
      Measure.map (exactSupportInclusion support) (conditional support) U ≠ 0 := by
    rw [Measure.map_apply
      (continuous_exactSupportInclusion support).measurable hU.measurableSet]
    exact hconditional_ne_zero
  have hterm_ne_zero :
      (weights support •
        Measure.map (exactSupportInclusion support) (conditional support)) U ≠ 0 := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact mul_ne_zero (hweightsPositive support) hmap_ne_zero
  have hterm_le :
      (weights support •
        Measure.map (exactSupportInclusion support) (conditional support)) U ≤
      universalSparseSupportMixture weights conditional U := by
    rw [universalSparseSupportMixture, Measure.finset_sum_apply]
    exact Finset.single_le_sum
      (f := fun candidate : CardSubset (Fin M) K =>
        (weights candidate •
          Measure.map (exactSupportInclusion candidate)
            (conditional candidate)) U)
      (fun _ _ => zero_le _) (Finset.mem_univ support)
  intro hmixture_zero
  apply hterm_ne_zero
  exact bot_unique (hterm_le.trans_eq hmixture_zero)

end PKG26AtomicFeatures
