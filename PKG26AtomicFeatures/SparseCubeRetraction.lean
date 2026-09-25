import PKG26AtomicFeatures.RepresentationOptimizationModel
import PKG26AtomicFeatures.HierarchicalPopulationModel
import PKG26AtomicFeatures.MesoscalePopulationModel
import PKG26AtomicFeatures.MesoscaleWidthThreeRecovery

/-!
# A source domain realizing the full atomic sparse cube

Retraction to the sparse unit cube gives a measurable source feature map
whose range is exactly the postulate's cube. On every population supported
in that cube the representation equals the original coefficient vector
almost everywhere. Composing learned encoders with this representation
therefore preserves actual loss while making the representation dependence
explicit.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set

theorem measurableSet_sparseUnitCube (M K : ℕ) : MeasurableSet (SparseUnitCube M K) := by
  have hs : MeasurableSet {v : FeatureVector M | (nonzeroSupport v).card ≤ K} :=
    (measurable_nonzeroSupport_comp (id : FeatureVector M → FeatureVector M) measurable_id)
      (t := {S | S.card ≤ K}) (by trivial)
  have hb : MeasurableSet {v : FeatureVector M | ∀ i, 0 ≤ v i ∧ v i ≤ 1} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_le measurable_const (measurable_pi_apply i)).inter
        (measurableSet_le (measurable_pi_apply i) measurable_const)
  exact hs.inter hb

theorem zero_mem_sparseUnitCube (M K : ℕ) : (0 : FeatureVector M) ∈ SparseUnitCube M K := by
  simp [SparseUnitCube, nonzeroSupport]

/-- Identity on the entire sparse cube, with zero as the value off it. -/
noncomputable def sparseCubeRetraction (M K : ℕ) (v : FeatureVector M) : FeatureVector M := by
  classical
  exact if v ∈ SparseUnitCube M K then v else 0

theorem measurable_sparseCubeRetraction (M K : ℕ) : Measurable (sparseCubeRetraction M K) := by
  classical
  exact measurable_id.ite (measurableSet_sparseUnitCube M K) measurable_const

theorem sparseCubeRetraction_eq_self {M K : ℕ} {v : FeatureVector M}
    (hv : v ∈ SparseUnitCube M K) : sparseCubeRetraction M K v = v := by
  classical
  exact if_pos hv

theorem sparseCubeRetraction_mem (M K : ℕ) (v : FeatureVector M) :
    sparseCubeRetraction M K v ∈ SparseUnitCube M K := by
  unfold sparseCubeRetraction
  split_ifs with hv
  · exact hv
  · exact zero_mem_sparseUnitCube M K

theorem range_sparseCubeRetraction (M K : ℕ) :
    Set.range (sparseCubeRetraction M K) = SparseUnitCube M K := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact sparseCubeRetraction_mem M K x
  · intro hv
    exact ⟨v, sparseCubeRetraction_eq_self hv⟩

/-- The identity dictionary and sparse-cube retraction realize every
coefficient vector required by the Atomic Postulate. -/
theorem atomicPostulate_sparseCubeRetraction (M K : ℕ) (γ : ℝ) (hγ : γ ≤ 1) :
    AtomicPostulate (1 : Matrix (Fin M) (Fin M) ℝ)
      (sparseCubeRetraction M K) (sparseCubeRetraction M K) γ K :=
  ⟨identityDictionary_unit M, identityDictionary_stable M (2 * K) γ hγ,
    range_sparseCubeRetraction M K, fun _ => (Matrix.one_mulVec _).symm⟩

theorem identityDictionary_orthonormal (M : ℕ) :
    Orthonormal ℝ (fun j => representationToEuclidean M ((1 : Matrix (Fin M) (Fin M) ℝ).col j)) := by
  have heq : (fun j => representationToEuclidean M ((1 : Matrix (Fin M) (Fin M) ℝ).col j)) =
      (fun j : Fin M => EuclideanSpace.single j (1 : ℝ)) := by
    funext j
    ext i
    simp [representationToEuclidean, Matrix.col, Matrix.one_apply, eq_comm]
  rw [heq]
  exact EuclideanSpace.orthonormal_single

theorem sparseCubeRetraction_idempotent (M K : ℕ) (v : FeatureVector M) :
    sparseCubeRetraction M K (sparseCubeRetraction M K v) = sparseCubeRetraction M K v :=
  sparseCubeRetraction_eq_self (sparseCubeRetraction_mem M K v)

theorem sparseCubeRetraction_ae_eq_id {M K : ℕ} (μ : Measure (FeatureVector M))
    (hsupport : ∀ᵐ v ∂μ, v ∈ SparseUnitCube M K) : sparseCubeRetraction M K =ᵐ[μ] id :=
  hsupport.mono fun _ hv => sparseCubeRetraction_eq_self hv

/-- The constructed, positively scaled population obeys the full bounded
source codomain almost surely. -/
theorem mesoscaleScaledPopulationLaw_ae_sparseUnitCube (δ θ H η : ℝ)
    (hH : 1 ≤ H) (hη : 0 < η) (hηone : η ≤ 1) :
    ∀ᵐ z ∂mesoscaleScaledPopulationLaw δ θ H η, z ∈ SparseUnitCube 3 2 := by
  filter_upwards [mesoscaleScaledPopulationLaw_ae_unitCube δ θ H η hH hη hηone,
    mesoscaleScaledPopulationLaw_ae_support_card δ θ H η hH hη] with z hb hs
  exact ⟨hs.le, hb⟩

/-- Composing a feasible feature map with a measurable representation
preserves all global encoder constraints. -/
theorem IsFeasibleRecoveryPair.comp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d m K : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} {u : Ω → FeatureVector m} {γ : ℝ}
    (hu : IsFeasibleRecoveryPair B u γ K) (f : Ω' → Ω) (hf : Measurable f) :
    IsFeasibleRecoveryPair B (u ∘ f) γ K :=
  ⟨hu.1, hu.2.1, hu.2.2.1.comp hf, fun x => hu.2.2.2.1 (f x),
    fun x j => hu.2.2.2.2 (f x) j⟩

/-- Actual losses ignore null-set changes in either source or learned code. -/
theorem actualPopulationSquaredLoss_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] {d M m : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    {z z' : Ω → FeatureVector M} {u u' : Ω → FeatureVector m}
    (hz : z =ᵐ[μ] z') (hu : u =ᵐ[μ] u') :
    actualPopulationSquaredLoss μ A z B u = actualPopulationSquaredLoss μ A z' B u' := by
  apply lintegral_congr_ae
  filter_upwards [hz, hu] with x hx hu
  rw [hx, hu]

/-- Every attained ambient optimum supplies an attained optimum whose
encoder explicitly factors through an almost-sure identity representation. -/
theorem IsApproximatelyOptimalRecoveryPair.comp_ae_identity
    {d m K : ℕ} {μ : Measure (FeatureVector d)}
    {B : Matrix (Fin d) (Fin m) ℝ} {u : FeatureVector d → FeatureVector m} {γ C : ℝ}
    (hopt : IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin d) (Fin d) ℝ) id B u γ C K)
    (f : FeatureVector d → FeatureVector d) (hf : Measurable f) (hfid : f =ᵐ[μ] id) :
    IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin d) (Fin d) ℝ) f B (u ∘ f) γ C K := by
  refine ⟨hopt.1.comp f hf, ?_⟩
  intro B' u' hu'
  have hucomp : u ∘ f =ᵐ[μ] u := hfid.mono fun x hx => congrArg u hx
  rw [actualPopulationSquaredLoss_congr_ae μ 1 B hfid hucomp,
    actualPopulationSquaredLoss_congr_ae μ 1 B' hfid Filter.EventuallyEq.rfl]
  exact hopt.2 B' u' hu'

/-- If a representation is the identity almost surely, optimality over
encoders depending on that representation implies optimality against every
feasible measurable encoder. Each unrestricted competitor is composed with
the representation to produce the required admissible competitor. -/
theorem isApproximatelyOptimalRecoveryPair_of_representation_comparisons
    {d m K : ℕ} (μ : Measure (FeatureVector d))
    (f : FeatureVector d → FeatureVector d) (hf : Measurable f) (hfid : f =ᵐ[μ] id)
    (B : Matrix (Fin d) (Fin m) ℝ) (g : FeatureVector d → FeatureVector m) (γ C : ℝ)
    (hfeas : IsFeasibleRecoveryPair B (g ∘ f) γ K)
    (hopt : ∀ (B' : Matrix (Fin d) (Fin m) ℝ) (g' : FeatureVector d → FeatureVector m),
      IsFeasibleRecoveryPair B' (g' ∘ f) γ K →
      actualPopulationSquaredLoss μ (1 : Matrix (Fin d) (Fin d) ℝ) f B (g ∘ f) ≤
        ENNReal.ofReal C * actualPopulationSquaredLoss μ 1 f B' (g' ∘ f)) :
    IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin d) (Fin d) ℝ) id B (g ∘ f) γ C K := by
  refine ⟨hfeas, ?_⟩
  intro B' u' hu'
  have hcmp := hopt B' u' (hu'.comp f hf)
  have hucomp : u' ∘ f =ᵐ[μ] u' := hfid.mono fun x hx => congrArg u' hx
  rw [actualPopulationSquaredLoss_congr_ae μ 1 B hfid Filter.EventuallyEq.rfl,
    actualPopulationSquaredLoss_congr_ae μ 1 B' hfid hucomp] at hcmp
  exact hcmp

/-- The restricted representation-based optimum has exactly the same
population behavior as an ambient optimum when the representation equals
the coefficient vector almost everywhere. -/
theorem IsOptimalRepresentationPair.ambient_of_ae_identity
    {d m K : ℕ} {μ : Measure (FeatureVector d)}
    {f : FeatureVector d → FeatureVector d} (hf : Measurable f) (hfid : f =ᵐ[μ] id)
    {B : Matrix (Fin d) (Fin m) ℝ} {g : FeatureVector d → FeatureVector m} {γ : ℝ}
    (hopt : IsOptimalRepresentationPair μ (1 : Matrix (Fin d) (Fin d) ℝ) f f B g γ K) :
    IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin d) (Fin d) ℝ) id B (g ∘ f) γ 1 K := by
  apply isApproximatelyOptimalRecoveryPair_of_representation_comparisons μ f hf hfid B g γ 1 hopt.1
  intro B' g' hg'
  simpa only [ENNReal.ofReal_one, one_mul] using hopt.2 B' g' hg'

theorem IsApproximatelyOptimalRecoveryPair.representation_of_ae_identity
    {d m K : ℕ} {μ : Measure (FeatureVector d)}
    {B : Matrix (Fin d) (Fin m) ℝ} {u : FeatureVector d → FeatureVector m} {γ : ℝ}
    (hopt : IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin d) (Fin d) ℝ) id B u γ 1 K)
    (f : FeatureVector d → FeatureVector d) (hf : Measurable f) (hfid : f =ᵐ[μ] id) :
    IsOptimalRepresentationPair μ (1 : Matrix (Fin d) (Fin d) ℝ) f f B u γ K := by
  have h := hopt.comp_ae_identity f hf hfid
  refine ⟨h.1, ?_⟩
  intro B' g' hg'
  simpa only [ENNReal.ofReal_one, one_mul] using h.2 B' (g' ∘ f) hg'

/-- The infima over all ambient encoders and over representation-dependent
encoders coincide. This equality does not assume attainment. -/
theorem optimalRepresentationLoss_eq_ambient_of_ae_identity {d m K : ℕ}
    (μ : Measure (FeatureVector d)) (f : FeatureVector d → FeatureVector d)
    (hf : Measurable f) (hfid : f =ᵐ[μ] id) (γ : ℝ) :
    optimalRepresentationLoss μ (1 : Matrix (Fin d) (Fin d) ℝ) f f γ K m =
      optimalRecoveryLoss μ (1 : Matrix (Fin d) (Fin d) ℝ) id γ K m := by
  apply le_antisymm
  · unfold optimalRecoveryLoss
    refine le_iInf fun B => le_iInf fun u => le_iInf fun hu => ?_
    have hcomp : u ∘ f =ᵐ[μ] u := hfid.mono fun x hx => congrArg u hx
    have hle : optimalRepresentationLoss μ 1 f f γ K m ≤ actualPopulationSquaredLoss μ 1 f B (u ∘ f) :=
      iInf_le_of_le B (iInf_le_of_le u (iInf_le_of_le (hu.comp f hf) le_rfl))
    rwa [actualPopulationSquaredLoss_congr_ae μ 1 B hfid hcomp] at hle
  · unfold optimalRepresentationLoss
    refine le_iInf fun B => le_iInf fun g => le_iInf fun hg => ?_
    rw [actualPopulationSquaredLoss_congr_ae μ 1 B hfid Filter.EventuallyEq.rfl]
    exact iInf_le_of_le B (iInf_le_of_le (g ∘ f) (iInf_le_of_le hg le_rfl))

theorem singleCoordinateF1Sup_ae_identity_source {d m : ℕ}
    (μ : Measure (FeatureVector d)) {f : FeatureVector d → FeatureVector d}
    (hfid : f =ᵐ[μ] id) (u : FeatureVector d → FeatureVector m) (i : Fin d) :
    singleCoordinateF1Sup μ {x | 0 < f x i} u = singleCoordinateF1Sup μ {x | 0 < x i} u := by
  apply singleCoordinateF1Sup_congr_truth_ae
  filter_upwards [hfid] with x hx
  change (0 < f x i) = (0 < x i)
  rw [hx]
  rfl

end PKG26AtomicFeatures
