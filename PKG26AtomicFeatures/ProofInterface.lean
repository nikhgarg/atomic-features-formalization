import PKG26AtomicFeatures.PaperInterface
import PKG26AtomicFeatures.TailRecoveryPrinciple
import PKG26AtomicFeatures.CommonRecoveryPredictions
import PKG26AtomicFeatures.RankedRecoveryPredictions
import PKG26AtomicFeatures.RegularHierarchicalRecovery
import PKG26AtomicFeatures.LocalSupportRecovery
import PKG26AtomicFeatures.ActivationTransfer
import PKG26AtomicFeatures.MesoscaleSourceWitness
import PKG26AtomicFeatures.MesoscaleArbitrarySource
import PKG26AtomicFeatures.RegularSupportRecovery
import PKG26AtomicFeatures.HierarchyRichness

/-!
# Proof Interface: A Testable Theory of Atomic Features

This file contains exact-type proof endpoints for the transparent propositions
in `PaperInterface.lean`. It is not a human semantic-review surface: one source
claim is reviewed once, against its expanded `...Spec : Prop` declaration.
-/

namespace PKG26AtomicFeatures

theorem sparseRecovery : SparseRecoverySpec := by
  intro X d M K matrix code f h x v hv hsparse
  exact featurization_unique_sparse_representation h x v hv hsparse

theorem rigidity : RigiditySpec := by
  intro X d M K γ A z f hK hKM hγ hsource hrich M' K' γ' B u hγ' halt hpareto
  obtain ⟨hsparsity, hequal, hwidth⟩ := atomic_rigidity_of_openRich A z B u f hK hKM
    (hsource.1.sparseInjective hγ) (halt.1.sparseInjective hγ')
    hsource.2.1 hrich hsource.2.2.2 halt.2.1 halt.2.2.2
  by_cases hM' : M' < M
  · exact Or.inr (hwidth hM')
  · have hMle : M ≤ M' := Nat.le_of_not_gt hM'
    have heqM : M' = M := by
      by_contra hne
      exact hpareto ⟨hMle, hsparsity, Or.inl (by omega)⟩
    have heqK : K' = K := by
      by_contra hne
      exact hpareto ⟨hMle, hsparsity, Or.inr (by omega)⟩
    exact Or.inl (hequal heqM heqK)

/-- Direction and activation recovery for every qualifying positive-prevalence atom. -/
theorem uniformPositivePrevalenceRecovery : UniformPositivePrevalenceRecoverySpec := by
  classical
  intro K γ ρ cLower cUpper C₀ η hK hγ hγone hρ hcLower hcUpper hC₀ hηone
  let η' : ℝ := max η (1 / 2)
  have hηη' : η ≤ η' := le_max_left _ _
  have hη' : 0 < η' :=
    (show (0 : ℝ) < 1 / 2 by norm_num).trans_le (le_max_right _ _)
  have hη'one : η' < 1 := max_lt hηone (by norm_num)
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  obtain ⟨t, C, ht, hC, hrec⟩ := exists_tail_recovery_constants
    K γ ρ cLower cUpper C₀ η' hK hγ hγone hρ hcLower
      (hcLower.trans_le hcUpper) hC₀pos hη' hη'one
  refine ⟨C, t, hC, ht, ?_⟩
  intro X _ μ _ d M m A z f _hKM hAunit hsource hreg σ _hsorted hm B code hfeas hloss i hpi htail
  have hopt : IsApproximatelyOptimalRecoveryPair μ A z B code γ C₀ K :=
    (isApproximatelyOptimalRecoveryPair_iff_loss_le_infimum μ A z B code γ C₀ hC₀pos).mpr
      ⟨hfeas, hloss⟩
  obtain ⟨e, he⟩ := hrec X μ d M m A z hreg hAunit hsource.1
    σ hm B code hopt
  let i' : tailRecoverableFeatures (featurePrevalence μ z) σ C m :=
    ⟨i, (mem_tailRecoverableFeatures _ σ C m i).mpr ⟨hpi, htail⟩⟩
  exact ⟨e i', hηη'.trans_lt (he i').1, hηη'.trans_lt (he i').2⟩

/-- The paper's separate direction and activation witnesses follow from the
uniform construction, without requiring those witnesses to coincide. -/
theorem positivePrevalenceRecovery : PositivePrevalenceRecoverySpec := by
  intro K γ ρ cLower cUpper C₀ η hK hγ hγone hρ hcLower hcUpper hC₀ hηone
  obtain ⟨C, t, hC, _ht, hrec⟩ := uniformPositivePrevalenceRecovery
    K γ ρ cLower cUpper C₀ η hK hγ hγone hρ hcLower hcUpper hC₀ hηone
  refine ⟨C, hC, ?_⟩
  intro X _ μ _ d M m A z f hKM hAunit hsource hreg σ hsorted hm B code hfeas hloss i hpi htail
  obtain ⟨j, hdir, hact⟩ := hrec X μ d M m A z f hKM hAunit hsource hreg
    σ hsorted hm B code hfeas hloss i hpi htail
  refine ⟨⟨j, ?_⟩, ⟨j, t, hact⟩⟩
  simpa only [real_inner_comm] using hdir

/-- The actual recovery theorem and both ranked matching predictions use
one constant; the second population retains its own recovery prefix. -/
theorem positivePrevalenceRecoveryPredictions : PositivePrevalenceRecoveryPredictionsSpec := by
  classical
  intro K γ ρ cLower cUpper C₀ η hK hγ hγone hρ hcLower hcUpper hC₀ hη hηone
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  obtain ⟨t, C, ht, hC, hrec⟩ := exists_common_recovery_prediction_constants
    K γ ρ cLower cUpper C₀ (matchingRecoveryConfidence γ η) η hK hγ hγone hρ hcLower
      (hcLower.trans_le hcUpper) hC₀pos (matchingRecoveryConfidence_pos hη hηone)
      (matchingRecoveryConfidence_lt_one hγ hη) hη hηone
  refine ⟨C, t, hC, ht, ?_⟩
  intro X _ μ _ d M m A z f _hKM hAunit hsource hreg σ hsorted _hmpos hm B code hfeas hloss
  have hopt : IsApproximatelyOptimalRecoveryPair μ A z B code γ C₀ K :=
    (isApproximatelyOptimalRecoveryPair_iff_loss_le_infimum μ A z B code γ C₀ hC₀pos).mpr
      ⟨hfeas, hloss⟩
  obtain ⟨hrecovery, hsize, hdata⟩ := hrec X μ d M m A z hreg hAunit hsource.1
    σ hm B code hopt
  refine ⟨hrecovery, ?_, ?_⟩
  · intro s width hwidth hwidthM B' code' hfeas' hloss'
    have h := hsize (Fin s) width hwidth hwidthM B' code' (fun l =>
      (isApproximatelyOptimalRecoveryPair_iff_loss_le_infimum
        μ A z (B' l) (code' l) γ C₀ hC₀pos).mpr ⟨hfeas' l, hloss' l⟩)
    rwa [tailRecoverableFeatures_card_eq_rank _ σ hsorted] at h
  · intro μ' _ hreg' σ' hsorted' B' code' hfeas' hloss'
    have h := hdata μ' hreg' σ' B' code'
      ((isApproximatelyOptimalRecoveryPair_iff_loss_le_infimum
        μ' A z B' code' γ C₀ hC₀pos).mpr ⟨hfeas', hloss'⟩)
    rwa [tailRecoverableFeatures_eq_image_rank_filter _ σ hsorted,
      tailRecoverableFeatures_eq_image_rank_filter _ σ' hsorted'] at h

/-- Translating a prescribed cosine threshold into a distance tolerance
keeps the public P1/P2 statements in the paper's parameterization. -/
private theorem matching_tolerance {t : ℝ} (ht : 0 < t) (htone : t < 1) :
    0 < Real.sqrt ((1 - t) / 2) ∧ Real.sqrt ((1 - t) / 2) < 1 ∧
      1 - 2 * Real.sqrt ((1 - t) / 2) ^ 2 = t := by
  have hpos : 0 < (1 - t) / 2 := by linarith
  have hsq := Real.sq_sqrt hpos.le
  refine ⟨Real.sqrt_pos.2 hpos, ?_, ?_⟩
  · nlinarith [Real.sqrt_nonneg ((1 - t) / 2)]
  · linarith

/-- Lowering the signed cosine threshold can only enlarge the maximum
simultaneous matching. -/
private theorem testableMatchingMetric_antitone
    {ι : Type*} {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ) {s t : ℝ} (hst : s ≤ t) :
    testableMatchingMetric width B C t ≤ testableMatchingMetric width B C s := by
  obtain ⟨J, hJ, hcard⟩ := testableMatchingMetric_attained width B C t
  rw [← hcard]
  apply card_le_testableMatchingMetric width B C s J
  intro l
  obtain ⟨e, he⟩ := hJ l
  exact ⟨e, fun j => hst.trans (he j)⟩

/-- P1 is the size conclusion of the common recovery-and-matching theorem. -/
theorem positivePrevalenceSizeStability : PositivePrevalenceSizeStabilitySpec := by
  intro K γ ρ cLower cUpper C₀ t hK hγ hγone hρ hcLower hcUpper hC₀ htone
  let t' : ℝ := max t (1 / 2)
  have htt' : t ≤ t' := le_max_left _ _
  have ht' : 0 < t' :=
    (show (0 : ℝ) < 1 / 2 by norm_num).trans_le (le_max_right _ _)
  have ht'one : t' < 1 := max_lt htone (by norm_num)
  obtain ⟨hε, hεone, hthreshold⟩ := matching_tolerance ht' ht'one
  obtain ⟨C, τ, hC, _hτ, hpred⟩ := positivePrevalenceRecoveryPredictions
    K γ ρ cLower cUpper C₀ (Real.sqrt ((1 - t') / 2))
    hK hγ hγone hρ hcLower hcUpper hC₀ hε hεone
  refine ⟨C, hC, ?_⟩
  intro X _ μ _ d M m A z f hKM hAunit hsource hreg σ hsorted hmpos hm B code hfeas hloss
  have hsize := (hpred X μ d M m A z f hKM hAunit hsource hreg σ hsorted
    hmpos hm B code hfeas hloss).2.1
  intro s width hwidth hwidthM B' code' hfeas' hloss'
  have hsize' := hsize s width hwidth hwidthM B' code' hfeas' hloss'
  rw [hthreshold] at hsize'
  exact hsize'.trans (testableMatchingMetric_antitone width B B' htt')

/-- P2 retains the separately computed prefixes of the two populations. -/
theorem positivePrevalenceDataStability : PositivePrevalenceDataStabilitySpec := by
  intro K γ ρ cLower cUpper C₀ t hK hγ hγone hρ hcLower hcUpper hC₀ htone
  let t' : ℝ := max t (1 / 2)
  have htt' : t ≤ t' := le_max_left _ _
  have ht' : 0 < t' :=
    (show (0 : ℝ) < 1 / 2 by norm_num).trans_le (le_max_right _ _)
  have ht'one : t' < 1 := max_lt htone (by norm_num)
  obtain ⟨hε, hεone, hthreshold⟩ := matching_tolerance ht' ht'one
  obtain ⟨C, τ, hC, _hτ, hpred⟩ := positivePrevalenceRecoveryPredictions
    K γ ρ cLower cUpper C₀ (Real.sqrt ((1 - t') / 2))
    hK hγ hγone hρ hcLower hcUpper hC₀ hε hεone
  refine ⟨C, hC, ?_⟩
  intro X _ μ _ d M m A z f hKM hAunit hsource hreg σ hsorted hmpos hm B code hfeas hloss
  have hdata := (hpred X μ d M m A z f hKM hAunit hsource hreg σ hsorted
    hmpos hm B code hfeas hloss).2.2
  intro μ' _ hreg' σ' hsorted' B' code' hfeas' hloss'
  have hdata' := hdata μ' hreg' σ' hsorted' B' code' hfeas' hloss'
  rw [hthreshold] at hdata'
  exact hdata'.trans
    (testableMatchingMetric_antitone (fun _ : Unit => m) B (fun _ => B') htt')

/-- Hierarchical activation recovery follows from the actual sampling
law and an explicit feasible whole-family comparator. -/
theorem uniformHierarchicalRecovery : UniformHierarchicalRecoverySpec := by
  classical
  intro L γ ρ κ cLower cUpper C₀ η hL hγ hγone _hρ hκ hκhalf hcLower hcUpper hC₀ hηone
  let η' : ℝ := max η (1 / 2)
  have hηη' : η ≤ η' := le_max_left _ _
  have hη'one : η' < 1 := max_lt hηone (by norm_num)
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  obtain ⟨t, C, ht, hC, hrec⟩ := exists_regular_hierarchical_tail_recovery_constants
    L γ ρ κ cLower cUpper C₀ η' hL hγ hγone hκ hκhalf
      (hcLower.trans_le hcUpper) hC₀pos hη'one
  refine ⟨C, t, hC, ht, ?_⟩
  intro X _ μ d N m A z f w _hLN hAunit hsource hmodel σ _hsorted hm B code hfeas hloss
  obtain ⟨e, he⟩ := hrec X μ d N m w A z hmodel hAunit hsource.1 σ hm B code hfeas hloss
  intro i hpi htail
  let i' : tailRecoverableFeatures (fun k => featurePrevalence μ z (hierarchicalParent k))
      σ C (m / 3) := ⟨i, (mem_tailRecoverableFeatures _ σ C (m / 3) i).mpr ⟨hpi, htail⟩⟩
  exact ⟨fun role => e (i', role), hηη'.trans_lt (he (i', 0)),
    fun k => hηη'.trans_lt (he (i', k.succ))⟩

/-- The source conclusion permits separate activation witnesses for each role. -/
theorem hierarchicalRecovery : HierarchicalRecoverySpec := by
  intro L γ ρ κ cLower cUpper C₀ η hL hγ hγone hρ hκ hκhalf hcLower hcUpper hC₀ hηone
  obtain ⟨C, t, hC, _ht, hrec⟩ := uniformHierarchicalRecovery
    L γ ρ κ cLower cUpper C₀ η hL hγ hγone hρ hκ hκhalf hcLower hcUpper hC₀ hηone
  refine ⟨C, hC, ?_⟩
  intro X _ μ d N m A z f w hLN hAunit hsource hmodel σ hsorted hm B code hfeas hloss i hpi htail
  obtain ⟨j, hp, hc⟩ := hrec X μ d N m A z f w hLN hAunit hsource hmodel
    σ hsorted hm B code hfeas hloss i hpi htail
  exact ⟨⟨j 0, t, hp⟩, fun k => ⟨j k.succ, t, hc k⟩⟩

/-- A fixed canonical atomic representation exhibits the source's entire
mesoscale feature table at every tolerance, for all reconstruction optima. -/
theorem canonicalMesoscaleFeatureSplittingProof : CanonicalMesoscaleFeatureSplittingSpec :=
  canonicalMesoscaleFeatureSplitting

/-- Every fixed orthonormal atomic source admits the mesoscale population;
the representation-dependent lexicographic optima and exact loss ordering
are part of the conclusion. -/
theorem mesoscaleFeatureSplitting : MesoscaleFeatureSplittingSpec := by
  intro X _ d A z f hz hpost hA ε hε _hεthird
  obtain ⟨μ, hμ, hfamily, hattain, hone, htwo, hthree, hzero, h32, h21⟩ :=
    mesoscaleFeatureSplittingForOrthonormalSource A z f hz hpost.toAtomicPostulate hA ε hε
  exact ⟨μ, hμ, hfamily, hattain,
    fun B g hopt => hone B g hopt.1,
    fun B g hopt => htwo B g hopt.1,
    fun B g hopt => hthree B g hopt.1, hzero, h32, h21⟩

/-- The conditional-loss cutoff comes from the actual source-support law;
the learned span has the requested accuracy independently of both widths. -/
theorem conditionalSpanRecovery : ConditionalSpanRecoverySpec := by
  intro K γ cLower ε hK hγ hγone hcLower hε
  exact exists_local_support_recovery_threshold K γ cLower ε hK hγ hγone hcLower hε

/-- The upper density bound controls small projected coefficients; sparse
stability transfers this to the actual learned coordinate and its F1. -/
theorem activationTransfer : ActivationTransferSpec := by
  intro K γ cUpper η hK hγ hcUpper hη hηone
  exact exists_activation_transfer_constants K γ cUpper η hK hγ hcUpper hη hηone

/-- The common stability margin gives the exact intersection factor
`1 + 2K/γ`, with no dependence on the number of support pairs. -/
theorem stableSupportIntersection : StableSupportIntersectionSpec := by
  intro ι d M m K γ r A B _hK hγ hr hAunit hBunit hA hB S T family
    hfamily hS hT hgap hsmall
  have hsmall' : (1 + 2 * (K : ℝ) / γ) * r < 1 := by
    simpa only [mul_comm] using hsmall
  refine ⟨support_intersection_card_eq_of_projector_bounds A B γ γ r
    (fun i => (hAunit i).le) (fun j => (hBunit j).le) hA hB hγ hγ hr
    hsmall' hsmall' S T family hfamily (fun i hi => (hS i hi).le)
    (fun i hi => (hT i hi).le) hgap, ?_⟩
  have hbound := support_intersection_projector_bound A B γ γ r
    (fun i => (hAunit i).le) (fun j => (hBunit j).le) hA hB hγ hγ hr
    S T family hfamily (fun i hi => (hS i hi).le)
    (fun i hi => (hT i hi).le) hgap
  simpa only [max_self, mul_comm] using hbound

theorem localToGlobalHall : LocalToGlobalHallSpec := by
  intro Left Right K edges hK hlower hupper
  exact LocalGlobalHall.local_to_global_hall edges K hK hlower hupper

theorem subspaceInclusion : SubspaceInclusionSpec := by
  intro X d M M' K K' matrix code alternative alternativeCode f _hsparse hf hrich hu hBu
  exact sparse_factorization_subspace_union_inclusion hf hrich hu hBu

theorem hierarchyRichness : HierarchyRichnessSpec := by
  refine ⟨?_, ?_⟩
  · intro X M K z hK hKM hsparse hnonneg child parent hne hhierarchy
    exact not_openKRich_of_perfect_hierarchy z hK hKM hsparse hnonneg
      child parent hne hhierarchy
  · exact ⟨1, hierarchyAlternativeMatrix, hierarchySourceCode,
      hierarchyAlternativeCode, hierarchy_refutes_rigidity_without_richness⟩

theorem genericRigidity : GenericRigiditySpec := by
  intro n M K hn hM hK hKM
  filter_upwards [ae_sphericalProjectiveDimensionGeneric n M] with source hgeneric
  intro X code f _hsparse hf hrich M' K' γ' hwidth hγ' alternative alternativeCode hu hBu hstable
  have hcutoff := hstable.min_lt_spark hγ'
  have hambient := spark_le_ambient_dimension_succ alternative
  have hspark : 2 * K' < spark alternative := by omega
  exact generic_featurization_bounds source code f alternative alternativeCode
    hn (by omega) hK hKM hgeneric hf hrich ⟨hu, hBu, hspark⟩

end PKG26AtomicFeatures
