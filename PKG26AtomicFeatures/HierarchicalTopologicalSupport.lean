import PKG26AtomicFeatures.MesoscalePositiveLoss
import Mathlib.MeasureTheory.Measure.Support

/-!
# Hierarchical recovery from topological population support

Exact recovery uses variation throughout the two parent-child squares, but
does not require an absolutely continuous population component. It suffices
that every neighborhood of every square point has positive probability.
Closed inverse-feasibility and decoder-range constraints then extend from
almost every sample to the entire open squares. This permits countably
supported populations, including dense mixtures of positive-weight atoms.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal Matrix

/-- Both open parent-child squares lie in the topological support of the
coefficient law. This condition only concerns the source population. -/
def HasParentChildSquareSupport (ν : Measure (FeatureVector 3)) : Prop :=
  ∀ (child : Fin 2) (a b : ℝ), a ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 →
    hierarchicalParentChildCode child a b ∈ ν.support

/-- Closed inverse-feasibility propagates from almost every observation to
the open parent-child squares whenever they lie in the population support. -/
theorem inverse_open_squares_of_zero_loss_and_topological_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z u : Ω → FeatureVector 3)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hdet : B.det ≠ 0)
    (hz : Measurable z) (hu : Measurable u)
    (hcode : ∀ᵐ ω ∂μ, (∀ j, 0 ≤ u ω j) ∧ (nonzeroSupport (u ω)).card ≤ 2)
    (hsupport : HasParentChildSquareSupport (Measure.map z μ))
    (hloss : actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) z B u = 0) :
    ∀ child : Fin 2, ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      (∀ j, 0 ≤ B⁻¹.mulVec (hierarchicalParentChildCode child a b) j) ∧
        (nonzeroSupport (B⁻¹.mulVec (hierarchicalParentChildCode child a b))).card ≤ 2 := by
  have heq := ae_eq_inverse_of_actualPopulationSquaredLoss_eq_zero μ z u B hdet hz hu hloss
  have hclosed : IsClosed {v : FeatureVector 3 |
      (∀ j, 0 ≤ B⁻¹.mulVec v j) ∧ (nonzeroSupport (B⁻¹.mulVec v)).card ≤ 2} :=
    (isClosed_nonnegative_sparse_codes 3 2).preimage
      B⁻¹.mulVecLin.continuous_of_finiteDimensional
  have hlaw : ∀ᵐ v ∂Measure.map z μ,
      (∀ j, 0 ≤ B⁻¹.mulVec v j) ∧ (nonzeroSupport (B⁻¹.mulVec v)).card ≤ 2 := by
    apply (ae_map_iff hz.aemeasurable hclosed.measurableSet).mpr
    filter_upwards [heq, hcode] with ω hω hfeas
    rwa [← hω]
  intro child a ha b hb
  exact Measure.support_subset_of_isClosed hclosed hlaw (hsupport child a b ha hb)

/-- Topological variation alone identifies all three hierarchical presence
events at any invertible exact decoder, through one common permutation. -/
theorem exists_hierarchical_presence_permutation_of_zero_loss_and_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z u : Ω → FeatureVector 3)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hdet : B.det ≠ 0)
    (hz : Measurable z) (hu : Measurable u)
    (hcode : ∀ᵐ ω ∂μ, (∀ j, 0 ≤ u ω j) ∧ (nonzeroSupport (u ω)).card ≤ 2)
    (hsource : ∀ᵐ ω ∂μ, (∀ j, 0 ≤ z ω j) ∧
      (z ω 0 = 0 → z ω 1 = 0 ∧ z ω 2 = 0))
    (hsupport : HasParentChildSquareSupport (Measure.map z μ))
    (hloss : actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) z B u = 0) :
    ∃ p : Equiv.Perm (Fin 3), ∀ᵐ ω ∂μ, ∀ j, 0 < u ω (p j) ↔ 0 < z ω j := by
  have hCdet : B⁻¹.det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det B (isUnit_iff_ne_zero.mpr hdet)).ne_zero
  have hpatch := inverse_open_squares_of_zero_loss_and_topological_support
    μ z u B hdet hz hu hcode hsupport hloss
  obtain ⟨p, _, _, _, _, hp⟩ :=
    exists_hierarchical_inverse_pattern_of_open_squares B⁻¹ hCdet hpatch
  refine ⟨p, ?_⟩
  filter_upwards [ae_eq_inverse_of_actualPopulationSquaredLoss_eq_zero μ z u B hdet hz hu hloss,
    hsource] with ω heq hω
  rw [heq]
  exact hp (z ω) hω.1 hω.2

/-- Feasible width three supplies invertibility from the positive decoding
margin; no linear inverse or decoder pattern is assumed at this endpoint. -/
theorem exists_hierarchical_presence_permutation_of_feasible_zero_loss_and_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z u : Ω → FeatureVector 3)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hz : Measurable z) (hfeas : IsFeasibleRecoveryPair B u γ 2)
    (hsource : ∀ᵐ ω ∂μ, (∀ j, 0 ≤ z ω j) ∧
      (z ω 0 = 0 → z ω 1 = 0 ∧ z ω 2 = 0))
    (hsupport : HasParentChildSquareSupport (Measure.map z μ))
    (hloss : actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) z B u = 0) :
    ∃ p : Equiv.Perm (Fin 3), ∀ᵐ ω ∂μ, ∀ j, 0 < u ω (p j) ↔ 0 < z ω j := by
  have hinj : Function.Injective B.mulVec := by
    intro v w heq
    apply sub_eq_zero.mp
    apply hfeas.2.1.kernel_eq_zero hγ (v - w)
    · have hcard := Finset.card_le_univ (nonzeroSupport (v - w))
      simpa only [Fintype.card_fin] using hcard.trans (show 3 ≤ 2 * 2 by norm_num)
    · rw [Matrix.mulVec_sub, heq, sub_self]
  have hdet : B.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det B).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero
  exact exists_hierarchical_presence_permutation_of_zero_loss_and_support μ z u B hdet hz
    hfeas.2.2.1 (Filter.Eventually.of_forall fun ω =>
      ⟨hfeas.2.2.2.2 ω, hfeas.2.2.2.1 ω⟩) hsource hsupport hloss

/-- Variation in both parent-child planes rules out zero reconstruction loss
at every width below three, even for signed unconstrained measurable codes. -/
theorem actualPopulationSquaredLoss_pos_of_parent_child_square_support
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (hm : m < 3)
    (μ : Measure Ω) (z : Ω → FeatureVector 3) (u : Ω → FeatureVector m)
    (B : Matrix (Fin 3) (Fin m) ℝ) (hz : Measurable z) (hu : Measurable u)
    (hsupport : HasParentChildSquareSupport (Measure.map z μ)) :
    0 < actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) z B u := by
  apply pos_iff_ne_zero.mpr
  intro hloss
  have hae := ae_mem_range_of_actualPopulationSquaredLoss_eq_zero μ z u B hz hu hloss
  have hrange := (LinearMap.range B.mulVecLin).closed_of_finiteDimensional
  have hlaw : ∀ᵐ v ∂Measure.map z μ, v ∈ LinearMap.range B.mulVecLin :=
    (ae_map_iff hz.aemeasurable hrange.measurableSet).mpr hae
  have htop : LinearMap.range B.mulVecLin = ⊤ :=
    submodule_eq_top_of_parent_child_open_squares _ fun child a b ha hb =>
      Measure.support_subset_of_isClosed hrange hlaw (hsupport child a b ha hb)
  have hdim := LinearMap.finrank_le_finrank_of_surjective (LinearMap.range_eq_top.mp htop)
  have hle : 3 ≤ m := by simpa only [Module.finrank_pi, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hdim
  omega

end PKG26AtomicFeatures
