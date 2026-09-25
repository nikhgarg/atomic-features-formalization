import PKG26AtomicFeatures.HierarchicalZeroLossPresence
import PKG26AtomicFeatures.MesoscalePopulationModel
import PKG26AtomicFeatures.FeatureF1Supremum

/-!
# Exact feature recovery at zero loss for the explicit mesoscale law

Each independent uniform parent-child square is an actual component of the
unscaled symmetric population, with mass `θ / 2`. Consequently every
feasible width-three zero-loss decoder has one common feature-presence
permutation. Each of the three best single-coordinate F1 suprema is one.
The sampling and prevalence premises are derived from the explicit mixture.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal Matrix

/-- The explicit mixture and inverse-pattern developments use the same
parent-child embedding. -/
theorem mesoscalePlaneEmbedding_eq_hierarchicalParentChildEmbedding (child : Fin 2) :
    mesoscalePlaneEmbedding child = hierarchicalParentChildEmbedding child := by
  funext q j
  fin_cases child <;> fin_cases j <;>
    norm_num [mesoscalePlaneEmbedding, hierarchicalParentChildEmbedding,
      hierarchicalParentChildCode, Pi.single_apply, Matrix.cons_val_two, Fin.succ]

/-- The independent uniform cube is a genuine submeasure of the pair law. -/
theorem mesoscalePairLaw_cube_le (δ θ H η : ℝ) :
    ENNReal.ofReal θ • uniformCubeCoefficientLaw 2 ≤ mesoscalePairLaw δ θ H η := by
  unfold mesoscalePairLaw
  exact Measure.le_add_left le_rfl

/-- Each unscaled parent-child cube appears with its actual mixture weight
`θ / 2`. No domination hypothesis is assumed here. -/
theorem mesoscalePopulationLaw_cube_le (δ θ H η : ℝ) (child : Fin 2) :
    ENNReal.ofReal (θ / 2) • hierarchicalParentChildCubeLaw child ≤
      mesoscalePopulationLaw δ θ H η := by
  have hmap := Measure.map_mono (mesoscalePairLaw_cube_le δ θ H η)
    (measurable_mesoscalePlaneEmbedding child)
  rw [Measure.map_smul, mesoscalePlaneEmbedding_eq_hierarchicalParentChildEmbedding] at hmap
  change ENNReal.ofReal θ • hierarchicalParentChildCubeLaw child ≤
    Measure.map (hierarchicalParentChildEmbedding child) (mesoscalePairLaw δ θ H η) at hmap
  have hweight : ENNReal.ofReal (θ / 2) = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal θ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num [div_eq_mul_inv, mul_comm]
  intro s
  have hhalf := mul_le_mul_right (hmap s) (1 / 2 : ℝ≥0∞)
  simp only [Measure.smul_apply, smul_eq_mul] at hhalf ⊢
  rw [hweight, mul_assoc]
  apply hhalf.trans
  rw [mesoscalePopulationLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul]
  rw [← mesoscalePlaneEmbedding_eq_hierarchicalParentChildEmbedding]
  fin_cases child
  · exact le_add_right le_rfl
  · exact le_add_left le_rfl

/-- The primitive rare-point positivity and the uniform component give
nonnegative hierarchical source coefficients almost everywhere. -/
theorem mesoscalePopulationLaw_ae_nonnegative_hierarchy
    (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η,
      (∀ j, 0 ≤ z j) ∧ (z 0 = 0 → z 1 = 0 ∧ z 2 = 0) := by
  filter_upwards [mesoscalePopulationLaw_ae_hierarchicalPresence δ θ H η hH hη] with z hz
  refine ⟨?_, fun hz0 => (hz.1.ne' hz0).elim⟩
  intro j
  fin_cases j
  · exact hz.1.le
  · rcases hz.2 with h | h
    · exact h.1.le
    · exact h.1.symm.le
  · rcases hz.2 with h | h
    · exact h.2.symm.le
    · exact h.2.le

/-- For the actual unscaled mesoscale population, every feasible width-three
zero-loss decoder has one permutation preserving all three feature-presence
events almost everywhere. -/
theorem mesoscale_zero_loss_presence_permutation
    (δ θ H η γ : ℝ) (hθ : 0 < θ) (hH : 0 < H) (hη : 0 < η) (hγ : 0 < γ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3)
    (hfeas : IsFeasibleRecoveryPair B u γ 2)
    (hloss : actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0) :
    ∃ p : Equiv.Perm (Fin 3), ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η,
      ∀ j, 0 < u z (p j) ↔ 0 < z j := by
  apply exists_hierarchical_presence_permutation_of_feasible_zero_loss
    (mesoscalePopulationLaw δ θ H η) id u B γ hγ measurable_id hfeas
    (mesoscalePopulationLaw_ae_nonnegative_hierarchy δ θ H η hH hη)
  · intro child
    refine ⟨θ / 2, by positivity, ?_⟩
    simpa only [Measure.map_id] using mesoscalePopulationLaw_cube_le δ θ H η child
  · exact hloss

/-- All three single-coordinate positive-threshold F1 suprema equal one at
every feasible width-three zero-loss decoder. The same decoder also has one
common almost-everywhere presence permutation. -/
theorem mesoscale_zero_loss_presence_and_f1
    (δ θ H η γ : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η) (hγ : 0 < γ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3)
    (hfeas : IsFeasibleRecoveryPair B u γ 2)
    (hloss : actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0) :
    ∃ p : Equiv.Perm (Fin 3),
      (∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, ∀ j, 0 < u z (p j) ↔ 0 < z j) ∧
      ∀ j : Fin 3, singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z j} u = 1 := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ.le hθone
  obtain ⟨p, hp⟩ := mesoscale_zero_loss_presence_permutation δ θ H η γ hθ hH hη hγ B u hfeas hloss
  refine ⟨p, hp, ?_⟩
  intro j
  apply singleCoordinateF1Sup_eq_one_of_presence_ae
    (mesoscalePopulationLaw δ θ H η) {z | 0 < z j} u (p j)
  · filter_upwards [hp] with z hz
    exact propext (hz j).symm
  · rw [mesoscalePopulationLaw_prevalence δ θ H η hδ hδone hθ.le hθone hH hη]
    split_ifs <;> norm_num

end PKG26AtomicFeatures
