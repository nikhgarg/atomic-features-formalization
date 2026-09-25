import PKG26AtomicFeatures.MesoscalePopulationModel
import PKG26AtomicFeatures.FeatureF1Supremum

/-!
# Width-one feature scores from actual child symmetry

For the explicit mesoscale measure, an event invariant under exchanging
the two children has exactly half its mass on either child. Thus a measurable
scalar encoder that respects this symmetry and is positive almost everywhere
has parent F1 supremum one and both child F1 suprema two-thirds.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators InnerProductSpace Matrix

/-- Every measurable event invariant under the actual child swap has half
its probability on each child. Balance is derived from the population's
pushforward symmetry and its almost-sure exclusive child presence. -/
theorem mesoscale_symmetric_event_child_balance
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (E : Set (FeatureVector 3)) (hE : MeasurableSet E)
    (hsym : ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η,
      mesoscaleSwapChildren z ∈ E ↔ z ∈ E) :
    ∀ k : Fin 2, (mesoscalePopulationLaw δ θ H η).real ({z | 0 < z k.succ} ∩ E) =
      (mesoscalePopulationLaw δ θ H η).real E / 2 := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ hθone
  have hpre : mesoscaleSwapChildren ⁻¹' ({z : FeatureVector 3 | 0 < z 1} ∩ E)
      =ᵐ[mesoscalePopulationLaw δ θ H η] ({z | 0 < z 2} ∩ E : Set (FeatureVector 3)) := by
    filter_upwards [hsym] with z hz
    apply propext
    change (0 < mesoscaleSwapChildren z 1 ∧ mesoscaleSwapChildren z ∈ E) ↔
      0 < z 2 ∧ z ∈ E
    rw [hz]
    rfl
  have hequal := map_measureReal_apply (μ := mesoscalePopulationLaw δ θ H η)
    (s := {z : FeatureVector 3 | 0 < z 1} ∩ E) measurable_mesoscaleSwapChildren
    ((measurableSet_lt measurable_const (measurable_pi_apply (1 : Fin 3))).inter hE)
  rw [mesoscalePopulationLaw_swap_children, measureReal_congr hpre] at hequal
  have hdiff : (E \ {z : FeatureVector 3 | 0 < z 1}) =ᵐ[mesoscalePopulationLaw δ θ H η]
      ({z | 0 < z 2} ∩ E : Set (FeatureVector 3)) := by
    filter_upwards [mesoscalePopulationLaw_ae_hierarchicalPresence δ θ H η hH hη] with z hz
    apply propext
    change (z ∈ E ∧ ¬ 0 < z 1) ↔ 0 < z 2 ∧ z ∈ E
    rcases hz.2 with h | h
    · simp [h.1, h.2]
    · simp [h.1, h.2]
  have hsum := measureReal_inter_add_diff (μ := mesoscalePopulationLaw δ θ H η) (s := E)
    (t := {z : FeatureVector 3 | 0 < z 1}) (measurableSet_lt measurable_const (measurable_pi_apply (1 : Fin 3)))
  rw [Set.inter_comm E] at hsum
  have hdiffReal : (mesoscalePopulationLaw δ θ H η).real (E \ {z : FeatureVector 3 | 0 < z 1}) =
      (mesoscalePopulationLaw δ θ H η).real ({z | 0 < z 2} ∩ E) := measureReal_congr hdiff
  intro k
  fin_cases k
  · change (mesoscalePopulationLaw δ θ H η).real ({z | 0 < z 1} ∩ E) = _
    linarith
  · change (mesoscalePopulationLaw δ θ H η).real ({z | 0 < z 2} ∩ E) = _
    linarith

/-- An actual measurable symmetric positive scalar code has exactly the
width-one F1 table. Neither threshold balance nor any F1 score is assumed. -/
theorem mesoscale_F1_table_of_symmetric_positive_scalar_code
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (u : FeatureVector 3 → FeatureVector 1) (hu : Measurable u)
    (hsym : ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, u (mesoscaleSwapChildren z) 0 = u z 0)
    (hpositive : ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, 0 < u z 0) :
    singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z 0} u = 1 ∧
      ∀ k : Fin 2, singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η)
        {z | 0 < z k.succ} u = 2 / 3 := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ hθone
  have hfull : (mesoscalePopulationLaw δ θ H η).real {z | 0 < u z 0} = 1 := by
    have hevent : {z | 0 < u z 0} =ᵐ[mesoscalePopulationLaw δ θ H η]
        (Set.univ : Set (FeatureVector 3)) := by
      filter_upwards [hpositive] with z hz
      exact propext (iff_true_intro hz)
    rw [measureReal_congr hevent, probReal_univ]
  constructor
  · apply singleCoordinateF1Sup_eq_one_of_presence_ae
      (mesoscalePopulationLaw δ θ H η) {z | 0 < z 0} u 0
    · filter_upwards [mesoscalePopulationLaw_ae_hierarchicalPresence δ θ H η hH hη,
        hpositive] with z hz hu
      exact propext ⟨fun _ => hu, fun _ => hz.1⟩
    · rw [mesoscalePopulationLaw_prevalence δ θ H η hδ hδone hθ hθone hH hη]
      norm_num
  · intro k
    have htruth : (mesoscalePopulationLaw δ θ H η).real {z | 0 < z k.succ} = 1 / 2 := by
      rw [mesoscalePopulationLaw_prevalence δ θ H η hδ hδone hθ hθone hH hη]
      simp only [Fin.succ_ne_zero, ↓reduceIte]
    apply singleCoordinateF1Sup_eq_two_thirds_of_balanced_thresholds
      (mesoscalePopulationLaw δ θ H η) {z | 0 < z k.succ} u
    · rw [htruth]
      norm_num
    · rw [hfull, htruth]
      norm_num
    · intro t _
      exact mesoscale_symmetric_event_child_balance δ θ H η hδ hδone hθ hθone hH hη
        {z | t < u z 0}
        (measurableSet_lt measurable_const ((measurable_pi_apply 0).comp hu))
        (hsym.mono fun z hz => by
          change (t < u (mesoscaleSwapChildren z) 0) ↔ t < u z 0
          rw [hz]) k

theorem mesoscale_inner_coordinates
    (w : EuclideanRepresentation 3) (z : FeatureVector 3) :
    inner ℝ w (representationToEuclidean 3 z) =
      w 0 * z 0 + w 1 * z 1 + w 2 * z 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [representationToEuclidean, real_inner_eq_re_inner, RCLike.inner_apply]
  ring

/-- Equal child coefficients make the actual linear code invariant under
swapping the two source children. -/
theorem mesoscale_inner_swap_children
    (w : EuclideanRepresentation 3) (hsym : w 1 = w 2) (z : FeatureVector 3) :
    inner ℝ w (representationToEuclidean 3 (mesoscaleSwapChildren z)) =
      inner ℝ w (representationToEuclidean 3 z) := by
  rw [mesoscale_inner_coordinates, mesoscale_inner_coordinates]
  norm_num [mesoscaleSwapChildren, Matrix.cons_val_two, hsym]
  ring

/-- A coordinatewise positive direction has positive actual linear code
almost everywhere under the hierarchical population. -/
theorem mesoscale_inner_pos_ae
    (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η)
    (w : EuclideanRepresentation 3) (hw : ∀ j, 0 < w j) :
    ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η,
      0 < inner ℝ w (representationToEuclidean 3 z) := by
  filter_upwards [mesoscalePopulationLaw_ae_hierarchicalPresence δ θ H η hH hη] with z hz
  rw [mesoscale_inner_coordinates]
  have hp := mul_pos (hw 0) hz.1
  rcases hz.2 with h | h
  · rw [h.2, mul_zero, add_zero]
    exact add_pos hp (mul_pos (hw 1) h.1)
  · rw [h.1, mul_zero, add_zero]
    exact add_pos hp (mul_pos (hw 2) h.2)

/-- In particular, every strictly positive child-symmetric linear scalar
code has the exact parent/child F1 table on the actual population. -/
theorem mesoscale_F1_table_of_positive_symmetric_linear_code
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (w : EuclideanRepresentation 3) (hw : ∀ j, 0 < w j) (hsym : w 1 = w 2) :
    singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z 0}
      (fun z (_ : Fin 1) => inner ℝ w (representationToEuclidean 3 z)) = 1 ∧
      ∀ k : Fin 2, singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η)
        {z | 0 < z k.succ}
        (fun z (_ : Fin 1) => inner ℝ w (representationToEuclidean 3 z)) = 2 / 3 := by
  apply mesoscale_F1_table_of_symmetric_positive_scalar_code δ θ H η
    hδ hδone hθ hθone hH hη
  · apply measurable_pi_lambda
    intro j
    exact (continuous_const.inner (representationToEuclidean 3).continuous).measurable
  · exact Filter.Eventually.of_forall (mesoscale_inner_swap_children w hsym)
  · exact mesoscale_inner_pos_ae δ θ H η hH hη w hw

end PKG26AtomicFeatures
