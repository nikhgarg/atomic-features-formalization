import PKG26AtomicFeatures.NonnegativeLeastSquares
import PKG26AtomicFeatures.RegularPopulationModel
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Population uniqueness of nonnegative least-squares encoders

For a globally stable dictionary, the canonical nonnegative least-squares
encoder is measurable and its risk is bounded by the input's second moment.
Any measurable nonnegative encoder whose actual expected squared residual is
no larger agrees with it almost everywhere. Neither finite competing risk
nor pointwise optimality of the competing encoder is assumed.

The measure can be arbitrary: finiteness of the input's second moment is
enough, so the statements apply in particular to finite and probability laws.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal

/-- Actual expected squared Euclidean residual for an arbitrary Euclidean
input map and an actual coefficient map. Infinite risk is retained. -/
noncomputable def euclideanPopulationSquaredLoss
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (u : Ω → FeatureVector m) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal
    (‖f ω - representationToEuclidean d (B.mulVec (u ω))‖ ^ 2) ∂μ

/-- The canonical encoder depends on a sample only through its observed
Euclidean representation. -/
noncomputable def nonnegativeLeastSquaresEncoder
    {Ω : Type*} {d m : ℕ} (f : Ω → EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) : Ω → FeatureVector m :=
  nonnegativeLeastSquaresCode B γ hγ hlower ∘ f

theorem measurable_nonnegativeLeastSquaresEncoder
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    {f : Ω → EuclideanRepresentation d} (hf : Measurable f)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) :
    Measurable (nonnegativeLeastSquaresEncoder f B γ hγ hlower) :=
  (measurable_nonnegativeLeastSquaresCode B γ hγ hlower).comp hf

theorem nonnegativeLeastSquaresEncoder_nonneg
    {Ω : Type*} {d m : ℕ} (f : Ω → EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) (ω : Ω) (j : Fin m) :
    0 ≤ nonnegativeLeastSquaresEncoder f B γ hγ hlower ω j :=
  (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower (f ω)).1 j

/-- The small-width sparsity constraint is automatic for the actual
canonical encoder, including empty learned widths. -/
theorem nonnegativeLeastSquaresEncoder_sparse
    {Ω : Type*} {d m K : ℕ} (f : Ω → EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) (hmK : m ≤ K) :
    KSparse (K := K) (nonnegativeLeastSquaresEncoder f B γ hγ hlower) := by
  intro ω
  exact (show (nonzeroSupport
    (nonnegativeLeastSquaresEncoder f B γ hγ hlower ω)).card ≤ m by
      simpa only [Fintype.card_fin] using Finset.card_le_univ
        (nonzeroSupport (nonnegativeLeastSquaresEncoder f B γ hγ hlower ω))).trans hmK

theorem measurable_euclideanSquaredResidual
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    {f : Ω → EuclideanRepresentation d} (hf : Measurable f)
    (B : Matrix (Fin d) (Fin m) ℝ) {u : Ω → FeatureVector m}
    (hu : Measurable u) :
    Measurable (fun ω => ENNReal.ofReal
      (‖f ω - representationToEuclidean d (B.mulVec (u ω))‖ ^ 2)) := by
  exact ((hf.sub ((representationToEuclidean d).continuous.measurable.comp
    (B.mulVecLin.continuous_of_finiteDimensional.measurable.comp hu))).norm.pow_const 2).ennreal_ofReal

/-- Pointwise comparison with the feasible zero code bounds canonical risk
by the input's second moment. -/
theorem nonnegativeLeastSquaresEncoder_loss_le_secondMoment
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) :
    euclideanPopulationSquaredLoss μ f B (nonnegativeLeastSquaresEncoder f B γ hγ hlower) ≤
      ∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ 2) ∂μ := by
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  simpa only [Matrix.mulVec_zero, map_zero, sub_zero] using
    (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower (f ω)).2 0 (fun _ => le_rfl)

theorem nonnegativeLeastSquaresEncoder_loss_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (hsecond : (∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ 2) ∂μ) < ⊤) :
    euclideanPopulationSquaredLoss μ f B
      (nonnegativeLeastSquaresEncoder f B γ hγ hlower) < ⊤ :=
  (nonnegativeLeastSquaresEncoder_loss_le_secondMoment μ f B γ hγ hlower).trans_lt hsecond

/-- The risk comparison itself implies finite competing risk; it need not
be supplied as an independent assumption. -/
theorem euclideanPopulationSquaredLoss_lt_top_of_le_nonnegativeLeastSquares
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ v : FeatureVector m, γ * ‖representationToEuclidean m v‖ ≤
      ‖representationToEuclidean d (B.mulVec v)‖)
    (hsecond : (∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ 2) ∂μ) < ⊤)
    (u : Ω → FeatureVector m)
    (hrisk : euclideanPopulationSquaredLoss μ f B u ≤
      euclideanPopulationSquaredLoss μ f B (nonnegativeLeastSquaresEncoder f B γ hγ hlower)) :
    euclideanPopulationSquaredLoss μ f B u < ⊤ :=
  hrisk.trans_lt (nonnegativeLeastSquaresEncoder_loss_lt_top μ f B γ hγ hlower hsecond)

/-- Every measurable nonnegative encoder with risk at most the canonical
risk agrees with the canonical encoder almost everywhere. The conclusion
follows from equality of actual squared residuals and pointwise uniqueness. -/
theorem ae_eq_nonnegativeLeastSquaresEncoder_of_loss_le
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) {f : Ω → EuclideanRepresentation d} (hf : Measurable f)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ v : FeatureVector m, γ * ‖representationToEuclidean m v‖ ≤
      ‖representationToEuclidean d (B.mulVec v)‖)
    (hsecond : (∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ 2) ∂μ) < ⊤)
    {u : Ω → FeatureVector m} (hu : Measurable u)
    (hnonneg : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ u ω j)
    (hrisk : euclideanPopulationSquaredLoss μ f B u ≤
      euclideanPopulationSquaredLoss μ f B (nonnegativeLeastSquaresEncoder f B γ hγ hlower)) :
    u =ᵐ[μ] nonnegativeLeastSquaresEncoder f B γ hγ hlower := by
  have hpointwise :
      (fun ω => ENNReal.ofReal (‖f ω - representationToEuclidean d
        (B.mulVec (nonnegativeLeastSquaresEncoder f B γ hγ hlower ω))‖ ^ 2)) ≤ᵐ[μ]
      (fun ω => ENNReal.ofReal (‖f ω - representationToEuclidean d (B.mulVec (u ω))‖ ^ 2)) := by
    filter_upwards [hnonneg] with ω hω
    exact ENNReal.ofReal_le_ofReal
      ((nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower (f ω)).2 (u ω) hω)
  have hequal := ae_eq_of_ae_le_of_lintegral_le hpointwise
    (nonnegativeLeastSquaresEncoder_loss_lt_top μ f B γ hγ hlower hsecond).ne
    (measurable_euclideanSquaredResidual hf B hu).aemeasurable hrisk
  filter_upwards [hequal, hnonneg] with ω hω hn
  have hreal := congrArg ENNReal.toReal hω
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at hreal
  have hoptimal : IsNonnegativeLeastSquaresCode B (f ω) (u ω) := by
    refine ⟨hn, fun v hv => ?_⟩
    rw [← hreal]
    exact (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower (f ω)).2 v hv
  exact hoptimal.eq_nonnegativeLeastSquaresCode hγ hlower

/-- Above the dictionary width, sparse lower stability is the global lower
singular bound required by the nonnegative least-squares construction. -/
theorem SparseLowerStable.global_bound_of_width_le
    {d m s : ℕ} {B : Matrix (Fin d) (Fin m) ℝ} {γ : ℝ}
    (hstable : SparseLowerStable B γ s) (hms : m ≤ s) :
    ∀ v : FeatureVector m, γ * ‖representationToEuclidean m v‖ ≤
      ‖representationToEuclidean d (B.mulVec v)‖ := by
  intro v
  apply hstable v
  exact (show (nonzeroSupport v).card ≤ m by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (nonzeroSupport v)).trans hms

/-- At width at most K, canonical nonnegative least squares is an actual
feasible competitor in the paper's dictionary-and-code class. -/
theorem isFeasibleRecoveryPair_nonnegativeLeastSquaresEncoder
    {Ω : Type*} [MeasurableSpace Ω] {d m K : ℕ}
    {f : Ω → EuclideanRepresentation d} (hf : Measurable f)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ v : FeatureVector m, γ * ‖representationToEuclidean m v‖ ≤
      ‖representationToEuclidean d (B.mulVec v)‖)
    (hunit : HasUnitEuclideanColumns B) (hstable : SparseLowerStable B γ (2 * K))
    (hmK : m ≤ K) :
    IsFeasibleRecoveryPair B (nonnegativeLeastSquaresEncoder f B γ hγ hlower) γ K :=
  ⟨hunit, hstable, measurable_nonnegativeLeastSquaresEncoder hf B γ hγ hlower,
    nonnegativeLeastSquaresEncoder_sparse f B γ hγ hlower hmK,
    nonnegativeLeastSquaresEncoder_nonneg f B γ hγ hlower⟩

/-- Every exact joint optimizer in the existing recovery-pair class uses
the canonical NNLS encoder almost everywhere when the learned width is at
most K. Its sparse stability already implies the required global bound. -/
theorem IsApproximatelyOptimalRecoveryPair.ae_eq_nonnegativeLeastSquaresEncoder
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    {μ : Measure Ω} {A : Matrix (Fin d) (Fin M) ℝ} {z : Ω → FeatureVector M}
    {B : Matrix (Fin d) (Fin m) ℝ} {u : Ω → FeatureVector m} {γ : ℝ}
    (hoptimal : IsApproximatelyOptimalRecoveryPair μ A z B u γ 1 K)
    (hγ : 0 < γ) (hmK : m ≤ K)
    (hf : Measurable (fun ω => representationToEuclidean d (A.mulVec (z ω))))
    (hsecond : (∫⁻ ω, ENNReal.ofReal
      (‖representationToEuclidean d (A.mulVec (z ω))‖ ^ 2) ∂μ) < ⊤) :
    u =ᵐ[μ] nonnegativeLeastSquaresEncoder
      (fun ω => representationToEuclidean d (A.mulVec (z ω))) B γ hγ
      (hoptimal.1.2.1.global_bound_of_width_le (by omega : m ≤ 2 * K)) := by
  let f := fun ω => representationToEuclidean d (A.mulVec (z ω))
  let hlower := hoptimal.1.2.1.global_bound_of_width_le (by omega : m ≤ 2 * K)
  have hcanonical := isFeasibleRecoveryPair_nonnegativeLeastSquaresEncoder
    hf B γ hγ hlower hoptimal.1.1 hoptimal.1.2.1 hmK
  apply ae_eq_nonnegativeLeastSquaresEncoder_of_loss_le μ hf B γ hγ hlower hsecond
    hoptimal.1.2.2.1 (Filter.Eventually.of_forall hoptimal.1.2.2.2.2)
  simpa only [euclideanPopulationSquaredLoss, actualPopulationSquaredLoss,
    ENNReal.ofReal_one, one_mul] using
    hoptimal.2 B (nonnegativeLeastSquaresEncoder f B γ hγ hlower) hcanonical

end PKG26AtomicFeatures
