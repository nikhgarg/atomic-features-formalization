import PKG26AtomicFeatures.RepresentationOptimizationModel
import PKG26AtomicFeatures.FeatureF1

/-!
# Sparse feature representations and noisy accessibility

The decoder is defined on the entire representation space and returns
nonnegative feature activations. Its error bound is joint in all feature
coordinates. A lower stability margin `γ` corresponds to a noise amplification
factor `1 / γ`; the non-strict inequality includes zero noise.
-/

namespace PKG26AtomicFeatures

universe u

open scoped ENNReal

/-- A representation assigns a vector in the ambient space to each input. -/
abbrev RepresentationMap (X : Type u) (d : ℕ) := X → RepresentationVector d

/-- Every scalar feature activation is nonnegative. -/
def NonnegativeFeatureMap {X : Type u} {M : ℕ} (z : X → FeatureVector M) : Prop :=
  ∀ x i, 0 ≤ z x i

/-- The inputs on which a feature is active. -/
def FeatureActivationEvent {X : Type u} {M : ℕ}
    (z : X → FeatureVector M) (i : Fin M) : Set X :=
  {x | 0 < z x i}

/-- Every bounded nonnegative sparse activation occurs, and no other
activation occurs. -/
def RealizesSparseCube {X : Type u} {M : ℕ}
    (z : X → FeatureVector M) (K : ℕ) : Prop :=
  Set.range z = SparseUnitCube M K

/-- One dictionary uses weakly fewer columns and weakly less sparsity,
with a strict improvement in at least one of those two resources. -/
def StrictDictionaryEfficiency (M K M' K' : ℕ) : Prop :=
  M ≤ M' ∧ K ≤ K' ∧ (M < M' ∨ K < K')

/-- The recovery confidence used for dictionary matching. Its deficit is
bounded by both the directional tolerance `η² / 2` and the stability
tolerance `γ² / 8`. -/
noncomputable def matchingRecoveryConfidence (γ η : ℝ) : ℝ :=
  1 - min (η ^ 2 / 2) (γ ^ 2 / 8)

/-- A matching tolerance between zero and one gives positive recovery
confidence. -/
theorem matchingRecoveryConfidence_pos {γ η : ℝ}
    (hηpos : 0 < η) (hηlt : η < 1) :
    0 < matchingRecoveryConfidence γ η := by
  have hηsq : η ^ 2 < 1 := by
    nlinarith [mul_pos hηpos (sub_pos.mpr hηlt)]
  have hmin := min_le_left (η ^ 2 / 2) (γ ^ 2 / 8)
  unfold matchingRecoveryConfidence
  linarith

/-- Positive stability and matching tolerances keep the recovery confidence
strictly below one. -/
theorem matchingRecoveryConfidence_lt_one {γ η : ℝ}
    (hγpos : 0 < γ) (hηpos : 0 < η) :
    matchingRecoveryConfidence γ η < 1 := by
  have hmin : 0 < min (η ^ 2 / 2) (γ ^ 2 / 8) :=
    lt_min (by positivity) (by positivity)
  unfold matchingRecoveryConfidence
  linarith

/-- A molecule with size budget `r` is a linear combination of at most `r`
atomic columns. The budget is a parameter; this definition does not impose a
particular meaning of a small budget or assert a splitting law. -/
def Molecule {d M : ℕ} (A : Matrix (Fin d) (Fin M) ℝ)
    (r : ℕ) (v : RepresentationVector d) : Prop :=
  ∃ c : FeatureVector M, (nonzeroSupport c).card ≤ r ∧ v = A.mulVec c

/-- A dictionary linearly reconstructs the representation from its features. -/
def LinearFeatureRepresentation {X : Type u} {d M : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (f : RepresentationMap X d) : Prop :=
  ∀ x, f x = A.mulVec (z x)

/-- The current atomic postulate: a sparse nonnegative factorization with
full signed sparse stability. Unit columns, population coefficient bounds,
and richness are separate assumptions of the results that need them. -/
def StableAtomicRepresentation {X : Type u} {d M : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (f : RepresentationMap X d) (γ : ℝ) (K : ℕ) : Prop :=
  SparseLowerStable A γ (2 * K) ∧ KSparse (K := K) z ∧
    NonnegativeFeatureMap z ∧ LinearFeatureRepresentation A z f

/-- The linear representation postulate as an existence claim: the observed
representation admits a stable, sparse, nonnegative atomic factorization. -/
def StableAtomicRepresentationHypothesis {X : Type u} {d : ℕ}
    (f : RepresentationMap X d) (M K : ℕ) (γ : ℝ) : Prop :=
  ∃ (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M),
    StableAtomicRepresentation A z f γ K

/-- A learned dictionary recovers atomic direction `i` at level `η` when one
of its columns has inner product strictly above `η` with that direction. -/
def DirectionRecovered {d M m : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (i : Fin M) (η : ℝ) : Prop :=
  ∃ j : Fin m,
    η < inner ℝ (representationToEuclidean d (B.col j))
      (representationToEuclidean d (A.col i))

/-- A learned code recovers atomic activation `i` at level `η` when one of
its coordinates has a real threshold whose population F1 is strictly above
`η`. The coordinate and threshold witnesses are independent of direction
recovery, and the threshold is unrestricted, as in the source definition. -/
def ActivationRecovered {X : Type u} [MeasurableSpace X] {M m : ℕ}
    (μ : MeasureTheory.Measure X) (z : X → FeatureVector M)
    (code : X → FeatureVector m) (i : Fin M) (η : ℝ) : Prop :=
  ∃ (j : Fin m) (τ : ℝ),
    η < populationF1 μ (FeatureActivationEvent z i) {x | τ < code x j}

/-- The linear representation hypothesis asserts existence of a dictionary
and nonnegative scalar features realizing the given representation. -/
def LinearRepresentationHypothesis {X : Type u} {d : ℕ}
    (f : RepresentationMap X d) (M : ℕ) : Prop :=
  ∃ (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M),
    NonnegativeFeatureMap z ∧ LinearFeatureRepresentation A z f

/-- Expected squared reconstruction loss conditional on an atomic support.
Results using this quantity require the conditioning support to have positive
probability. -/
noncomputable def conditionalSupportSquaredLoss
    {X : Type u} [MeasurableSpace X] {d M m : ℕ}
    (μ : MeasureTheory.Measure X) (A : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (B : Matrix (Fin d) (Fin m) ℝ)
    (code : X → FeatureVector m) (S : Finset (Fin M)) : ℝ≥0∞ :=
  actualPopulationSquaredLoss (sourceSupportConditionalLaw μ z S) A z B code

/-- A child can be active only when its parent is active. Distinctness of
the two feature indices is imposed where a theorem requires it. -/
def PerfectFeatureHierarchy {X : Type u} {M : ℕ}
    (z : X → FeatureVector M) (child parent : Fin M) : Prop :=
  ∀ x, 0 < z x child → 0 < z x parent

/-- The projector definition of subspace gap, including zero-dimensional
spaces. The source results compare equal-dimensional spaces. -/
noncomputable def subspaceGap {d : ℕ}
    (U V : Submodule ℝ (EuclideanRepresentation d)) : ℝ :=
  ‖U.starProjection - V.starProjection‖

/-- A single nonnegative feature can be decoded with absolute error at most
`L` times the Euclidean representation noise. -/
def ScalarNoisyFeatureAccessible {X : Type u} {d : ℕ}
    (z : X → ℝ) (f : RepresentationMap X d) (L : ℝ) : Prop :=
  ∃ g : RepresentationVector d → ℝ,
    (∀ y, 0 ≤ g y) ∧
    ∀ (x : X) (noise : RepresentationVector d),
      |g (f x + noise) - z x| ≤ L * ‖representationToEuclidean d noise‖

/-- One globally defined nonnegative decoder has joint Euclidean error at
most `L` times the noise norm at every represented input. This condition does
not require the decoder to be globally Lipschitz away from the data range. -/
def NoisyFeatureAccessible {X : Type u} {d M : ℕ}
    (z : X → FeatureVector M) (f : RepresentationMap X d) (L : ℝ) : Prop :=
  ∃ g : RepresentationVector d → FeatureVector M,
    NonnegativeFeatureMap g ∧
    ∀ (x : X) (noise : RepresentationVector d),
      ‖representationToEuclidean M (g (f x + noise) - z x)‖ ≤
        L * ‖representationToEuclidean d noise‖

/-- Joint Euclidean noise control implies the same bound for each feature. -/
theorem NoisyFeatureAccessible.scalar
    {X : Type u} {d M : ℕ} {L : ℝ}
    {z : X → FeatureVector M} {f : RepresentationMap X d}
    (h : NoisyFeatureAccessible z f L) (i : Fin M) :
    ScalarNoisyFeatureAccessible (fun x => z x i) f L := by
  obtain ⟨g, hnonneg, hbound⟩ := h
  refine ⟨fun y => g y i, fun y => hnonneg y i, ?_⟩
  intro x noise
  have hcoord := PiLp.norm_apply_le
    (representationToEuclidean M (g (f x + noise) - z x)) i
  have hcoord' : |g (f x + noise) i - z x i| ≤
      ‖representationToEuclidean M (g (f x + noise) - z x)‖ := by
    simpa [representationToEuclidean, Real.norm_eq_abs] using hcoord
  exact hcoord'.trans (hbound x noise)

/-- Zero noise forces exact decoding. -/
theorem exact_decoding_of_noise_bound
    {X : Type u} {d M : ℕ} {L : ℝ}
    {z : X → FeatureVector M} {f : RepresentationMap X d}
    {g : RepresentationVector d → FeatureVector M}
    (h : ∀ (x : X) (noise : RepresentationVector d),
      ‖representationToEuclidean M (g (f x + noise) - z x)‖ ≤
        L * ‖representationToEuclidean d noise‖) (x : X) :
    g (f x) = z x := by
  have hz : ‖representationToEuclidean M (g (f x) - z x)‖ ≤ 0 := by
    simpa using h x 0
  have heq : representationToEuclidean M (g (f x) - z x) = 0 :=
    norm_le_zero_iff.mp hz
  apply sub_eq_zero.mp
  exact (representationToEuclidean M).injective (by simpa using heq)

/-- Noise robustness controls distances between codes at any two inputs. -/
theorem NoisyFeatureAccessible.featureAccessible
    {X : Type u} {d M : ℕ} {γ : ℝ}
    {z : X → FeatureVector M} {f : RepresentationMap X d}
    (h : NoisyFeatureAccessible z f γ⁻¹) : FeatureAccessible z f γ := by
  obtain ⟨g, _hnonneg, hbound⟩ := h
  have hexact := exact_decoding_of_noise_bound hbound
  intro x y
  have hxy := hbound y (f x - f y)
  simpa only [add_sub_cancel, hexact x, div_eq_mul_inv, mul_comm] using hxy

/-- The atomic postulate with its explicit noisy-accessibility condition and
the source sparse-stability hypothesis. The cube equality supplies both the
bounded code domain and realization of every sparse cube activation. -/
def RobustAtomicPostulate {X : Type u} {d M : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (f : RepresentationMap X d) (γ : ℝ) (K : ℕ) : Prop :=
  HasUnitEuclideanColumns A ∧ SparseLowerStable A γ (2 * K) ∧
    RealizesSparseCube z K ∧ LinearFeatureRepresentation A z f ∧
    NoisyFeatureAccessible z f γ⁻¹

/-- The stability and representation hypotheses needed by the recovery and
rigidity arguments are contained in the robust atomic model. -/
theorem RobustAtomicPostulate.toAtomicPostulate
    {X : Type u} {d M K : ℕ} {γ : ℝ}
    {A : Matrix (Fin d) (Fin M) ℝ} {z : X → FeatureVector M}
    {f : RepresentationMap X d} (h : RobustAtomicPostulate A z f γ K) :
    AtomicPostulate A z f γ K :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end PKG26AtomicFeatures
