import PKG26AtomicFeatures.Featurization
import PKG26AtomicFeatures.LocalGlobalHall
import PKG26AtomicFeatures.GenericFeaturization
import PKG26AtomicFeatures.AtomicRigidity
import PKG26AtomicFeatures.RankedFeatureTail
import PKG26AtomicFeatures.TestableMatchingMetrics
import PKG26AtomicFeatures.RegularHierarchicalPopulation
import PKG26AtomicFeatures.QuotientDirectionGeometry
import PKG26AtomicFeatures.FeatureF1Supremum
import PKG26AtomicFeatures.RepresentationOptimizationModel
import PKG26AtomicFeatures.NoisySourceModel
import PKG26AtomicFeatures.StableSupportIntersections

/-!
# A Testable Theory of Atomic Features: source statements

The current main results are open-rich rigidity up to permutation and scaling,
prevalence-tail recovery, signed matching across widths and populations, and
hierarchical activation recovery. The model exposes sparse stability and nonnegative
factorization; normalization is local to the recovery results. Population
coefficient bounds follow from the stated conditional laws and need hold
only almost surely. Supplementary mesoscale results are grouped separately
from the manuscript's selected statements.

Genericity uses intrinsic surface measure on the product of unit spheres,
with ambient dimension written as `n + 1`.
-/

namespace PKG26AtomicFeatures

universe u

/-- Proposition `prop:spark-uniqueness`: every input has exactly one
coefficient vector at the stated sparsity. -/
def SparseRecoverySpec : Prop :=
  ∀ (X : Type u) (d M K : ℕ)
    (matrix : Matrix (Fin d) (Fin M) ℝ) (code : X → FeatureVector M)
    (f : RepresentationMap X d),
    IsFeaturization K matrix code f →
    ∀ (x : X) (v : FeatureVector M),
      f x = matrix.mulVec v → (nonzeroSupport v).card ≤ K → v = code x

/-- Atomicness, `thm:2k`: a Pareto-efficient exact competitor is equivalent
up to one common permutation and nonzero column/code scalings, or requires
at least twice the source sparsity. The source is open-rich; neither
normalization nor full-cube surjectivity is imposed. The stability margins
of the two representations may differ. -/
def RigiditySpec : Prop :=
  ∀ (X : Type u) (d M K : ℕ) (γ : ℝ)
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (f : RepresentationMap X d),
    1 ≤ K → K < M → 0 < γ → StableAtomicRepresentation A z f γ K →
    OpenKRich (K := K) z →
    ∀ (M' K' : ℕ) (γ' : ℝ) (B : Matrix (Fin d) (Fin M') ℝ)
      (u : X → FeatureVector M'),
      0 < γ' → StableAtomicRepresentation B u f γ' K' →
      ¬ StrictDictionaryEfficiency M K M' K' →
      AtomicPairsEquivalent A z B u ∨ 2 * K ≤ K'

/-- Theorem `thm:recovery-principle`, with the appendix's positive-prevalence scope.
The actual loss is compared with the infimum over the actual feasible class.
Direction and activation use the paper's separate existential witnesses.
The ranking is explicit, and regularity
specifies exact-K supports and positive-mass conditioning. Positive prevalence
excludes absent atoms at zero tail. -/
def PositivePrevalenceRecoverySpec : Prop :=
  ∀ (K : ℕ) (γ ρ cLower cUpper C₀ η : ℝ),
    1 ≤ K → 0 < γ → γ ≤ 1 → 0 < ρ →
    0 < cLower → cLower ≤ cUpper → 1 ≤ C₀ → η < 1 →
    ∃ C : ℝ, 1 < C ∧
      ∀ (X : Type u) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
        [MeasureTheory.IsProbabilityMeasure μ] (d M m : ℕ)
        (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
        (f : RepresentationMap X d),
        K < M → HasUnitEuclideanColumns A → StableAtomicRepresentation A z f γ K →
        RegularSparsePopulation (K := K) μ z ρ cLower cUpper →
        ∀ σ : Equiv.Perm (Fin M), Antitone (fun j => featurePrevalence μ z (σ j)) →
        m ≤ M →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : X → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          actualPopulationSquaredLoss μ A z B code ≤
            ENNReal.ofReal C₀ * optimalRecoveryLoss μ A z γ K m →
          ∀ i : Fin M, 0 < featurePrevalence μ z i →
            C * rankedFeatureTail (featurePrevalence μ z) σ m ≤ featurePrevalence μ z i →
            DirectionRecovered A B i η ∧ ActivationRecovered μ z code i η

/-- Recovery and predictions P1/P2 with a common constant and threshold.
The positive-prevalence convention makes the ranked prefix empty-safe.
Recovery uses confidence `1 - min (η²/2) (γ²/8)` for matching at `1 - 2η²`.
P2 uses each population's own rank and ordering.
All objectives and matching scores are those of the actual dictionaries. -/
def PositivePrevalenceRecoveryPredictionsSpec : Prop :=
  ∀ (K : ℕ) (γ ρ cLower cUpper C₀ η : ℝ),
    1 ≤ K → 0 < γ → γ ≤ 1 → 0 < ρ →
    0 < cLower → cLower ≤ cUpper → 1 ≤ C₀ → 0 < η → η < 1 →
    ∃ C t : ℝ, 1 < C ∧ 0 < t ∧
      ∀ (X : Type u) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
        [MeasureTheory.IsProbabilityMeasure μ] (d M m : ℕ)
        (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
        (f : RepresentationMap X d),
        K < M → HasUnitEuclideanColumns A → StableAtomicRepresentation A z f γ K →
        RegularSparsePopulation (K := K) μ z ρ cLower cUpper →
        ∀ σ : Equiv.Perm (Fin M), Antitone (fun j => featurePrevalence μ z (σ j)) →
        1 ≤ m → m ≤ M →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : X → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          actualPopulationSquaredLoss μ A z B code ≤
            ENNReal.ofReal C₀ * optimalRecoveryLoss μ A z γ K m →
          (∃ e : tailRecoverableFeatures (featurePrevalence μ z) σ C m ↪ Fin m,
            ∀ i,
              matchingRecoveryConfidence γ η < inner ℝ (representationToEuclidean d (A.col i.1))
                (representationToEuclidean d (B.col (e i))) ∧
              matchingRecoveryConfidence γ η <
                populationF1 μ (FeatureActivationEvent z i.1) {x | t < code x (e i)}) ∧
          (∀ (s : ℕ) (width : Fin s → ℕ),
            (∀ l, m ≤ width l) → (∀ l, width l ≤ M) →
            ∀ (B' : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ)
              (code' : ∀ l, X → FeatureVector (width l)),
              (∀ l, IsFeasibleRecoveryPair (B' l) (code' l) γ K) →
              (∀ l, actualPopulationSquaredLoss μ A z (B' l) (code' l) ≤
                ENNReal.ofReal C₀ * optimalRecoveryLoss μ A z γ K (width l)) →
              tailRecoverableRank (featurePrevalence μ z) σ C m ≤
                testableMatchingMetric width B B' (1 - 2 * η ^ 2)) ∧
          (∀ (μ' : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ'],
            RegularSparsePopulation (K := K) μ' z ρ cLower cUpper →
            ∀ (σ' : Equiv.Perm (Fin M)), Antitone (fun j => featurePrevalence μ' z (σ' j)) →
            ∀ (B' : Matrix (Fin d) (Fin m) ℝ) (code' : X → FeatureVector m),
              IsFeasibleRecoveryPair B' code' γ K →
              actualPopulationSquaredLoss μ' A z B' code' ≤
                ENNReal.ofReal C₀ * optimalRecoveryLoss μ' A z γ K m →
              ((Finset.univ.filter fun j : Fin M =>
                  j.val < tailRecoverableRank (featurePrevalence μ z) σ C m).image σ ∩
                (Finset.univ.filter fun j : Fin M =>
                  j.val < tailRecoverableRank (featurePrevalence μ' z) σ' C m).image σ').card ≤
                testableMatchingMetric (fun _ : Unit => m) B (fun _ => B')
                  (1 - 2 * η ^ 2))

/-- P1, `cor:stability-size`: at any prescribed signed cosine threshold
`t < 1`, the same constant gives a ranked-prefix lower bound for the
maximum simultaneous one-to-one matching into every larger learned width. -/
def PositivePrevalenceSizeStabilitySpec : Prop :=
  ∀ (K : ℕ) (γ ρ cLower cUpper C₀ t : ℝ),
    1 ≤ K → 0 < γ → γ ≤ 1 → 0 < ρ →
    0 < cLower → cLower ≤ cUpper → 1 ≤ C₀ → t < 1 →
    ∃ C : ℝ, 1 < C ∧
      ∀ (X : Type u) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
        [MeasureTheory.IsProbabilityMeasure μ] (d M m : ℕ)
        (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
        (f : RepresentationMap X d),
        K < M → HasUnitEuclideanColumns A → StableAtomicRepresentation A z f γ K →
        RegularSparsePopulation (K := K) μ z ρ cLower cUpper →
        ∀ σ : Equiv.Perm (Fin M), Antitone (fun j => featurePrevalence μ z (σ j)) →
        1 ≤ m → m ≤ M →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : X → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          actualPopulationSquaredLoss μ A z B code ≤
            ENNReal.ofReal C₀ * optimalRecoveryLoss μ A z γ K m →
          ∀ (s : ℕ) (width : Fin s → ℕ),
            (∀ l, m ≤ width l) → (∀ l, width l ≤ M) →
            ∀ (B' : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ)
              (code' : ∀ l, X → FeatureVector (width l)),
              (∀ l, IsFeasibleRecoveryPair (B' l) (code' l) γ K) →
              (∀ l, actualPopulationSquaredLoss μ A z (B' l) (code' l) ≤
                ENNReal.ofReal C₀ * optimalRecoveryLoss μ A z γ K (width l)) →
              tailRecoverableRank (featurePrevalence μ z) σ C m ≤
                testableMatchingMetric width B B' t

/-- P2, `cor:stability-data`: the guaranteed signed matching size is the
intersection of the two populations' own ranked recovery prefixes. Both
populations have the same stated regularity constants; neither the ranking
nor the tail is shared. Empty prefixes have size zero. -/
def PositivePrevalenceDataStabilitySpec : Prop :=
  ∀ (K : ℕ) (γ ρ cLower cUpper C₀ t : ℝ),
    1 ≤ K → 0 < γ → γ ≤ 1 → 0 < ρ →
    0 < cLower → cLower ≤ cUpper → 1 ≤ C₀ → t < 1 →
    ∃ C : ℝ, 1 < C ∧
      ∀ (X : Type u) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
        [MeasureTheory.IsProbabilityMeasure μ] (d M m : ℕ)
        (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
        (f : RepresentationMap X d),
        K < M → HasUnitEuclideanColumns A → StableAtomicRepresentation A z f γ K →
        RegularSparsePopulation (K := K) μ z ρ cLower cUpper →
        ∀ σ : Equiv.Perm (Fin M), Antitone (fun j => featurePrevalence μ z (σ j)) →
        1 ≤ m → m ≤ M →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : X → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          actualPopulationSquaredLoss μ A z B code ≤
            ENNReal.ofReal C₀ * optimalRecoveryLoss μ A z γ K m →
          ∀ (μ' : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ'],
            RegularSparsePopulation (K := K) μ' z ρ cLower cUpper →
            ∀ (σ' : Equiv.Perm (Fin M)), Antitone (fun j => featurePrevalence μ' z (σ' j)) →
            ∀ (B' : Matrix (Fin d) (Fin m) ℝ) (code' : X → FeatureVector m),
              IsFeasibleRecoveryPair B' code' γ K →
              actualPopulationSquaredLoss μ' A z B' code' ≤
                ENNReal.ofReal C₀ * optimalRecoveryLoss μ' A z γ K m →
              ((Finset.univ.filter fun j : Fin M =>
                  j.val < tailRecoverableRank (featurePrevalence μ z) σ C m).image σ ∩
                (Finset.univ.filter fun j : Fin M =>
                  j.val < tailRecoverableRank (featurePrevalence μ' z) σ' C m).image σ').card ≤
                testableMatchingMetric (fun _ : Unit => m) B (fun _ => B') t

/-- Activation F1 for the parent and both children of each qualifying family.
The support law has exactly L families and arbitrarily correlated child choices,
with each conditional child probability at least κ. Active coefficients have a
bounded joint density. The parent tail uses `floor(m/3)` and excludes absent
families. Each recovered feature has its own existential coordinate and threshold,
as in the source recovery definition. No directional conclusion is required. -/
def HierarchicalRecoverySpec : Prop :=
  ∀ (L : ℕ) (γ ρ κ cLower cUpper C₀ η : ℝ),
    1 ≤ L → 0 < γ → γ ≤ 1 → 0 < ρ → 0 < κ → κ ≤ 1 / 2 →
    0 < cLower → cLower ≤ cUpper → 1 ≤ C₀ → η < 1 →
    ∃ C : ℝ, 1 < C ∧
      ∀ (X : Type u) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
        (d N m : ℕ) (A : Matrix (Fin d) (Fin (N * 3)) ℝ)
        (z : X → FeatureVector (N * 3)) (f : RepresentationMap X d)
        (w : HierarchicalJointSample N L → ℝ),
        L < N → HasUnitEuclideanColumns A → StableAtomicRepresentation A z f γ (2 * L) →
        RegularHierarchicalPopulation μ z w ρ κ cLower cUpper →
        ∀ σ : Equiv.Perm (Fin N),
        Antitone (fun j => featurePrevalence μ z (hierarchicalParent (σ j))) →
        m ≤ N * 3 →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : X → FeatureVector m),
          IsFeasibleRecoveryPair B code γ (2 * L) →
          actualPopulationSquaredLoss μ A z B code ≤
            ENNReal.ofReal C₀ * optimalRecoveryLoss μ A z γ (2 * L) m →
          ∀ i : Fin N, 0 < featurePrevalence μ z (hierarchicalParent i) →
            C * rankedFeatureTail (fun k => featurePrevalence μ z (hierarchicalParent k))
              σ (m / 3) ≤ featurePrevalence μ z (hierarchicalParent i) →
            ActivationRecovered μ z code (hierarchicalParent i) η ∧
              ∀ k : Fin 2, ActivationRecovered μ z code (hierarchicalChild i k) η

/-- Small loss on any positive-probability source support gives a learned
K-span at the requested accuracy. The cutoff depends only on K, γ, the lower
density bound, and accuracy; it is uniform in the population and both widths.
The density lower bound is expressed as domination of the uniform cube law. -/
def ConditionalSpanRecoverySpec : Prop :=
  ∀ (K : ℕ) (γ cLower ε : ℝ),
    1 ≤ K → 0 < γ → γ ≤ 1 → 0 < cLower → 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (X : Type u) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
        [MeasureTheory.IsProbabilityMeasure μ] (d M m : ℕ)
        (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M),
        Measurable z → HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : X → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          ∀ S : ExactSourceSupport M K, μ (sourceSupportEvent z S.1) ≠ 0 →
          ENNReal.ofReal cLower • uniformCubeCoefficientLaw K ≤
            MeasureTheory.Measure.map (sourceSupportCoordinates z S)
              (sourceSupportConditionalLaw μ z S.1) →
          conditionalSupportSquaredLoss μ A z B code S.1 ≤ ENNReal.ofReal δ →
          ∃ T : Finset (Fin m), T.card = K ∧
            subspaceGap (euclideanColumnSpan A S.1) (euclideanColumnSpan B T) ≤ ε

/-- Activation transfer for any prescribed coordinate pair with identical
membership in a chosen good support family. Constants depend only on K, γ,
confidence and the upper density bound. The loss budget includes the actual
probability of leaving the good family, without a separation hypothesis. -/
def ActivationTransferSpec : Prop :=
  ∀ (K : ℕ) (γ cUpper η : ℝ),
    1 ≤ K → 0 < γ → 0 < cUpper → 0 < η → η < 1 →
    ∃ r c t : ℝ, 0 < r ∧ 0 < c ∧ 0 < t ∧
      ∀ (X : Type u) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
        [MeasureTheory.IsProbabilityMeasure μ] (d M m : ℕ)
        (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M),
        BoundedSparsePopulation (K := K) μ z →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : X → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          ∀ (G : Finset (ExactSourceSupport M K))
            (T : {s // s ∈ G} → Finset (Fin m)),
            (∀ s ∈ G, μ (sourceSupportEvent z s.1) ≠ 0) →
            (∀ s ∈ G, MeasureTheory.Measure.map (sourceSupportCoordinates z s)
              (sourceSupportConditionalLaw μ z s.1) ≤
                ENNReal.ofReal cUpper • uniformCubeCoefficientLaw K) →
            (∀ s, (T s).card = K) →
            (∀ s, subspaceGap (euclideanColumnSpan A s.1.1)
              (euclideanColumnSpan B (T s)) ≤ r) →
            ∀ (i : Fin M) (j : Fin m),
              (∀ s, i ∈ s.1.1 ↔ j ∈ T s) →
              0 < featurePrevalence μ z i →
              ∀ E : ℝ, 0 ≤ E → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal E →
                E + μ.real {x | nonzeroSupport (z x) ∉ G.image Subtype.val} ≤
                  c * featurePrevalence μ z i →
                η < populationF1 μ {x | 0 < z x i} {x | t < code x j}

/-- The support-intersection lemma, with a nonempty finite family and the
common sparse-stability margin made explicit. Projector distance agrees with
the equal-dimensional gap and remains defined when both intersections are
zero-dimensional. Both intersection cardinality and the stated quantitative
gap bound are conclusions. -/
def StableSupportIntersectionSpec : Prop :=
  ∀ (ι : Type u) (d M m K : ℕ) (γ r : ℝ)
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ),
    1 ≤ K → 0 < γ → 0 ≤ r →
    HasUnitEuclideanColumns A → HasUnitEuclideanColumns B →
    SparseLowerStable A γ (2 * K) → SparseLowerStable B γ (2 * K) →
    ∀ (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m)) (family : Finset ι),
      family.Nonempty →
      (∀ i ∈ family, (S i).card = K) → (∀ i ∈ family, (T i).card = K) →
      (∀ i ∈ family,
        subspaceGap (euclideanColumnSpan A (S i))
          (euclideanColumnSpan B (T i)) ≤ r) →
      r * (1 + 2 * (K : ℝ) / γ) < 1 →
      (supportFamilyIntersection S family).card =
        (supportFamilyIntersection T family).card ∧
      subspaceGap (euclideanColumnSpan A (supportFamilyIntersection S family))
        (euclideanColumnSpan B (supportFamilyIntersection T family)) ≤
        r * (1 + 2 * (K : ℝ) / γ)

/-- Lemma `lem:local-global-hall` for an arbitrary bipartite graph, including
global Hall, a left-saturating matching, and the cardinality conclusion. -/
def LocalToGlobalHallSpec : Prop :=
  ∀ (Left Right : Type u) (K : ℕ) (edges : Left → Right → Prop),
    1 ≤ K →
    (∀ vertices : Set Left,
      Cardinal.mk vertices ≤ ((2 * K : ℕ) : Cardinal.{u}) →
      Cardinal.mk vertices ≤ Cardinal.mk (LocalGlobalHall.graphNeighborhood edges vertices)) →
    (∀ vertices : Set Left,
      Cardinal.mk vertices ≤ (K : Cardinal.{u}) →
      Cardinal.mk (LocalGlobalHall.graphNeighborhood edges vertices) ≤
        ((2 * K - 1 : ℕ) : Cardinal.{u})) →
    (∀ vertices : Set Left,
      Cardinal.mk vertices ≤ Cardinal.mk (LocalGlobalHall.graphNeighborhood edges vertices)) ∧
    (∃ matching : Left → Right,
      Function.Injective matching ∧ ∀ x, edges x (matching x)) ∧
    Cardinal.mk Left ≤ Cardinal.mk Right

/-- Appendix `lem:inclusion`: sparse factorizations and open richness give
inclusion of the exact-support span unions. The alternative uses its effective
budget `min K' M'`, so no nonexistent supports or strict-spark restriction
are introduced for a full-column-rank competitor. -/
def SubspaceInclusionSpec : Prop :=
  ∀ (X : Type u) (d M M' K K' : ℕ)
    (matrix : Matrix (Fin d) (Fin M) ℝ) (code : X → FeatureVector M)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M') (f : RepresentationMap X d),
    KSparse (K := K) code → LinearFeatureRepresentation matrix code f →
    OpenKRich (K := K) code → KSparse (K := K') alternativeCode →
    LinearFeatureRepresentation alternative alternativeCode f →
    SparseSubspaceUnion matrix K ⊆ SparseSubspaceUnion alternative (min K' M')

/-- Theorem `thm:generic-rigidity`: for almost every unit-column source dictionary,
every stable alternative sparse factorization with more columns than the ambient
dimension satisfies both the sparsity bound and the strict half-width bound.
The source dimension is `d = n + 1`; `1 ≤ n` is exactly `2 ≤ d`. All input domains and
factorizations are quantified after the almost-everywhere choice of source, so
the exceptional set is uniform in them. -/
def GenericRigiditySpec : Prop :=
  ∀ (n M K : ℕ), 1 ≤ n → n + 1 < M → 1 ≤ K → K ≤ M →
    ∀ᵐ source ∂productUnitSphereSurfaceMeasure n M,
    ∀ (X : Type u) (code : X → FeatureVector M)
      (f : RepresentationMap X (n + 1)),
      KSparse (K := K) code →
      LinearFeatureRepresentation (ProductUnitSphere.matrix source) code f →
      OpenKRich (K := K) code →
      ∀ (M' K' : ℕ) (γ' : ℝ), n + 1 < M' → 0 < γ' →
      ∀ (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
        (alternativeCode : X → FeatureVector M'),
        KSparse (K := K') alternativeCode → LinearFeatureRepresentation alternative alternativeCode f →
        SparseLowerStable alternative γ' (2 * K') →
        (1 + (n : ℝ) * ((M : ℝ) - M') / M ≤ K') ∧
          (M : ℝ) / 2 < M'

/-! ## Supplementary results absent from the current manuscript -/

/-- Supplementary hierarchy obstruction. A distinct perfectly hierarchical
pair excludes open richness for nonnegative sparse codes. An explicit
normalized, stable example shows that rigidity can fail without richness;
this does not assert failure for every hierarchical source. -/
def HierarchyRichnessSpec : Prop :=
  (∀ (X : Type u) (M K : ℕ) (z : X → FeatureVector M),
    1 ≤ K → K < M → KSparse (K := K) z → NonnegativeFeatureMap z →
    ∀ child parent : Fin M, child ≠ parent →
      PerfectFeatureHierarchy z child parent → ¬ OpenKRich (K := K) z) ∧
  (∃ (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (z code : Set.Icc (0 : ℝ) 1 → FeatureVector 3),
    HasUnitEuclideanColumns A ∧ HasUnitEuclideanColumns B ∧
    SparseLowerStable A 1 4 ∧ SparseLowerStable B 1 4 ∧
    KSparse (K := 2) z ∧ KSparse (K := 2) code ∧
    (∀ t i, 0 ≤ z t i) ∧ (∀ t i, 0 ≤ code t i) ∧
    (∀ t i, z t i ≤ 1) ∧
    (∀ t, A.mulVec (z t) = B.mulVec (code t)) ∧
    (∀ t, 0 < z t 0 → 0 < z t 1) ∧
    ¬ OpenKRich (K := 2) z ∧ ¬ AtomicPairsEquivalent A z B code)


/-- A canonical three-dimensional witness for the mesoscale splitting
proposition. The source satisfies the stable atomic model, with orthonormal
identity columns and K=2. All global optima satisfy the table, a stronger
conclusion than restricting the claim to sparsity-tie-selected optima.
The source maps are fixed before the accuracy tolerance and the population.
Existence of the complete lexicographic selection at every width and strict
inequalities of actual optimal values
are part of the statement. -/
def CanonicalMesoscaleFeatureSplittingSpec : Prop :=
  ∃ (z f : FeatureVector 3 → FeatureVector 3),
    Measurable z ∧ Measurable f ∧
    AtomicPostulate (1 : Matrix (Fin 3) (Fin 3) ℝ) z f (1 / 2) 2 ∧
    Orthonormal ℝ (fun j => representationToEuclidean 3 ((1 : Matrix (Fin 3) (Fin 3) ℝ).col j)) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 3 →
      ∃ (μ : MeasureTheory.Measure (FeatureVector 3)),
      MeasureTheory.IsProbabilityMeasure μ ∧
      (∀ᵐ x ∂μ, z x = 0 ∨ (0 < z x 0 ∧
        ((0 < z x 1 ∧ z x 2 = 0) ∨ (z x 1 = 0 ∧ 0 < z x 2)))) ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ 3 →
        ∃ (B : Matrix (Fin 3) (Fin m) ℝ) (g : FeatureVector 3 → FeatureVector m),
          IsSparsitySelectedRepresentationPair μ 1 z f B g (1 / 2) 2) ∧
      (∀ (B : Matrix (Fin 3) (Fin 1) ℝ) (g : FeatureVector 3 → FeatureVector 1),
        IsOptimalRepresentationPair μ 1 z f B g (1 / 2) 2 →
          singleCoordinateF1Sup μ (FeatureActivationEvent z 0) (g ∘ f) = 1 ∧
          ∀ k : Fin 2, singleCoordinateF1Sup μ (FeatureActivationEvent z k.succ) (g ∘ f) = 2 / 3) ∧
      (∀ (B : Matrix (Fin 3) (Fin 2) ℝ) (g : FeatureVector 3 → FeatureVector 2),
        IsOptimalRepresentationPair μ 1 z f B g (1 / 2) 2 →
          singleCoordinateF1Sup μ (FeatureActivationEvent z 0) (g ∘ f) ≤ 2 / 3 + ε ∧
          ∀ k : Fin 2, 1 - ε ≤ singleCoordinateF1Sup μ (FeatureActivationEvent z k.succ) (g ∘ f)) ∧
      (∀ (B : Matrix (Fin 3) (Fin 3) ℝ) (g : FeatureVector 3 → FeatureVector 3),
        IsOptimalRepresentationPair μ 1 z f B g (1 / 2) 2 →
          ∀ i : Fin 3, singleCoordinateF1Sup μ (FeatureActivationEvent z i) (g ∘ f) = 1) ∧
      optimalRepresentationLoss μ 1 z f (1 / 2) 2 3 = 0 ∧
      optimalRepresentationLoss μ 1 z f (1 / 2) 2 3 <
        optimalRepresentationLoss μ 1 z f (1 / 2) 2 2 ∧
      optimalRepresentationLoss μ 1 z f (1 / 2) 2 2 <
        optimalRepresentationLoss μ 1 z f (1 / 2) 2 1

/-- Mesoscale feature splitting on any fixed measurable atomic representation
with three orthonormal columns and sparsity two. The population is chosen after
the source model and tolerance. Each lexicographic optimum exists and satisfies
the stated F1 table; the actual minimum reconstruction loss strictly decreases.
Measurability makes the coefficient and learned maps population observables. -/
def MesoscaleFeatureSplittingSpec : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (d : ℕ)
    (A : Matrix (Fin d) (Fin 3) ℝ) (z : X → FeatureVector 3)
    (f : RepresentationMap X d),
    Measurable z → RobustAtomicPostulate A z f (1 / 2) 2 →
    Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)) →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 3 →
      ∃ (μ : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure μ ∧
      (∀ᵐ x ∂μ, z x = 0 ∨ (0 < z x 0 ∧
        ((0 < z x 1 ∧ z x 2 = 0) ∨ (z x 1 = 0 ∧ 0 < z x 2)))) ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ 3 →
        ∃ (B : Matrix (Fin d) (Fin m) ℝ) (g : RepresentationVector d → FeatureVector m),
          IsSparsitySelectedRepresentationPair μ A z f B g (1 / 2) 2) ∧
      (∀ (B : Matrix (Fin d) (Fin 1) ℝ) (g : RepresentationVector d → FeatureVector 1),
        IsSparsitySelectedRepresentationPair μ A z f B g (1 / 2) 2 →
          singleCoordinateF1Sup μ (FeatureActivationEvent z 0) (g ∘ f) = 1 ∧
          ∀ k : Fin 2, singleCoordinateF1Sup μ (FeatureActivationEvent z k.succ) (g ∘ f) = 2 / 3) ∧
      (∀ (B : Matrix (Fin d) (Fin 2) ℝ) (g : RepresentationVector d → FeatureVector 2),
        IsSparsitySelectedRepresentationPair μ A z f B g (1 / 2) 2 →
          singleCoordinateF1Sup μ (FeatureActivationEvent z 0) (g ∘ f) ≤ 2 / 3 + ε ∧
          ∀ k : Fin 2, 1 - ε ≤ singleCoordinateF1Sup μ (FeatureActivationEvent z k.succ) (g ∘ f)) ∧
      (∀ (B : Matrix (Fin d) (Fin 3) ℝ) (g : RepresentationVector d → FeatureVector 3),
        IsSparsitySelectedRepresentationPair μ A z f B g (1 / 2) 2 →
          ∀ i : Fin 3, singleCoordinateF1Sup μ (FeatureActivationEvent z i) (g ∘ f) = 1) ∧
      optimalRepresentationLoss μ A z f (1 / 2) 2 3 = 0 ∧
      optimalRepresentationLoss μ A z f (1 / 2) 2 3 <
        optimalRepresentationLoss μ A z f (1 / 2) 2 2 ∧
      optimalRepresentationLoss μ A z f (1 / 2) 2 2 <
        optimalRepresentationLoss μ A z f (1 / 2) 2 1

/-! ## Supplementary uniform recovery constructions -/

/-- A supplementary uniform recovery construction: one positive threshold and one coordinate serve direction and activation simultaneously. -/
def UniformPositivePrevalenceRecoverySpec : Prop :=
  ∀ (K : ℕ) (γ ρ cLower cUpper C₀ η : ℝ),
    1 ≤ K → 0 < γ → γ ≤ 1 → 0 < ρ →
    0 < cLower → cLower ≤ cUpper → 1 ≤ C₀ → η < 1 →
    ∃ C t : ℝ, 1 < C ∧ 0 < t ∧
      ∀ (X : Type u) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
        [MeasureTheory.IsProbabilityMeasure μ] (d M m : ℕ)
        (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
        (f : RepresentationMap X d),
        K < M → HasUnitEuclideanColumns A → StableAtomicRepresentation A z f γ K →
        RegularSparsePopulation (K := K) μ z ρ cLower cUpper →
        ∀ σ : Equiv.Perm (Fin M), Antitone (fun j => featurePrevalence μ z (σ j)) →
        m ≤ M →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : X → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          actualPopulationSquaredLoss μ A z B code ≤
            ENNReal.ofReal C₀ * optimalRecoveryLoss μ A z γ K m →
          ∀ i : Fin M, 0 < featurePrevalence μ z i →
            C * rankedFeatureTail (featurePrevalence μ z) σ m ≤ featurePrevalence μ z i →
            ∃ j : Fin m,
              η < inner ℝ (representationToEuclidean d (A.col i))
                (representationToEuclidean d (B.col j)) ∧
              η < populationF1 μ (FeatureActivationEvent z i) {x | t < code x j}

/-- A supplementary hierarchical recovery construction: one positive threshold works for every qualifying family and all three roles. -/
def UniformHierarchicalRecoverySpec : Prop :=
  ∀ (L : ℕ) (γ ρ κ cLower cUpper C₀ η : ℝ),
    1 ≤ L → 0 < γ → γ ≤ 1 → 0 < ρ → 0 < κ → κ ≤ 1 / 2 →
    0 < cLower → cLower ≤ cUpper → 1 ≤ C₀ → η < 1 →
    ∃ C t : ℝ, 1 < C ∧ 0 < t ∧
      ∀ (X : Type u) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
        (d N m : ℕ) (A : Matrix (Fin d) (Fin (N * 3)) ℝ)
        (z : X → FeatureVector (N * 3)) (f : RepresentationMap X d)
        (w : HierarchicalJointSample N L → ℝ),
        L < N → HasUnitEuclideanColumns A → StableAtomicRepresentation A z f γ (2 * L) →
        RegularHierarchicalPopulation μ z w ρ κ cLower cUpper →
        ∀ σ : Equiv.Perm (Fin N),
        Antitone (fun j => featurePrevalence μ z (hierarchicalParent (σ j))) →
        m ≤ N * 3 →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : X → FeatureVector m),
          IsFeasibleRecoveryPair B code γ (2 * L) →
          actualPopulationSquaredLoss μ A z B code ≤
            ENNReal.ofReal C₀ * optimalRecoveryLoss μ A z γ (2 * L) m →
          ∀ i : Fin N, 0 < featurePrevalence μ z (hierarchicalParent i) →
            C * rankedFeatureTail (fun k => featurePrevalence μ z (hierarchicalParent k))
              σ (m / 3) ≤ featurePrevalence μ z (hierarchicalParent i) →
            ∃ j : Fin 3 → Fin m,
              η < populationF1 μ (FeatureActivationEvent z (hierarchicalParent i))
                {x | t < code x (j 0)} ∧
              ∀ k : Fin 2,
                η < populationF1 μ (FeatureActivationEvent z (hierarchicalChild i k))
                  {x | t < code x (j k.succ)}

end PKG26AtomicFeatures
