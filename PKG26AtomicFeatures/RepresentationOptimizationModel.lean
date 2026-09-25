import PKG26AtomicFeatures.FeatureSupportExpectation

/-!
# Atomic representations and population optimization

Source codes range over the nonnegative sparse unit cube. Feasible learned
maps depend only on the observed representation. Reconstruction loss and
expected activation count define the two successive optimization objectives.
-/

namespace PKG26AtomicFeatures

universe u

/-- The postulate's codomain `[0,1]^{M,K}` consists of the nonnegative
unit-cube vectors with at most `K` nonzero coordinates. -/
def SparseUnitCube (M K : ℕ) : Set (FeatureVector M) :=
  {v | (nonzeroSupport v).card ≤ K ∧ ∀ i, 0 ≤ v i ∧ v i ≤ 1}

/-- Accessibility bounds changes in the feature code by changes in the
observed representation. Both distances use Euclidean norms. -/
def FeatureAccessible {X : Type u} {d M : ℕ}
    (z : X → FeatureVector M) (f : X → RepresentationVector d) (γ : ℝ) : Prop :=
  ∀ x y, ‖representationToEuclidean M (z x - z y)‖ ≤
    ‖representationToEuclidean d (f x - f y)‖ / γ

/-- A stable atomic dictionary and code representation. Equality
of the range to the sparse cube includes both the code's bounded codomain
and surjectivity. The model's parameter restrictions occur in the Spec. -/
def AtomicPostulate {X : Type u} {d M : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (f : X → RepresentationVector d) (γ : ℝ) (K : ℕ) : Prop :=
  HasUnitEuclideanColumns A ∧ SparseLowerStable A γ (2 * K) ∧
    Set.range z = SparseUnitCube M K ∧ ∀ x, f x = A.mulVec (z x)

/-- Sparse lower stability controls code distances on the represented data:
the difference of two source codes has at most `2K` nonzero coordinates. -/
theorem AtomicPostulate.featureAccessible
    {X : Type u} {d M K : ℕ} {γ : ℝ}
    {A : Matrix (Fin d) (Fin M) ℝ} {z : X → FeatureVector M}
    {f : X → RepresentationVector d}
    (h : AtomicPostulate A z f γ K) (hγ : 0 < γ) :
    FeatureAccessible z f γ := by
  have hsparse (x : X) : (nonzeroSupport (z x)).card ≤ K := by
    have hx : z x ∈ SparseUnitCube M K := h.2.2.1 ▸ Set.mem_range_self x
    exact hx.1
  intro x y
  apply (le_div_iff₀ hγ).mpr
  simpa only [h.2.2.2 x, h.2.2.2 y, mul_comm] using
    h.2.1.code_distance (z x) (z y) (hsparse x) (hsparse y)

/-- Exact optimization over dictionaries and learned maps that depend only
on the observed representation. Feasibility constrains the actual composed
map on the source input domain. -/
def IsOptimalRepresentationPair
    {X : Type*} [MeasurableSpace X] {d M m : ℕ}
    (μ : MeasureTheory.Measure X) (A : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (B : Matrix (Fin d) (Fin m) ℝ) (g : RepresentationVector d → FeatureVector m)
    (γ : ℝ) (K : ℕ) : Prop :=
  IsFeasibleRecoveryPair B (g ∘ f) γ K ∧
    ∀ (B' : Matrix (Fin d) (Fin m) ℝ) (g' : RepresentationVector d → FeatureVector m),
      IsFeasibleRecoveryPair B' (g' ∘ f) γ K →
        actualPopulationSquaredLoss μ A z B (g ∘ f) ≤
          actualPopulationSquaredLoss μ A z B' (g' ∘ f)

/-- Actual optimal loss in the representation-dependent encoder class,
including nonattained infima and infinite losses. -/
noncomputable def optimalRepresentationLoss
    {X : Type*} [MeasurableSpace X] {d M : ℕ}
    (μ : MeasureTheory.Measure X) (A : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (γ : ℝ) (K m : ℕ) : ENNReal :=
  ⨅ (B : Matrix (Fin d) (Fin m) ℝ) (g : RepresentationVector d → FeatureVector m)
    (_ : IsFeasibleRecoveryPair B (g ∘ f) γ K), actualPopulationSquaredLoss μ A z B (g ∘ f)

/-- The source's lexicographic selection: first minimize actual reconstruction
loss and then actual expected support among all primary minimizers. -/
def IsSparsitySelectedRepresentationPair
    {X : Type*} [MeasurableSpace X] {d M m : ℕ}
    (μ : MeasureTheory.Measure X) (A : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (B : Matrix (Fin d) (Fin m) ℝ) (g : RepresentationVector d → FeatureVector m)
    (γ : ℝ) (K : ℕ) : Prop :=
  IsOptimalRepresentationPair μ A z f B g γ K ∧
    ∀ (C : Matrix (Fin d) (Fin m) ℝ) (h : RepresentationVector d → FeatureVector m),
      IsOptimalRepresentationPair μ A z f C h γ K →
        expectedCodeSupportSize μ (g ∘ f) ≤ expectedCodeSupportSize μ (h ∘ f)

end PKG26AtomicFeatures
