import PKG26AtomicFeatures.MesoscaleCountableScaledConstruction
import PKG26AtomicFeatures.OrthonormalPopulationTransport
import PKG26AtomicFeatures.SparseCubeSourceMoments

/-!
# Mesoscale splitting on an arbitrary fixed orthonormal atomic source

The source domain, source dictionary, and observed representation are fixed
before the feature tolerance and population are chosen. A countably supported
coefficient construction lifts through the measurable surjective source map.
Gram-preserving ambient compression compares all feasible learned dictionaries,
including dictionaries with columns outside the source span. Actual population
codes and scores are preserved without assuming a measurable ambient encoder.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal Matrix

/-- An attained representation optimum equals the actual infimum over
feasible dictionaries and representation-dependent encoders. -/
theorem IsOptimalRepresentationPair.loss_eq_optimalRepresentationLoss
    {X : Type*} [MeasurableSpace X] {d M m K : ℕ}
    {μ : Measure X} {A : Matrix (Fin d) (Fin M) ℝ}
    {z : X → FeatureVector M} {f : X → RepresentationVector d}
    {B : Matrix (Fin d) (Fin m) ℝ} {g : RepresentationVector d → FeatureVector m}
    {γ : ℝ} (hopt : IsOptimalRepresentationPair μ A z f B g γ K) :
    actualPopulationSquaredLoss μ A z B (g ∘ f) =
      optimalRepresentationLoss μ A z f γ K m := by
  unfold optimalRepresentationLoss
  apply le_antisymm
  · exact le_iInf fun C => le_iInf fun h => le_iInf fun hc => hopt.2 C h hc
  · exact iInf_le_of_le B (iInf_le_of_le g (iInf_le_of_le hopt.1 le_rfl))

/-- Every fixed measurable orthonormal three-atom source has a population
exhibiting the mesoscale table. Selected optima exist at all three widths;
the feature guarantees hold for every primary optimum, and hence for every
optimum selected by the expected-support tie-break. -/
theorem mesoscaleFeatureSplittingForOrthonormalSource
    {X : Type*} [MeasurableSpace X] {d : ℕ}
    (A : Matrix (Fin d) (Fin 3) ℝ) (z : X → FeatureVector 3)
    (f : X → RepresentationVector d) (hz : Measurable z)
    (hpost : AtomicPostulate A z f (1 / 2) 2)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧
      (∀ᵐ x ∂μ, z x = 0 ∨ (0 < z x 0 ∧
        ((0 < z x 1 ∧ z x 2 = 0) ∨ (z x 1 = 0 ∧ 0 < z x 2)))) ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ 3 →
        ∃ (B : Matrix (Fin d) (Fin m) ℝ) (g : RepresentationVector d → FeatureVector m),
          IsSparsitySelectedRepresentationPair μ A z f B g (1 / 2) 2) ∧
      (∀ (B : Matrix (Fin d) (Fin 1) ℝ) (g : RepresentationVector d → FeatureVector 1),
        IsOptimalRepresentationPair μ A z f B g (1 / 2) 2 →
          singleCoordinateF1Sup μ {x | 0 < z x 0} (g ∘ f) = 1 ∧
          ∀ k : Fin 2, singleCoordinateF1Sup μ {x | 0 < z x k.succ} (g ∘ f) = 2 / 3) ∧
      (∀ (B : Matrix (Fin d) (Fin 2) ℝ) (g : RepresentationVector d → FeatureVector 2),
        IsOptimalRepresentationPair μ A z f B g (1 / 2) 2 →
          singleCoordinateF1Sup μ {x | 0 < z x 0} (g ∘ f) ≤ 2 / 3 + ε ∧
          ∀ k : Fin 2, 1 - ε ≤ singleCoordinateF1Sup μ {x | 0 < z x k.succ} (g ∘ f)) ∧
      (∀ (B : Matrix (Fin d) (Fin 3) ℝ) (g : RepresentationVector d → FeatureVector 3),
        IsOptimalRepresentationPair μ A z f B g (1 / 2) 2 →
          ∀ i : Fin 3, singleCoordinateF1Sup μ {x | 0 < z x i} (g ∘ f) = 1) ∧
      optimalRepresentationLoss μ A z f (1 / 2) 2 3 = 0 ∧
      optimalRepresentationLoss μ A z f (1 / 2) 2 3 <
        optimalRepresentationLoss μ A z f (1 / 2) 2 2 ∧
      optimalRepresentationLoss μ A z f (1 / 2) 2 2 <
        optimalRepresentationLoss μ A z f (1 / 2) 2 1 := by
  have hfeq : f = fun x => A.mulVec (z x) := funext hpost.2.2.2
  subst f
  have hrange : Set.range z = SparseUnitCube 3 2 := hpost.2.2.1
  obtain ⟨δ, θ, H, η, hδ, hδone, hθ, hθone, hH, hη, hηone, _hbudget, _hcal,
    hprob, hcount, hcube, hfamily, _hcard, hattain, hone, htwo, hthree, hzero, h32, h21⟩ :=
    exists_mesoscale_countable_scaled_construction ε hε
  let ν := mesoscaleCountableScaledPopulationLaw δ θ H η
  letI : IsProbabilityMeasure ν := hprob
  obtain ⟨μ, hμprob, hmap⟩ := exists_mesoscaleCountableScaledPopulationLaw_lift z hz hrange
    δ θ H η hδ.le hδone.le hθ.le hθone.le hH hη hηone
  letI : IsProbabilityMeasure μ := hμprob
  have hsourcecube : ∀ᵐ x ∂μ, z x ∈ SparseUnitCube 3 2 :=
    Filter.Eventually.of_forall fun x => hrange ▸ Set.mem_range_self x
  have hz2 := integrable_norm_sq_of_ae_sparseUnitCube μ z hz hsourcecube
  obtain ⟨S, hScount, hSae⟩ := hcount
  have hTcount : (S ∩ SparseUnitCube 3 2).Countable := hScount.mono Set.inter_subset_left
  have hTae : ∀ᵐ q ∂Measure.map z μ, q ∈ S ∩ SparseUnitCube 3 2 := by
    rw [hmap]
    exact hSae.and hcube
  have hTrange : S ∩ SparseUnitCube 3 2 ⊆ Set.range z := by
    rw [hrange]
    exact Set.inter_subset_right
  have hfiniteCanonical {m : ℕ} (C : Matrix (Fin 3) (Fin m) ℝ)
      (u : FeatureVector 3 → FeatureVector m)
      (hopt : IsApproximatelyOptimalRecoveryPair ν (1 : Matrix (Fin 3) (Fin 3) ℝ)
        id C u (1 / 2) 1 2) :
      actualPopulationSquaredLoss ν (1 : Matrix (Fin 3) (Fin 3) ℝ) id C u < ⊤ := by
    have hc : IsOptimalRepresentationPair ν (1 : Matrix (Fin 3) (Fin 3) ℝ)
        id id C u (1 / 2) 2 := by
      refine ⟨by simpa only [Function.comp_id] using hopt.1, ?_⟩
      intro D v hv
      have hv' : IsFeasibleRecoveryPair D v (1 / 2) 2 := by
        simpa only [Function.comp_id] using hv
      simpa only [Function.comp_id, ENNReal.ofReal_one, one_mul] using hopt.2 D v hv'
    simpa only [Function.comp_id] using
      hc.loss_lt_top_of_sparseUnitCube (identityDictionary_orthonormal 3) hcube
  have hselected (m : ℕ) (hm : 1 ≤ m) (hmthree : m ≤ 3) :
      ∃ (B : Matrix (Fin d) (Fin m) ℝ) (g : RepresentationVector d → FeatureVector m),
        IsSparsitySelectedRepresentationPair μ A z (fun x => A.mulVec (z x)) B g (1 / 2) 2 := by
    obtain ⟨C, u, hopt, hsecondary⟩ := hattain m hm hmthree
    have hoptmap : IsApproximatelyOptimalRecoveryPair (Measure.map z μ)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id C u (1 / 2) 1 2 := by rwa [hmap]
    have hfinite : actualPopulationSquaredLoss (Measure.map z μ)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id C u < ⊤ := by
      rw [hmap]
      exact hfiniteCanonical C u hopt
    refine ⟨A * C, u ∘ A.transpose.mulVec,
      orthonormal_representation_lift_selected μ A hA z hz hz2 C u (1 / 2)
        (by norm_num) hmthree (by omega) hoptmap hfinite ?_ hTcount hTae hTrange⟩
    simpa only [hmap] using hsecondary
  have hcompress {m : ℕ} (hm : m ≤ 3)
      (B : Matrix (Fin d) (Fin m) ℝ) (g : RepresentationVector d → FeatureVector m)
      (hopt : IsOptimalRepresentationPair μ A z (fun x => A.mulVec (z x)) B g (1 / 2) 2) :
      ∃ (C : Matrix (Fin 3) (Fin m) ℝ) (u : FeatureVector 3 → FeatureVector m),
        IsApproximatelyOptimalRecoveryPair ν (1 : Matrix (Fin 3) (Fin 3) ℝ) id C u (1 / 2) 1 2 ∧
        ∀ i, singleCoordinateF1Sup μ {x | 0 < z x i} (g ∘ fun x => A.mulVec (z x)) =
          singleCoordinateF1Sup ν {q | 0 < q i} u := by
    obtain ⟨C, u, hu, _, _, _, hscore, _⟩ :=
      exists_coefficient_optimum_preserving_observables μ A hA z hz hz2 B g (1 / 2)
        (by norm_num) hm (by omega) hopt (hopt.loss_lt_top_of_sparseUnitCube hA hsourcecube)
        hTcount hTae hTrange
    rw [hmap] at hu hscore
    exact ⟨C, u, hu, hscore⟩
  have hloss (m : ℕ) (hm : 1 ≤ m) (hmthree : m ≤ 3) :
      optimalRepresentationLoss μ A z (fun x => A.mulVec (z x)) (1 / 2) 2 m =
        optimalRecoveryLoss ν (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 m := by
    obtain ⟨C, u, hopt, _⟩ := hattain m hm hmthree
    have hoptmap : IsApproximatelyOptimalRecoveryPair (Measure.map z μ)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id C u (1 / 2) 1 2 := by rwa [hmap]
    have hlift := hoptmap.orthonormal_representation_lift μ A hA z hz hz2
      (by norm_num) hmthree (by omega) hTcount hTae hTrange
    calc
      _ = actualPopulationSquaredLoss μ A z (A * C)
          ((u ∘ A.transpose.mulVec) ∘ fun x => A.mulVec (z x)) :=
        hlift.loss_eq_optimalRepresentationLoss.symm
      _ = actualPopulationSquaredLoss (Measure.map z μ) (1 : Matrix (Fin 3) (Fin 3) ℝ)
          id C u := orthonormalRepresentation_loss_lift μ A hA z hz C u hopt.1.2.2.1
      _ = optimalRecoveryLoss ν (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 m := by
        rw [hmap]
        exact hopt.loss_eq_optimalRecoveryLoss
  refine ⟨μ, hμprob, ?_, hselected, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : ∀ᵐ q ∂Measure.map z μ, MesoscaleHierarchicalPresence q := by
      rwa [hmap]
    exact (ae_of_ae_map hz.aemeasurable hp).mono fun _ h => Or.inr h
  · intro B g hopt
    obtain ⟨C, u, hu, hscore⟩ := hcompress (by norm_num) B g hopt
    obtain ⟨hp, hc⟩ := hone C u hu
    exact ⟨(hscore 0).trans hp, fun k => (hscore k.succ).trans (hc k)⟩
  · intro B g hopt
    obtain ⟨C, u, hu, hscore⟩ := hcompress (by norm_num) B g hopt
    obtain ⟨hp, hc⟩ := htwo C u hu
    refine ⟨?_, ?_⟩
    · rw [hscore 0]
      exact hp
    · intro k
      rw [hscore k.succ]
      exact hc k
  · intro B g hopt
    obtain ⟨C, u, hu, hscore⟩ := hcompress (by norm_num) B g hopt
    obtain ⟨_, _, _, hf⟩ := hthree C u hu
    exact fun i => (hscore i).trans (hf i)
  · rw [hloss 3 (by norm_num) (by norm_num)]
    exact hzero
  · rw [hloss 3 (by norm_num) (by norm_num), hloss 2 (by norm_num) (by norm_num)]
    exact h32
  · rw [hloss 2 (by norm_num) (by norm_num), hloss 1 (by norm_num) (by norm_num)]
    exact h21

end PKG26AtomicFeatures
