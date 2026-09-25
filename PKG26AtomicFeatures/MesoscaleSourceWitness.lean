import PKG26AtomicFeatures.MesoscaleAllWidthTieBreak

/-!
# A fixed atomic representation exhibiting mesoscale feature splitting

The identity dictionary and one fixed measurable retraction realize the full
sparse unit cube. For each accuracy tolerance, the scaled construction supplies
a population on this same source model. All comparisons are over encoders that
factor through the observed representation. Almost-sure identity transports
both the optimization problem and the feature scores without altering them.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set

/-- One fixed source model exhibits the complete three-width recovery table
for every tolerance. All primary optima satisfy the table; optimizer existence
and strict inequalities of actual infimum losses are also proved. -/
theorem canonicalMesoscaleFeatureSplitting :
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
          singleCoordinateF1Sup μ {x | 0 < z x 0} (g ∘ f) = 1 ∧
          ∀ k : Fin 2, singleCoordinateF1Sup μ {x | 0 < z x k.succ} (g ∘ f) = 2 / 3) ∧
      (∀ (B : Matrix (Fin 3) (Fin 2) ℝ) (g : FeatureVector 3 → FeatureVector 2),
        IsOptimalRepresentationPair μ 1 z f B g (1 / 2) 2 →
          singleCoordinateF1Sup μ {x | 0 < z x 0} (g ∘ f) ≤ 2 / 3 + ε ∧
          ∀ k : Fin 2, 1 - ε ≤ singleCoordinateF1Sup μ {x | 0 < z x k.succ} (g ∘ f)) ∧
      (∀ (B : Matrix (Fin 3) (Fin 3) ℝ) (g : FeatureVector 3 → FeatureVector 3),
        IsOptimalRepresentationPair μ 1 z f B g (1 / 2) 2 →
          ∀ i : Fin 3, singleCoordinateF1Sup μ {x | 0 < z x i} (g ∘ f) = 1) ∧
      optimalRepresentationLoss μ 1 z f (1 / 2) 2 3 = 0 ∧
      optimalRepresentationLoss μ 1 z f (1 / 2) 2 3 <
        optimalRepresentationLoss μ 1 z f (1 / 2) 2 2 ∧
      optimalRepresentationLoss μ 1 z f (1 / 2) 2 2 <
        optimalRepresentationLoss μ 1 z f (1 / 2) 2 1 := by
  let f := sparseCubeRetraction 3 2
  have hf : Measurable f := measurable_sparseCubeRetraction 3 2
  refine ⟨f, f, hf, hf, atomicPostulate_sparseCubeRetraction 3 2 (1 / 2) (by norm_num),
    identityDictionary_orthonormal 3, ?_⟩
  intro ε hε _hεthird
  obtain ⟨δ, θ, H, η, _hδ, _hδone, _hθ, _hθone, _hH, _hη, _hηone, _hbudget, _hcal,
    hprob, hcube, hpresence, _hsupport, _hattain, hone, htwo, hthree, hzero, h32, h21⟩ :=
    exists_mesoscale_scaled_construction ε hε
  let μ := mesoscaleScaledPopulationLaw δ θ H η
  have hfid : f =ᵐ[μ] id := sparseCubeRetraction_ae_eq_id μ hcube
  have hscore {m : ℕ} (u : FeatureVector 3 → FeatureVector m) (i : Fin 3) :
      singleCoordinateF1Sup μ {x | 0 < f x i} u =
        singleCoordinateF1Sup μ {x | 0 < x i} u :=
    singleCoordinateF1Sup_ae_identity_source μ hfid u i
  have hloss (m : ℕ) : optimalRepresentationLoss μ 1 f f (1 / 2) 2 m =
      optimalRecoveryLoss μ 1 id (1 / 2) 2 m :=
    optimalRepresentationLoss_eq_ambient_of_ae_identity μ f hf hfid (1 / 2)
  refine ⟨μ, hprob, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hfid, hpresence] with x hx hp
    right
    simpa only [hx, id_eq] using hp
  · intro m hm hmthree
    obtain ⟨B, u, hopt, htie⟩ := exists_mesoscale_scaled_all_width_support_tie_optima
      δ θ H η _hδ _hδone _hθ _hθone _hH _hη m hm hmthree
    refine ⟨B, u, hopt.representation_of_ae_identity f hf hfid, ?_⟩
    intro C g hC
    have hcmp := htie C (g ∘ f) (hC.ambient_of_ae_identity hf hfid)
    have heq : expectedCodeSupportSize μ (u ∘ f) = expectedCodeSupportSize μ u :=
      expectedCodeSupportSize_congr_ae μ (hfid.mono fun x hx => congrArg u hx)
    exact heq.le.trans hcmp
  · intro B g hopt
    obtain ⟨hp, hc⟩ := hone B (g ∘ f) (hopt.ambient_of_ae_identity hf hfid)
    exact ⟨(hscore _ 0).trans hp, fun k => (hscore _ k.succ).trans (hc k)⟩
  · intro B g hopt
    obtain ⟨hp, hc⟩ := htwo B (g ∘ f) (hopt.ambient_of_ae_identity hf hfid)
    refine ⟨?_, ?_⟩
    · rw [hscore]
      exact hp
    · intro k
      rw [hscore]
      exact hc k
  · intro B g hopt
    obtain ⟨_, _, _, hscores⟩ := hthree B (g ∘ f) (hopt.ambient_of_ae_identity hf hfid)
    exact fun i => (hscore _ i).trans (hscores i)
  · rw [hloss]
    exact hzero
  · rw [hloss, hloss]
    exact h32
  · rw [hloss, hloss]
    exact h21

end PKG26AtomicFeatures
