import PKG26AtomicFeatures.MesoscaleReferenceClipping
import PKG26AtomicFeatures.MesoscaleRiskPerturbation
import PKG26AtomicFeatures.MesoscaleDominantPredictions
import PKG26AtomicFeatures.CompactMinimizerPerturbation

/-!
# Width-two recovery for actual mesoscale population minimizers

The strict dominant active sets of every finite-reference minimizer form an
open neighborhood on the compact feasible dictionary class. A uniform
objective perturbation margin therefore preserves the dominant pattern.
The explicit population-risk comparison and almost-everywhere uniqueness
of actual NNLS encoders connect this neighborhood to actual global pair
optima and their population feature scores.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators InnerProductSpace Topology ENNReal

/-- The strict dominant active-set pattern on the actual feasible
reference dictionary space. -/
def MesoscaleStrictDominantPattern (B : MesoscaleReferenceDictionary) : Prop :=
  ∃ e : Equiv.Perm (Fin 2), ∀ s : Fin 2,
    0 < mesoscaleReferenceCode B.1 B.2.2 s.castSucc (e s) ∧
      ∀ j, j ≠ e s → nnlsResidualColumnInner B.1 (mesoscaleReferenceInput s.castSucc)
        (mesoscaleReferenceCode B.1 B.2.2 s.castSucc) j < 0

theorem continuous_mesoscaleReferenceCode (s : Fin 3) :
    Continuous (fun B : MesoscaleReferenceDictionary => mesoscaleReferenceCode B.1 B.2.2 s) := by
  have hdict : Continuous (fun B : MesoscaleReferenceDictionary =>
      (⟨B.1, B.2.2.global_bound_of_width_le (by norm_num)⟩ :
        GlobalStableDictionary 3 2 (1 / 2))) := continuous_subtype_val.subtype_mk _
  simpa only [stableDictionaryNNLSCode, mesoscaleReferenceCode] using
    (continuous_stableDictionaryNNLSCode (1 / 2) (by norm_num)).comp
    (hdict.prodMk (continuous_const (y := mesoscaleReferenceInput s)))

theorem continuous_mesoscaleReferenceColumnResidual (s : Fin 3) (j : Fin 2) :
    Continuous (fun B : MesoscaleReferenceDictionary =>
      nnlsResidualColumnInner B.1 (mesoscaleReferenceInput s)
        (mesoscaleReferenceCode B.1 B.2.2 s) j) := by
  have hdict : Continuous (fun B : MesoscaleReferenceDictionary =>
      (⟨B.1, B.2.2.global_bound_of_width_le (by norm_num)⟩ :
        GlobalStableDictionary 3 2 (1 / 2))) := continuous_subtype_val.subtype_mk _
  simpa only [stableDictionaryNNLSColumnResidual, stableDictionaryNNLSCode, mesoscaleReferenceCode] using
    (continuous_stableDictionaryNNLSColumnResidual (1 / 2) (by norm_num) j).comp
    (hdict.prodMk (continuous_const (y := mesoscaleReferenceInput s)))

/-- Strict coordinate inequalities give an open set on the actual
unit-column stable dictionary class. -/
theorem isOpen_mesoscaleStrictDominantPattern :
    IsOpen {B : MesoscaleReferenceDictionary | MesoscaleStrictDominantPattern B} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro B ⟨e, he⟩
  have hs (s : Fin 2) : ∀ᶠ C : MesoscaleReferenceDictionary in 𝓝 B,
      0 < mesoscaleReferenceCode C.1 C.2.2 s.castSucc (e s) ∧
        ∀ j, j ≠ e s → nnlsResidualColumnInner C.1 (mesoscaleReferenceInput s.castSucc)
          (mesoscaleReferenceCode C.1 C.2.2 s.castSucc) j < 0 := by
    have hactive := continuousAt_const.eventually_lt
      (((continuous_apply (e s)).comp (continuous_mesoscaleReferenceCode s.castSucc)).continuousAt)
      (he s).1
    have hinactive (j : Fin 2) : ∀ᶠ C : MesoscaleReferenceDictionary in 𝓝 B,
        j ≠ e s → nnlsResidualColumnInner C.1 (mesoscaleReferenceInput s.castSucc)
          (mesoscaleReferenceCode C.1 C.2.2 s.castSucc) j < 0 := by
      by_cases hj : j = e s
      · exact Filter.Eventually.of_forall (fun _ h => (h hj).elim)
      · exact ((continuous_mesoscaleReferenceColumnResidual s.castSucc j).continuousAt.eventually_lt
          continuousAt_const ((he s).2 j hj)).mono (fun _ h _ => h)
    filter_upwards [hactive, Filter.eventually_all.mpr hinactive] with C ha hi
    exact ⟨ha, hi⟩
  filter_upwards [Filter.eventually_all.mpr hs] with C hC
  exact ⟨e, hC⟩

/-- A single positive margin controls all globally minimizing dictionaries
of every uniformly close objective, with the strict pattern derived from
actual reference optimality. -/
theorem exists_mesoscale_strict_pattern_perturbation_margin :
    ∃ κ : ℝ, 0 < κ ∧ ∀ g : MesoscaleReferenceDictionary → ℝ,
      (∀ B, |g B - mesoscaleReferenceNNLSRisk B.1 B.2.2| ≤ κ) →
      ∀ B, (∀ C, g B ≤ g C) → MesoscaleStrictDominantPattern B := by
  letI : CompactSpace MesoscaleReferenceDictionary :=
    isCompact_iff_compactSpace.mp (isCompact_unitSparseLowerStable 3 2 4 (1 / 2))
  let benchmark : MesoscaleReferenceDictionary :=
    ⟨mesoscaleBenchmarkDictionary, mesoscaleBenchmarkDictionary_unit,
      mesoscaleBenchmarkDictionary_stable⟩
  obtain ⟨κ, hκ, hlocal⟩ := exists_uniform_objective_perturbation_margin
    (Set.univ : Set MesoscaleReferenceDictionary) {B | MesoscaleStrictDominantPattern B}
    (fun B => mesoscaleReferenceNNLSRisk B.1 B.2.2) isCompact_univ
    ⟨benchmark, Set.mem_univ _⟩ continuous_mesoscaleReferenceNNLSRisk.continuousOn
    isOpen_mesoscaleStrictDominantPattern (by
      intro B _ hB
      have hmin : IsMesoscaleReferenceMinimizer B.1 B.2.2 := by
        refine ⟨B.2.1, ?_⟩
        intro C hC hs
        exact hB ⟨C, hC, hs⟩ (Set.mem_univ _)
      exact hmin.strict_dominant_clipping)
  exact ⟨κ, hκ, fun g hg B hB => hlocal g (fun C _ => hg C) B (Set.mem_univ _) (fun C _ => hB C)⟩

/-- Actual canonical encoding on the primitive three-coordinate sample space. -/
noncomputable def mesoscaleWidthTwoEncoder (B : MesoscaleReferenceDictionary) :
    FeatureVector 3 → FeatureVector 2 :=
  nonnegativeLeastSquaresEncoder (representationToEuclidean 3) B.1 (1 / 2) (by norm_num)
    (B.2.2.global_bound_of_width_le (by norm_num))

/-- The actual real expected NNLS loss under the explicit mesoscale law. -/
noncomputable def mesoscaleWidthTwoPopulationRisk (δ θ H η : ℝ)
    (B : MesoscaleReferenceDictionary) : ℝ :=
  nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
    (representationToEuclidean 3) B.1 (1 / 2) (by norm_num)
    (B.2.2.global_bound_of_width_le (by norm_num))

theorem mesoscaleWidthTwoEncoder_feasible (B : MesoscaleReferenceDictionary) :
    IsFeasibleRecoveryPair B.1 (mesoscaleWidthTwoEncoder B) (1 / 2) 2 :=
  isFeasibleRecoveryPair_nonnegativeLeastSquaresEncoder
    (representationToEuclidean 3).continuous.measurable B.1 (1 / 2) (by norm_num)
    (B.2.2.global_bound_of_width_le (by norm_num)) B.2.1 B.2.2 (by norm_num)

theorem mesoscaleWidthTwoPopulationRisk_nonneg (δ θ H η : ℝ)
    (B : MesoscaleReferenceDictionary) : 0 ≤ mesoscaleWidthTwoPopulationRisk δ θ H η B :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem actualPopulationSquaredLoss_mesoscaleWidthTwoEncoder (δ θ H η : ℝ)
    (B : MesoscaleReferenceDictionary) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B.1 (mesoscaleWidthTwoEncoder B) =
      ENNReal.ofReal (mesoscaleWidthTwoPopulationRisk δ θ H η B) := by
  simpa only [actualPopulationSquaredLoss, euclideanPopulationSquaredLoss, Matrix.one_mulVec,
    id_eq, mesoscaleWidthTwoPopulationRisk, mesoscaleWidthTwoEncoder] using
    (ofReal_nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
      (representationToEuclidean 3).continuous.measurable
      (integrable_mesoscalePopulation_secondMoment δ θ H η) B.1 (1 / 2) (by norm_num)
      (B.2.2.global_bound_of_width_le (by norm_num))).symm

/-- Actual joint global optimality implies minimization of the canonical
population risk over all feasible width-two dictionaries. -/
theorem actual_width_two_optimal_pair_minimizes_populationRisk
    (δ θ H η : ℝ) (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    ∀ C : MesoscaleReferenceDictionary,
      mesoscaleWidthTwoPopulationRisk δ θ H η ⟨B, hopt.1.1, hopt.1.2.1⟩ ≤
        mesoscaleWidthTwoPopulationRisk δ θ H η C := by
  let B' : MesoscaleReferenceDictionary := ⟨B, hopt.1.1, hopt.1.2.1⟩
  intro C
  have hcanonical : actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B (mesoscaleWidthTwoEncoder B') ≤
      actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u := by
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    simpa only [Matrix.one_mulVec, id_eq] using
      (nonnegativeLeastSquaresCode_isMinimizer B (1 / 2) (by norm_num)
        (hopt.1.2.1.global_bound_of_width_le (by norm_num)) (representationToEuclidean 3 z)).2
        (u z) (hopt.1.2.2.2.2 z)
  have hcomp := hopt.2 C.1 (mesoscaleWidthTwoEncoder C) (mesoscaleWidthTwoEncoder_feasible C)
  simp only [ENNReal.ofReal_one, one_mul] at hcomp
  have hle := hcanonical.trans hcomp
  change actualPopulationSquaredLoss _ _ _ B'.1 _ ≤ _ at hle
  rw [actualPopulationSquaredLoss_mesoscaleWidthTwoEncoder,
    actualPopulationSquaredLoss_mesoscaleWidthTwoEncoder] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (mesoscaleWidthTwoPopulationRisk_nonneg δ θ H η C)).mp hle

/-- Compactness gives an actual global width-two dictionary/encoder
optimum, with a finite canonical loss and no selection premise. -/
theorem exists_mesoscale_width_two_optimal_pair (δ θ H η : ℝ) :
    ∃ (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2),
      IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 := by
  letI : CompactSpace MesoscaleReferenceDictionary :=
    isCompact_iff_compactSpace.mp (isCompact_unitSparseLowerStable 3 2 4 (1 / 2))
  let benchmark : MesoscaleReferenceDictionary :=
    ⟨mesoscaleBenchmarkDictionary, mesoscaleBenchmarkDictionary_unit,
      mesoscaleBenchmarkDictionary_stable⟩
  have hdict : Continuous (fun B : MesoscaleReferenceDictionary =>
      (⟨B.1, B.2.2.global_bound_of_width_le (by norm_num)⟩ :
        GlobalStableDictionary 3 2 (1 / 2))) := continuous_subtype_val.subtype_mk _
  have hc : Continuous (mesoscaleWidthTwoPopulationRisk δ θ H η) := by
    simpa only [mesoscaleWidthTwoPopulationRisk] using
      (continuous_nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
      (representationToEuclidean 3).continuous.measurable
      (integrable_mesoscalePopulation_secondMoment δ θ H η) (1 / 2) (by norm_num)).comp hdict
  obtain ⟨B, _, hB⟩ := isCompact_univ.exists_isMinOn
    (⟨benchmark, Set.mem_univ _⟩ : (Set.univ : Set MesoscaleReferenceDictionary).Nonempty)
    hc.continuousOn
  refine ⟨B.1, mesoscaleWidthTwoEncoder B, mesoscaleWidthTwoEncoder_feasible B, ?_⟩
  intro C v hC
  simp only [ENNReal.ofReal_one, one_mul]
  let C' : MesoscaleReferenceDictionary := ⟨C, hC.1, hC.2.1⟩
  have hcanonical : actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id C (mesoscaleWidthTwoEncoder C') ≤
      actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id C v := by
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    simpa only [Matrix.one_mulVec, id_eq] using
      (nonnegativeLeastSquaresCode_isMinimizer C (1 / 2) (by norm_num)
        (hC.2.1.global_bound_of_width_le (by norm_num)) (representationToEuclidean 3 z)).2
        (v z) (hC.2.2.2.2 z)
  apply le_trans _ hcanonical
  change actualPopulationSquaredLoss _ _ _ B.1 _ ≤ actualPopulationSquaredLoss _ _ _ C'.1 _
  rw [actualPopulationSquaredLoss_mesoscaleWidthTwoEncoder,
    actualPopulationSquaredLoss_mesoscaleWidthTwoEncoder]
  exact ENNReal.ofReal_le_ofReal (hB (Set.mem_univ C'))

/-- The explicit integrated population perturbation lies in the uniform
reference neighborhood once its scalar error bound is sufficiently small. -/
theorem exists_mesoscale_population_strict_pattern_margin :
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ θ H η : ℝ,
      0 ≤ δ → δ < 1 → 0 ≤ θ → θ ≤ 1 → 0 ≤ H → 0 ≤ η →
      δ * H ^ 2 = (3 / 5) * (1 - δ) →
      δ * η * (2 * H + η) + 2 * θ ≤ κ * (1 - δ) →
      ∀ B : MesoscaleReferenceDictionary,
        (∀ C, mesoscaleWidthTwoPopulationRisk δ θ H η B ≤
          mesoscaleWidthTwoPopulationRisk δ θ H η C) → MesoscaleStrictDominantPattern B := by
  obtain ⟨κ, hκ, hlocal⟩ := exists_mesoscale_strict_pattern_perturbation_margin
  refine ⟨κ, hκ, ?_⟩
  intro δ θ H η hδ hδone hθ hθone hH hη hcal herr B hB
  have hden : 0 < 1 - δ := sub_pos.mpr hδone
  let g : MesoscaleReferenceDictionary → ℝ := fun C =>
    mesoscaleWidthTwoPopulationRisk δ θ H η C / (1 - δ)
  apply hlocal g _ B
  · intro C
    exact div_le_div_of_nonneg_right (hB C) hden.le
  · intro C
    have hpert := nnls_mesoscalePopulation_perturbation C.1 (1 / 2) (by norm_num)
      (C.2.2.global_bound_of_width_le (by norm_num)) δ θ H η hδ hδone.le hθ hθone hH hη hcal
    change |mesoscaleWidthTwoPopulationRisk δ θ H η C -
      (1 - δ) * mesoscaleReferenceNNLSRisk C.1 C.2.2| ≤ _ at hpert
    change |mesoscaleWidthTwoPopulationRisk δ θ H η C / (1 - δ) -
      mesoscaleReferenceNNLSRisk C.1 C.2.2| ≤ κ
    have hid : mesoscaleWidthTwoPopulationRisk δ θ H η C / (1 - δ) -
        mesoscaleReferenceNNLSRisk C.1 C.2.2 =
        (mesoscaleWidthTwoPopulationRisk δ θ H η C -
          (1 - δ) * mesoscaleReferenceNNLSRisk C.1 C.2.2) / (1 - δ) := by
      rw [sub_div, mul_div_cancel_left₀ _ hden.ne']
    rw [hid, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    exact hpert.trans herr

/-- Almost-everywhere equality holds pointwise at every positive-mass
atom, without any regular conditional probability convention. -/
theorem eq_at_positive_mass_atom_of_ae_eq
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → E}
    (hfg : f =ᵐ[μ] g) (x : Ω) (hx : μ {x} ≠ 0) : f x = g x := by
  by_contra h
  apply hx
  exact measure_mono_null (by intro y hy; simpa only [Set.mem_singleton_iff.mp hy] using h)
    (ae_iff.mp hfg)

/-- Every actual globally optimal encoder agrees with canonical NNLS on
each dominant atom, whose positive mass is derived from the mixture. -/
theorem mesoscale_width_two_optimal_pair_dominant_code
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) (k : Fin 2) :
    u (mesoscalePlaneEmbedding k mesoscaleDominantPair) =
      mesoscaleReferenceCode B hopt.1.2.1 k.castSucc := by
  have hsecond := integrable_mesoscalePopulation_secondMoment δ θ H η
  have hae := hopt.ae_eq_nonnegativeLeastSquaresEncoder (by norm_num) (by norm_num)
    (by simpa only [Matrix.one_mulVec, id_eq] using (representationToEuclidean 3).continuous.measurable)
    (by simpa only [Matrix.one_mulVec, id_eq] using hsecond.lintegral_lt_top)
  have hmass := mesoscalePopulationLaw_dominant_mass_real δ θ H η hδ hδone.le hθ hθone.le k
  have hpos : 0 < (mesoscalePopulationLaw δ θ H η).real
      {mesoscalePlaneEmbedding k mesoscaleDominantPair} :=
    lt_of_lt_of_le (div_pos (mul_pos (sub_pos.mpr hθone) (sub_pos.mpr hδone)) (by norm_num)) hmass
  have hmassne : (mesoscalePopulationLaw δ θ H η)
      {mesoscalePlaneEmbedding k mesoscaleDominantPair} ≠ 0 := by
    intro hz
    simp [Measure.real, hz] at hpos
  have heq := eq_at_positive_mass_atom_of_ae_eq hae
    (mesoscalePlaneEmbedding k mesoscaleDominantPair) hmassne
  simpa only [nonnegativeLeastSquaresEncoder, Function.comp_apply, Matrix.one_mulVec, id_eq,
    mesoscaleDominantPoint_eq_reference, mesoscaleReferenceCode] using heq

/-- The uniform reference margin controls the actual width-two F1 table
for every globally optimal nonnegative dictionary/encoder pair. The law,
loss, clipping pattern, and atom-code equality are all derived from the
primitive mixture and actual optimization assumptions. -/
theorem exists_mesoscale_width_two_recovery_margin :
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ θ H η : ℝ,
      0 ≤ δ → δ < 1 → 0 ≤ θ → θ < 1 → 0 < H → 0 < η →
      δ * H ^ 2 = (3 / 5) * (1 - δ) →
      δ * η * (2 * H + η) + 2 * θ ≤ κ * (1 - δ) →
      ∀ (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2),
        IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 →
        (∀ k : Fin 2, 1 - 2 * (δ + θ) ≤
          singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z k.succ} u) ∧
        singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z 0} u ≤
          2 * (1 + (δ + θ)) / (3 + (δ + θ)) ∧
        2 * (1 + (δ + θ)) / (3 + (δ + θ)) ≤ 2 / 3 + (δ + θ) := by
  obtain ⟨κ, hκ, hlocal⟩ := exists_mesoscale_population_strict_pattern_margin
  refine ⟨κ, hκ, ?_⟩
  intro δ θ H η hδ hδone hθ hθone hH hη hcal herr B u hopt
  have hpattern := hlocal δ θ H η hδ hδone hθ hθone.le hH.le hη.le hcal herr
    ⟨B, hopt.1.1, hopt.1.2.1⟩
    (actual_width_two_optimal_pair_minimizes_populationRisk δ θ H η B u hopt)
  obtain ⟨e, he⟩ := hpattern
  have hcode := mesoscale_width_two_optimal_pair_dominant_code δ θ H η hδ hδone hθ hθone B u hopt
  apply mesoscale_F1_table_of_dominant_pattern δ θ H η hδ hδone.le hθ hθone.le hH hη u hopt.1.2.2.1
  refine ⟨e, ?_⟩
  intro k
  refine ⟨?_, ?_⟩
  · rw [hcode]
    exact (he k).1
  · rw [hcode]
    apply (mesoscaleReferenceCode_isNNLS B hopt.1.2.1 (Fin.rev k).castSucc).eq_zero_of_columnResidual_neg
    apply (he (Fin.rev k)).2
    intro heq
    have hkr : k = Fin.rev k := e.injective heq
    fin_cases k <;> norm_num [Fin.rev] at hkr

end PKG26AtomicFeatures
