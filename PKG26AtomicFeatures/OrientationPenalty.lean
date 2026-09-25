import PKG26AtomicFeatures.ProjectedCoefficientCodes
import PKG26AtomicFeatures.UniformCubeCoefficients
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# A loss penalty for the wrong orientation of a learned atom

The coefficients occupy a positive cube. A learned atom close to the negative
of a source atom makes the corresponding projected coefficient negative on a
positive-volume rectangular part of that cube. Sparse stability then forces
positive reconstruction error for every nonnegative sparse code.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- Euclidean unit coordinate vector used to select a source atom. -/
noncomputable def coefficientBasisVector {K : ℕ} (i : Fin K) : EuclideanRepresentation K :=
  representationToEuclidean K (Pi.single i 1 : FeatureVector K)

@[simp] theorem norm_coefficientBasisVector {K : ℕ} (i : Fin K) :
    ‖coefficientBasisVector i‖ = 1 := by
  change ‖PiLp.single (β := fun _ : Fin K => ℝ) 2 i (1 : ℝ)‖ = 1
  simp only [PiLp.norm_single, norm_one]

/-- Stability bounds every projected coefficient vector by the source norm. -/
theorem projected_coefficient_norm_upper_bound {d M K : ℕ}
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (D : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation M)
    (hT : T.card ≤ K)
    (hsupport : ∀ z, nonzeroSupport ((representationToEuclidean M).symm (D z)) ⊆ T)
    (hD : ∀ z, representationToEuclidean d
      (B.mulVec ((representationToEuclidean M).symm (D z))) =
        (euclideanColumnSpan B T).starProjection (F z))
    (γ b : ℝ) (hγ : 0 < γ) (hstable : SparseLowerStable B γ (2 * K))
    (hupper : ∀ z, ‖F z‖ ≤ b * ‖z‖) (z : EuclideanRepresentation K) :
    ‖D z‖ ≤ (b / γ) * ‖z‖ := by
  have hcard : (nonzeroSupport ((representationToEuclidean M).symm (D z))).card ≤ 2 * K :=
    ((Finset.card_le_card (hsupport z)).trans hT).trans (by omega)
  have hbound := hstable ((representationToEuclidean M).symm (D z)) hcard
  rw [(representationToEuclidean M).apply_symm_apply, hD z] at hbound
  have hproj := (euclideanColumnSpan B T).norm_starProjection_apply_le (F z)
  have h := hbound.trans (hproj.trans (hupper z))
  have h' : ‖D z‖ ≤ (b * ‖z‖) / γ :=
    (le_div_iff₀ hγ).mpr (by simpa only [mul_comm] using h)
  convert h' using 1
  ring

/-- An atom close to the negative source direction forces a negative entry
in the actual projected coefficient map. The map's synthesis equation and
sparse stability derive the orientation conclusion. -/
theorem projected_coordinate_negative_of_wrong_orientation {d M K : ℕ}
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (D : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation M)
    (hT : T.card ≤ K)
    (hsupport : ∀ z, nonzeroSupport ((representationToEuclidean M).symm (D z)) ⊆ T)
    (hD : ∀ z, representationToEuclidean d
      (B.mulVec ((representationToEuclidean M).symm (D z))) =
        (euclideanColumnSpan B T).starProjection (F z))
    (γ : ℝ) (hγ : 0 < γ) (hstable : SparseLowerStable B γ (2 * K))
    (i : Fin K) (j : Fin M) (hj : j ∈ T)
    (hwrong : ‖F (coefficientBasisVector i) + representationToEuclidean d (B.col j)‖ ≤ γ / 2) :
    (D (coefficientBasisVector i)) j ≤ -(1 / 2 : ℝ) := by
  classical
  let v : FeatureVector M :=
    (representationToEuclidean M).symm (D (coefficientBasisVector i)) + Pi.single j 1
  have hv : nonzeroSupport v ⊆ T := by
    apply nonzeroSupport_subset_of_mem_coordinateSpan
    exact (coordinateSpan T).add_mem
      (mem_coordinateSpan_of_nonzeroSupport_subset (hsupport _))
      (canonicalVector_mem_coordinateSpan T hj)
  have hcol : representationToEuclidean d (B.col j) ∈ euclideanColumnSpan B T := by
    apply (mem_euclideanColumnSpan_iff_exists_code B T _).mpr
    refine ⟨Pi.single j 1,
      nonzeroSupport_subset_of_mem_coordinateSpan (canonicalVector_mem_coordinateSpan T hj), ?_⟩
    simp only [Matrix.mulVec_single_one]
  have hsyn : representationToEuclidean d (B.mulVec v) =
      (euclideanColumnSpan B T).starProjection
        (F (coefficientBasisVector i) + representationToEuclidean d (B.col j)) := by
    dsimp only [v]
    rw [Matrix.mulVec_add, map_add, hD, Matrix.mulVec_single_one, map_add,
      (euclideanColumnSpan B T).starProjection_eq_self_iff.mpr hcol]
  have hbound := hstable v (((Finset.card_le_card hv).trans hT).trans (by omega))
  rw [hsyn] at hbound
  have hcontract := (euclideanColumnSpan B T).norm_starProjection_apply_le
    (F (coefficientBasisVector i) + representationToEuclidean d (B.col j))
  have hvnorm : ‖representationToEuclidean M v‖ ≤ 1 / 2 := by
    have h := hbound.trans (hcontract.trans hwrong)
    nlinarith
  have hcoordinate := PiLp.norm_apply_le (representationToEuclidean M v) j
  have heval : (representationToEuclidean M v) j = (D (coefficientBasisVector i)) j + 1 := by
    dsimp only [v]
    rw [map_add, (representationToEuclidean M).apply_symm_apply]
    change (D (coefficientBasisVector i)) j +
      (representationToEuclidean M (Pi.single j 1 : FeatureVector M)) j = _
    simp only [representationToEuclidean, PiLp.continuousLinearEquiv_symm_apply,
      Pi.single_eq_same]
  rw [heval, Real.norm_eq_abs] at hcoordinate
  have h := (le_abs_self ((D (coefficientBasisVector i)) j + 1)).trans
    (hcoordinate.trans hvnorm)
  linarith

/-- A rectangle in the positive cube: the selected coordinate is in
`[1/2,1]`, and every other coordinate is in `[0,h]`. -/
def orientationCoefficientBox {K : ℕ} (i : Fin K) (h : ℝ) : Set (FeatureVector K) :=
  Set.pi Set.univ fun l => if l = i then Set.Icc (1 / 2 : ℝ) 1 else Set.Icc 0 h

/-- A negative diagonal coefficient dominates the small remaining
coordinates on the orientation rectangle. -/
theorem coefficient_functional_negative_on_orientationBox {K : ℕ}
    (L : EuclideanRepresentation K →L[ℝ] ℝ) (i : Fin K) (H h : ℝ)
    (hH : 0 ≤ H) (hh : 0 ≤ h) (hsize : (K : ℝ) * h * H ≤ 1 / 8)
    (hnegative : L (coefficientBasisVector i) ≤ -(1 / 2 : ℝ))
    (hcoeff : ∀ l, |L (coefficientBasisVector l)| ≤ H)
    (z : FeatureVector K) (hz : z ∈ orientationCoefficientBox i h) :
    L (representationToEuclidean K z) ≤ -(1 / 8 : ℝ) := by
  classical
  have hzall : ∀ l, z l ∈ if l = i then Set.Icc (1 / 2 : ℝ) 1 else Set.Icc 0 h := by
    simpa only [orientationCoefficientBox, Set.mem_pi, Set.mem_univ, forall_true_left] using hz
  have hzi : 1 / 2 ≤ z i ∧ z i ≤ 1 := by simpa using hzall i
  have hzother : ∀ l, l ≠ i → 0 ≤ z l ∧ z l ≤ h := by
    intro l hli
    simpa only [if_neg hli, Set.mem_Icc] using hzall l
  have hrepr : representationToEuclidean K z =
      ∑ l : Fin K, z l • coefficientBasisVector l := by
    simp only [coefficientBasisVector, ← map_smul, ← map_sum]
    congr 1
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hrepr, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hi : z i * L (coefficientBasisVector i) ≤ -(1 / 4 : ℝ) := by
    have hprod := mul_le_mul_of_nonneg_left hnegative (by linarith : 0 ≤ z i)
    nlinarith
  have hothers : (∑ l ∈ (Finset.univ : Finset (Fin K)).erase i,
      z l * L (coefficientBasisVector l)) ≤ 1 / 8 := by
    calc
      _ ≤ ∑ _l ∈ (Finset.univ : Finset (Fin K)).erase i, h * H := by
        apply Finset.sum_le_sum
        intro l hl
        have hz' := hzother l (Finset.mem_erase.mp hl).1
        have hL := (le_abs_self _).trans (hcoeff l)
        exact (mul_le_mul_of_nonneg_left hL hz'.1).trans
          (mul_le_mul_of_nonneg_right hz'.2 hH)
      _ = (((Finset.univ : Finset (Fin K)).erase i).card : ℝ) * (h * H) := by simp
      _ ≤ (K : ℝ) * (h * H) := mul_le_mul_of_nonneg_right
        (by
          have hc : ((Finset.univ : Finset (Fin K)).erase i).card ≤ K := by
            simpa only [Fintype.card_fin] using Finset.card_le_univ
              ((Finset.univ : Finset (Fin K)).erase i)
          exact_mod_cast hc)
        (mul_nonneg hh hH)
      _ ≤ 1 / 8 := by simpa only [mul_assoc] using hsize
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  linarith

theorem measurableSet_orientationCoefficientBox {K : ℕ} (i : Fin K) (h : ℝ) :
    MeasurableSet (orientationCoefficientBox i h) := by
  apply MeasurableSet.pi (Set.to_countable _)
  intro l _
  split_ifs <;> exact measurableSet_Icc

theorem orientationCoefficientBox_subset_unitCube {K : ℕ} (i : Fin K)
    (h : ℝ) (hh : h ≤ 1) : orientationCoefficientBox i h ⊆ coefficientUnitCube K := by
  intro z hz
  simp only [orientationCoefficientBox, Set.mem_pi, Set.mem_univ, forall_true_left] at hz
  simp only [coefficientUnitCube, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc]
  intro l
  by_cases hli : l = i
  · have hzl : 1 / 2 ≤ z l ∧ z l ≤ 1 := by simpa only [if_pos hli, Set.mem_Icc] using hz l
    exact ⟨by linarith [hzl.1], hzl.2⟩
  · have hzl : 0 ≤ z l ∧ z l ≤ h := by simpa only [if_neg hli, Set.mem_Icc] using hz l
    exact ⟨hzl.1, hzl.2.trans hh⟩

/-- A pointwise version of the cube norm bound, including its boundary. -/
theorem norm_le_of_mem_coefficientUnitCube {K : ℕ} (z : FeatureVector K)
    (hz : z ∈ coefficientUnitCube K) :
    ‖representationToEuclidean K z‖ ≤ (K : ℝ) + 1 := by
  have hz' : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    simpa only [coefficientUnitCube, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_Icc] using hz
  have hsq : ‖representationToEuclidean K z‖ ^ 2 ≤ (K : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin K, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        change (z i) ^ 2 ≤ 1
        nlinarith [(hz' i).1, (hz' i).2]
      _ = K := by simp
  nlinarith [norm_nonneg (representationToEuclidean K z), (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]

/-- Wrong orientation forces error at least `γ/16` on the rectangle for
every nonnegative `K`-sparse actual code. The projected coefficient map is
constructed from the stable dictionary; it is not an orientation premise. -/
theorem residual_lower_bound_on_orientationBox {d M K : ℕ}
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (γ b δ h : ℝ) (hγ : 0 < γ) (hb : 0 < b) (hδ : 0 ≤ δ)
    (hh : 0 ≤ h) (hhone : h ≤ 1) (hsize : (K : ℝ) * h * (b / γ) ≤ 1 / 8)
    (hT : T.card ≤ K) (hstable : SparseLowerStable B γ (2 * K))
    (hupper : ∀ z, ‖F z‖ ≤ b * ‖z‖)
    (hgap : ‖(LinearMap.range F.toLinearMap).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ)
    (hsmall : δ * b * ((K : ℝ) + 1) ≤ γ / 16)
    (i : Fin K) (j : Fin M) (hj : j ∈ T)
    (hwrong : ‖F (coefficientBasisVector i) + representationToEuclidean d (B.col j)‖ ≤ γ / 2)
    (z : FeatureVector K) (hz : z ∈ orientationCoefficientBox i h)
    (u : FeatureVector M) (hu : (nonzeroSupport u).card ≤ K) (hunonneg : ∀ l, 0 ≤ u l) :
    γ / 16 ≤ ‖F (representationToEuclidean K z) - representationToEuclidean d (B.mulVec u)‖ := by
  obtain ⟨D, hsupport, hD⟩ := exists_projected_support_coefficient_map F B T γ hγ hstable hT
  let L := (PiLp.proj 2 (fun _ : Fin M => ℝ) j).comp D
  have hnegative : L (coefficientBasisVector i) ≤ -(1 / 2 : ℝ) :=
    projected_coordinate_negative_of_wrong_orientation F B T D hT hsupport hD γ hγ hstable i j hj hwrong
  have hcoeff : ∀ l, |L (coefficientBasisVector l)| ≤ b / γ := by
    intro l
    have hnorm := projected_coefficient_norm_upper_bound F B T D hT hsupport hD
      γ b hγ hstable hupper (coefficientBasisVector l)
    rw [norm_coefficientBasisVector, mul_one] at hnorm
    exact (PiLp.norm_apply_le (D (coefficientBasisVector l)) j).trans hnorm
  have hnegative_z := coefficient_functional_negative_on_orientationBox L i (b / γ) h
    (div_pos hb hγ).le hh hsize hnegative hcoeff z hz
  change (D (representationToEuclidean K z)) j ≤ -(1 / 8 : ℝ) at hnegative_z
  have hcoordinate := PiLp.norm_apply_le
    (representationToEuclidean M u - D (representationToEuclidean K z)) j
  change |u j - (D (representationToEuclidean K z)) j| ≤
    ‖representationToEuclidean M u - D (representationToEuclidean K z)‖ at hcoordinate
  have hcode_lower : 1 / 8 ≤
      ‖representationToEuclidean M u - D (representationToEuclidean K z)‖ := by
    have habs := le_abs_self (u j - (D (representationToEuclidean K z)) j)
    linarith [hunonneg j]
  have hinverse := actual_code_distance_le_projected_residuals F B T D hT hsupport hD
    γ hstable δ hgap (representationToEuclidean K z) u hu
  have hnormz := norm_le_of_mem_coefficientUnitCube z
    (orientationCoefficientBox_subset_unitCube i h hhone hz)
  have herror : δ * ‖F (representationToEuclidean K z)‖ ≤ γ / 16 := by
    calc
      _ ≤ δ * (b * ‖representationToEuclidean K z‖) :=
        mul_le_mul_of_nonneg_left (hupper _) hδ
      _ ≤ δ * (b * ((K : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnormz hb.le) hδ
      _ ≤ γ / 16 := by simpa only [mul_assoc] using hsmall
  nlinarith

/-- The orientation rectangle has its explicit product volume. -/
theorem volume_orientationCoefficientBox {K : ℕ} (i : Fin K) (h : ℝ) :
    volume (orientationCoefficientBox i h) =
      ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal h ^ (K - 1) := by
  classical
  rw [orientationCoefficientBox, volume_pi, Measure.pi_pi]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin K))
    (fun l => (volume : Measure ℝ) (if l = i then Set.Icc (1 / 2 : ℝ) 1 else Set.Icc 0 h))
    (Finset.mem_univ i)]
  have hprod : (∏ l ∈ (Finset.univ : Finset (Fin K)).erase i,
      (volume : Measure ℝ) (if l = i then Set.Icc (1 / 2 : ℝ) 1 else Set.Icc 0 h)) =
      ENNReal.ofReal h ^ (K - 1) := by
    calc
      _ = ∏ _l ∈ (Finset.univ : Finset (Fin K)).erase i, ENNReal.ofReal h := by
        apply Finset.prod_congr rfl
        intro l hl
        rw [if_neg (Finset.mem_erase.mp hl).1, Real.volume_Icc, sub_zero]
      _ = _ := by simp
  rw [hprod]
  norm_num [Real.volume_Icc]

/-- The same orientation rectangle in Euclidean coefficient coordinates. -/
noncomputable def orientationEuclideanBox {K : ℕ} (i : Fin K) (h : ℝ) :
    Set (EuclideanRepresentation K) :=
  (representationToEuclidean K).symm ⁻¹' orientationCoefficientBox i h

theorem measurableSet_orientationEuclideanBox {K : ℕ} (i : Fin K) (h : ℝ) :
    MeasurableSet (orientationEuclideanBox i h) :=
  (measurableSet_orientationCoefficientBox i h).preimage
    (representationToEuclidean K).symm.continuous.measurable

/-- Its probability under the reference cube law is exactly its volume. -/
theorem uniformCubeCoefficientLaw_orientationBox {K : ℕ} (i : Fin K)
    (h : ℝ) (hh : h ≤ 1) :
    uniformCubeCoefficientLaw K (orientationEuclideanBox i h) =
      ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal h ^ (K - 1) := by
  rw [uniformCubeCoefficientLaw, Measure.map_apply
    (representationToEuclidean K).continuous.measurable
    (measurableSet_orientationEuclideanBox i h)]
  have hpre : (representationToEuclidean K) ⁻¹' orientationEuclideanBox i h =
      orientationCoefficientBox i h := by
    ext z
    simp only [orientationEuclideanBox, Set.mem_preimage,
      (representationToEuclidean K).symm_apply_apply]
  rw [hpre, uniformCubeCoordinateLaw, Measure.restrict_apply
    (measurableSet_orientationCoefficientBox i h),
    Set.inter_eq_left.mpr (orientationCoefficientBox_subset_unitCube i h hh)]
  exact volume_orientationCoefficientBox i h

/-- A lower density bound on the cube is precisely the measure domination
needed for the orientation penalty, even with correlated coordinates. -/
theorem cube_withDensity_ge_of_ae_lower_bound
    (K : ℕ) (f : EuclideanRepresentation K → ℝ≥0∞) (c : ℝ≥0∞)
    (hbound : ∀ᵐ z ∂uniformCubeCoefficientLaw K, c ≤ f z) :
    c • uniformCubeCoefficientLaw K ≤ (uniformCubeCoefficientLaw K).withDensity f := by
  simpa only [withDensity_const] using withDensity_mono hbound

/-- A residual floor on the orientation rectangle yields an explicit
expected squared-loss floor under any law with the stated lower density.
The random input space is unrestricted, and its coefficients are mapped to
the cube law before imposing the density comparison. -/
theorem squared_loss_lower_bound_of_orientationBox
    {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) (Z : Ω → EuclideanRepresentation K) (hZ : Measurable Z)
    (c h r : ℝ) (hh : h ≤ 1) (hr : 0 ≤ r)
    (hdom : ENNReal.ofReal c • uniformCubeCoefficientLaw K ≤ Measure.map Z μ)
    (i : Fin K) (residual : Ω → ℝ)
    (hres : ∀ ω, Z ω ∈ orientationEuclideanBox i h → r ≤ residual ω) :
    ENNReal.ofReal (r ^ 2) *
        (ENNReal.ofReal c * (ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal h ^ (K - 1))) ≤
      ∫⁻ ω, ENNReal.ofReal (residual ω ^ 2) ∂μ := by
  let box := Z ⁻¹' orientationEuclideanBox i h
  have hbox : MeasurableSet box := (measurableSet_orientationEuclideanBox i h).preimage hZ
  have hmass : ENNReal.ofReal c *
      (ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal h ^ (K - 1)) ≤ μ box := by
    have h := hdom (orientationEuclideanBox i h)
    rw [Measure.smul_apply, smul_eq_mul, uniformCubeCoefficientLaw_orientationBox i _ hh,
      Measure.map_apply hZ (measurableSet_orientationEuclideanBox i _)] at h
    exact h
  have hindicator : box.indicator (fun _ => ENNReal.ofReal (r ^ 2)) ≤
      fun ω => ENNReal.ofReal (residual ω ^ 2) := by
    intro ω
    by_cases hω : ω ∈ box
    · rw [Set.indicator_of_mem hω]
      apply ENNReal.ofReal_le_ofReal
      have h := hres ω hω
      nlinarith
    · rw [Set.indicator_of_notMem hω]
      exact zero_le _
  calc
    _ ≤ ENNReal.ofReal (r ^ 2) * μ box := mul_le_mul_right hmass _
    _ = ∫⁻ ω, box.indicator (fun _ => ENNReal.ofReal (r ^ 2)) ω ∂μ :=
      (lintegral_indicator_const hbox _).symm
    _ ≤ _ := lintegral_mono hindicator

/-- A side length depending only on the source upper bound, decoding
margin, and sparsity order, small enough for the negative coordinate to
dominate throughout the rectangle. -/
noncomputable def orientationBoxSide (K : ℕ) (H : ℝ) : ℝ :=
  min (1 / 2 : ℝ) (1 / (8 * H * (K : ℝ)))

theorem orientationBoxSide_bounds {K : ℕ} (hK : 0 < K) (H : ℝ) (hH : 0 < H) :
    0 < orientationBoxSide K H ∧ orientationBoxSide K H ≤ 1 ∧
      (K : ℝ) * orientationBoxSide K H * H ≤ 1 / 8 := by
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hden : 0 < 8 * H * (K : ℝ) := by positivity
  refine ⟨lt_min (by norm_num) (one_div_pos.mpr hden),
    (min_le_left _ _).trans (by norm_num), ?_⟩
  have hh : orientationBoxSide K H ≤ 1 / (8 * H * (K : ℝ)) := min_le_right _ _
  have hmul := (le_div_iff₀ hden).mp hh
  nlinarith

/-- Explicit positive loss scale for wrong orientation. -/
noncomputable def orientationLossFloor (K : ℕ) (γ b c : ℝ) : ℝ :=
  (γ / 16) ^ 2 * (c * ((1 / 2 : ℝ) * (orientationBoxSide K (b / γ)) ^ (K - 1)))

theorem orientationLossFloor_pos {K : ℕ} (hK : 0 < K)
    (γ b c : ℝ) (hγ : 0 < γ) (hb : 0 < b) (hc : 0 < c) :
    0 < orientationLossFloor K γ b c := by
  have hh := (orientationBoxSide_bounds hK (b / γ) (div_pos hb hγ)).1
  unfold orientationLossFloor
  positivity

/-- A wrongly oriented selected atom forces a uniform, strictly positive
conditional loss under a lower-bounded cube density. Both the projected
coefficient map and the positive-volume negative-coefficient region are
derived; the actual encoder only needs nonnegative, sparse coefficients. -/
theorem wrong_orientation_squared_loss_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {d M K : ℕ}
    (μ : Measure Ω) (Z : Ω → EuclideanRepresentation K) (hZ : Measurable Z)
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (code : Ω → FeatureVector M)
    (γ b c δ : ℝ) (hγ : 0 < γ) (hb : 0 < b) (hc : 0 < c) (hδ : 0 ≤ δ)
    (hdom : ENNReal.ofReal c • uniformCubeCoefficientLaw K ≤ Measure.map Z μ)
    (hT : T.card ≤ K) (hstable : SparseLowerStable B γ (2 * K))
    (hupper : ∀ z, ‖F z‖ ≤ b * ‖z‖)
    (hgap : ‖(LinearMap.range F.toLinearMap).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ)
    (hsmall : δ * b * ((K : ℝ) + 1) ≤ γ / 16)
    (i : Fin K) (j : Fin M) (hj : j ∈ T)
    (hwrong : ‖F (coefficientBasisVector i) + representationToEuclidean d (B.col j)‖ ≤ γ / 2)
    (hsparse : ∀ ω, (nonzeroSupport (code ω)).card ≤ K)
    (hnonneg : ∀ ω l, 0 ≤ code ω l) :
    ENNReal.ofReal (orientationLossFloor K γ b c) ≤
      ∫⁻ ω, ENNReal.ofReal (‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖ ^ 2) ∂μ := by
  have hK : 0 < K := by have hi := i.isLt; omega
  obtain ⟨hhpos, hhone, hhsize⟩ := orientationBoxSide_bounds hK (b / γ) (div_pos hb hγ)
  have hpoint : ∀ ω, Z ω ∈ orientationEuclideanBox i (orientationBoxSide K (b / γ)) →
      γ / 16 ≤ ‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖ := by
    intro ω hω
    have h := residual_lower_bound_on_orientationBox F B T γ b δ (orientationBoxSide K (b / γ))
      hγ hb hδ hhpos.le hhone hhsize hT hstable hupper hgap hsmall i j hj hwrong
      ((representationToEuclidean K).symm (Z ω)) hω (code ω) (hsparse ω) (hnonneg ω)
    simpa only [(representationToEuclidean K).apply_symm_apply] using h
  have hloss := squared_loss_lower_bound_of_orientationBox μ Z hZ c
    (orientationBoxSide K (b / γ)) (γ / 16) hhone (by positivity) hdom i _ hpoint
  simpa only [orientationLossFloor, ENNReal.ofReal_mul (sq_nonneg (γ / 16)),
    ENNReal.ofReal_mul hc.le, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_pow hhpos.le] using hloss

end PKG26AtomicFeatures
