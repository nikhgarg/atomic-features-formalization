import PKG26AtomicFeatures.StableSupportIntersections
import Mathlib.Analysis.InnerProductSpace.Dual

namespace PKG26AtomicFeatures

/-- Synthesis restricted to a coordinate support, with values in the
corresponding Euclidean column span. -/
noncomputable def supportedSynthesisLinearMap {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M)) :
    coordinateSpan T →ₗ[ℝ] euclideanColumnSpan B T where
  toFun u := ⟨representationToEuclidean d (B.mulVec u.1),
    (mem_euclideanColumnSpan_iff_exists_code B T _).mpr
      ⟨u.1, nonzeroSupport_subset_of_mem_coordinateSpan u.2, rfl⟩⟩
  map_add' u v := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Matrix.mulVec_add, map_add]
  map_smul' t u := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Matrix.mulVec_smul, map_smul, RingHom.id_apply]

/-- A stable dictionary identifies its supported coordinate space with the
span of the selected columns. Surjectivity follows from the definition of
the column span, and sparse stability proves injectivity. -/
theorem supportedSynthesisLinearMap_bijective {d M K : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (γ : ℝ) (hγ : 0 < γ) (hstable : SparseLowerStable B γ (2 * K))
    (hT : T.card ≤ K) : Function.Bijective (supportedSynthesisLinearMap B T) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    apply hstable.sparseInjective hγ u.1 v.1
    · exact (Finset.card_le_card (nonzeroSupport_subset_of_mem_coordinateSpan u.2)).trans hT
    · exact (Finset.card_le_card (nonzeroSupport_subset_of_mem_coordinateSpan v.2)).trans hT
    · apply (representationToEuclidean d).injective
      exact congrArg Subtype.val huv
  · intro x
    obtain ⟨u, hu, hux⟩ := (mem_euclideanColumnSpan_iff_exists_code B T x.1).mp x.2
    exact ⟨⟨u, mem_coordinateSpan_of_nonzeroSupport_subset hu⟩, Subtype.ext hux⟩

/-- The orthogonal projection of a source linear map onto a stable selected
column span has an actual continuous linear coefficient map supported there. -/
theorem exists_projected_support_coefficient_map {d M K : ℕ}
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (γ : ℝ) (hγ : 0 < γ) (hstable : SparseLowerStable B γ (2 * K))
    (hT : T.card ≤ K) :
    ∃ D : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation M,
      (∀ z, nonzeroSupport ((representationToEuclidean M).symm (D z)) ⊆ T) ∧
      ∀ z, representationToEuclidean d
        (B.mulVec ((representationToEuclidean M).symm (D z))) =
          (euclideanColumnSpan B T).starProjection (F z) := by
  let e := LinearEquiv.ofBijective (supportedSynthesisLinearMap B T)
    (supportedSynthesisLinearMap_bijective B T γ hγ hstable hT)
  let C : EuclideanRepresentation K →ₗ[ℝ] coordinateSpan T :=
    e.symm.toLinearMap.comp ((euclideanColumnSpan B T).orthogonalProjection.toLinearMap.comp
      F.toLinearMap)
  let D : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation M :=
    ((representationToEuclidean M).toLinearMap.comp
      ((coordinateSpan T).subtype.comp C)).toContinuousLinearMap
  have hD (z) : (representationToEuclidean M).symm (D z) = (C z).1 := by
    exact (representationToEuclidean M).symm_apply_apply _
  refine ⟨D, fun z => ?_, fun z => ?_⟩
  · rw [hD]
    exact nonzeroSupport_subset_of_mem_coordinateSpan (C z).2
  · rw [hD]
    have h := e.apply_symm_apply ((euclideanColumnSpan B T).orthogonalProjection (F z))
    exact congrArg Subtype.val h

/-- Unit upper column bounds give a coarse Euclidean synthesis bound by
the support cardinality times the Euclidean coefficient norm. -/
theorem synthesis_norm_le_support_card_mul_coefficient_norm {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ)
    (hunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (T : Finset (Fin M)) (u : FeatureVector M) (hu : nonzeroSupport u ⊆ T) :
    ‖representationToEuclidean d (B.mulVec u)‖ ≤
      (T.card : ℝ) * ‖representationToEuclidean M u‖ := by
  classical
  calc
    _ ≤ ∑ j ∈ nonzeroSupport u, |u j| := euclidean_mulVec_norm_le_sum_abs B hunit u
    _ ≤ ∑ _j ∈ nonzeroSupport u, ‖representationToEuclidean M u‖ := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (representationToEuclidean M u) j
    _ = ((nonzeroSupport u).card : ℝ) * ‖representationToEuclidean M u‖ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hu) (norm_nonneg _)

/-- A projected coefficient map has the same residual as orthogonal
projection, bounded by the projector gap times the source-vector norm. -/
theorem projected_coefficient_residual_le {d M K : ℕ}
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (D : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation M)
    (hD : ∀ z, representationToEuclidean d
      (B.mulVec ((representationToEuclidean M).symm (D z))) =
        (euclideanColumnSpan B T).starProjection (F z))
    (δ : ℝ) (hgap : ‖(LinearMap.range F.toLinearMap).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ) (z : EuclideanRepresentation K) :
    ‖F z - representationToEuclidean d
      (B.mulVec ((representationToEuclidean M).symm (D z)))‖ ≤ δ * ‖F z‖ := by
  rw [hD]
  have hsource : (LinearMap.range F.toLinearMap).starProjection (F z) = F z :=
    Submodule.starProjection_eq_self_iff.mpr ⟨z, rfl⟩
  calc
    _ = ‖((LinearMap.range F.toLinearMap).starProjection -
        (euclideanColumnSpan B T).starProjection) (F z)‖ := by
      rw [ContinuousLinearMap.sub_apply, hsource]
    _ ≤ ‖(LinearMap.range F.toLinearMap).starProjection -
        (euclideanColumnSpan B T).starProjection‖ * ‖F z‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hgap (norm_nonneg _)

/-- A sufficiently accurate projected coefficient map has a lower margin.
The factor `K` is a coarse synthesis bound valid for unit upper columns. -/
theorem projected_coefficient_norm_lower_bound {d M K : ℕ}
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (D : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation M)
    (hK : 0 < K) (hT : T.card ≤ K)
    (hsupport : ∀ z, nonzeroSupport ((representationToEuclidean M).symm (D z)) ⊆ T)
    (hD : ∀ z, representationToEuclidean d
      (B.mulVec ((representationToEuclidean M).symm (D z))) =
        (euclideanColumnSpan B T).starProjection (F z))
    (hunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (a b δ : ℝ) (hδ : 0 ≤ δ)
    (hlower : ∀ z, a * ‖z‖ ≤ ‖F z‖) (hupper : ∀ z, ‖F z‖ ≤ b * ‖z‖)
    (hsmall : δ * b ≤ a / 2)
    (hgap : ‖(LinearMap.range F.toLinearMap).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ) (z : EuclideanRepresentation K) :
    (a / (2 * (K : ℝ))) * ‖z‖ ≤ ‖D z‖ := by
  have herr := projected_coefficient_residual_le F B T D hD δ hgap z
  have hu := synthesis_norm_le_support_card_mul_coefficient_norm B hunit T
    ((representationToEuclidean M).symm (D z)) (hsupport z)
  rw [(representationToEuclidean M).apply_symm_apply] at hu
  have hcard : (T.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hT
  have hupper' := mul_le_mul_of_nonneg_left (hupper z) hδ
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (norm_nonneg z)
  have hnorm := hlower z
  have hsyn := mul_le_mul_of_nonneg_right hcard (norm_nonneg (D z))
  have htriangle := norm_add_le
    (F z - representationToEuclidean d (B.mulVec ((representationToEuclidean M).symm (D z))))
    (representationToEuclidean d (B.mulVec ((representationToEuclidean M).symm (D z))))
  rw [sub_add_cancel] at htriangle
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  apply (mul_le_mul_iff_left₀ (show 0 < 2 * (K : ℝ) by positivity)).mp
  have heq : (a / (2 * (K : ℝ))) * ‖z‖ * (2 * (K : ℝ)) = a * ‖z‖ := by field_simp
  rw [heq]
  nlinarith

/-- A coefficient map supported on exactly `K` coordinates and bounded
below has the whole selected coordinate space as its range. -/
theorem range_eq_euclidean_coordinate_span_of_lower_bound {M K : ℕ}
    (D : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation M)
    (T : Finset (Fin M)) (hT : T.card = K)
    (hsupport : ∀ z, nonzeroSupport ((representationToEuclidean M).symm (D z)) ⊆ T)
    (c : ℝ) (hc : 0 < c) (hlower : ∀ z, c * ‖z‖ ≤ ‖D z‖) :
    LinearMap.range D.toLinearMap =
      (coordinateSpan T).map (representationToEuclidean M).toLinearMap := by
  classical
  have hDinj : Function.Injective D := by
    intro z w hzw
    have h := hlower (z - w)
    rw [map_sub, hzw, sub_self, norm_zero] at h
    have hn : ‖z - w‖ = 0 := by nlinarith [norm_nonneg (z - w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hDdim : Module.finrank ℝ (LinearMap.range D.toLinearMap) = K := by
    rw [LinearMap.finrank_range_of_inj hDinj]
    simp
  have hTdim : Module.finrank ℝ (coordinateSpan T) = T.card := by
    have hli := (Pi.linearIndependent_single_one (Fin M) ℝ).comp
      (fun i : {i // i ∈ T} => i.val) Subtype.val_injective
    simpa only [coordinateSpan, Fintype.card_coe] using finrank_span_eq_card hli
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨z, rfl⟩
    exact ⟨(representationToEuclidean M).symm (D z),
      mem_coordinateSpan_of_nonzeroSupport_subset (hsupport z),
      (representationToEuclidean M).apply_symm_apply _⟩
  · rw [(representationToEuclidean M).toLinearEquiv.finrank_map_eq, hTdim, hT, hDdim]

/-- Every selected coordinate functional of a square supported coefficient
map has at least its lower margin in operator norm. -/
theorem coordinate_functional_norm_ge_of_supported_lower_bound {M K : ℕ}
    (D : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation M)
    (T : Finset (Fin M)) (hT : T.card = K)
    (hsupport : ∀ z, nonzeroSupport ((representationToEuclidean M).symm (D z)) ⊆ T)
    (c : ℝ) (hc : 0 < c) (hlower : ∀ z, c * ‖z‖ ≤ ‖D z‖)
    (j : Fin M) (hj : j ∈ T) :
    c ≤ ‖(PiLp.proj 2 (fun _ : Fin M => ℝ) j).comp D‖ := by
  let ej := representationToEuclidean M (Pi.single j 1 : FeatureVector M)
  have hej : ej ∈ LinearMap.range D.toLinearMap := by
    rw [range_eq_euclidean_coordinate_span_of_lower_bound D T hT hsupport c hc hlower]
    exact ⟨Pi.single j 1, canonicalVector_mem_coordinateSpan T hj, rfl⟩
  obtain ⟨z, hz⟩ := hej
  change D z = ej at hz
  have hejnorm : ‖ej‖ = 1 := by
    change ‖PiLp.single (β := fun _ : Fin M => ℝ) 2 j (1 : ℝ)‖ = 1
    simp only [PiLp.norm_single, norm_one]
  have hzpos : 0 < ‖z‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    have h := congrArg norm hz
    rw [hzero, map_zero, norm_zero, hejnorm] at h
    norm_num at h
  have hDz := hlower z
  rw [hz, hejnorm] at hDz
  let row := (PiLp.proj 2 (fun _ : Fin M => ℝ) j).comp D
  have hrowz : row z = 1 := by
    change (D z) j = 1
    rw [hz]
    simp only [ej, representationToEuclidean, PiLp.continuousLinearEquiv_symm_apply,
      Pi.single_eq_same]
  have hrowbound := row.le_opNorm z
  rw [hrowz, norm_one] at hrowbound
  by_contra hn
  have hstrict := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hzpos
  change ‖row‖ * ‖z‖ < c * ‖z‖ at hstrict
  linarith

/-- Sparse stability compares any actual `K`-sparse code with the projected
linear code by the sum of actual reconstruction error and projection error. -/
theorem actual_code_distance_le_projected_residuals {d M K : ℕ}
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (D : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation M)
    (hT : T.card ≤ K)
    (hsupport : ∀ z, nonzeroSupport ((representationToEuclidean M).symm (D z)) ⊆ T)
    (hD : ∀ z, representationToEuclidean d
      (B.mulVec ((representationToEuclidean M).symm (D z))) =
        (euclideanColumnSpan B T).starProjection (F z))
    (γ : ℝ) (hstable : SparseLowerStable B γ (2 * K))
    (δ : ℝ) (hgap : ‖(LinearMap.range F.toLinearMap).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ)
    (z : EuclideanRepresentation K) (u : FeatureVector M)
    (hu : (nonzeroSupport u).card ≤ K) :
    γ * ‖representationToEuclidean M u - D z‖ ≤
      ‖F z - representationToEuclidean d (B.mulVec u)‖ + δ * ‖F z‖ := by
  have hbound := hstable.code_distance_le_residuals u
    ((representationToEuclidean M).symm (D z)) ((representationToEuclidean d).symm (F z))
    hu ((Finset.card_le_card (hsupport z)).trans hT)
  simp only [map_sub, (representationToEuclidean M).apply_symm_apply,
    (representationToEuclidean d).apply_symm_apply] at hbound
  rw [norm_sub_rev (representationToEuclidean d (B.mulVec u)) (F z)] at hbound
  exact hbound.trans (add_le_add le_rfl
    (projected_coefficient_residual_le F B T D hD δ hgap z))

/-- A real coefficient functional with positive norm lower bound controls
a unit coefficient direction. This converts row norm bounds into the form
used by small-slab estimates. -/
theorem exists_unit_direction_of_functional_norm_lower_bound {K : ℕ}
    (L : EuclideanRepresentation K →L[ℝ] ℝ) (c : ℝ)
    (hc : 0 < c) (hL : c ≤ ‖L‖) :
    ∃ v : EuclideanRepresentation K, ‖v‖ = 1 ∧
      ∀ z, c * |inner ℝ v z| ≤ |L z| := by
  let f := (InnerProductSpace.toDual ℝ (EuclideanRepresentation K)).symm L
  have hfnorm : ‖f‖ = ‖L‖ :=
    (InnerProductSpace.toDual ℝ (EuclideanRepresentation K)).symm.norm_map L
  have hfpos : 0 < ‖f‖ := by rw [hfnorm]; exact hc.trans_le hL
  let v := ‖f‖⁻¹ • f
  have hfv : ‖f‖ • v = f := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hfpos.ne', one_smul]
  refine ⟨v, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hfpos)]
    exact inv_mul_cancel₀ hfpos.ne'
  · intro z
    have hvalue : inner ℝ f z = L z := InnerProductSpace.toDual_symm_apply
    calc
      c * |inner ℝ v z| ≤ ‖f‖ * |inner ℝ v z| :=
        mul_le_mul_of_nonneg_right (hfnorm ▸ hL) (abs_nonneg _)
      _ = |inner ℝ f z| := by
        conv_rhs => rw [← hfv, real_inner_smul_left, abs_mul, abs_of_pos hfpos]
      _ = |L z| := congrArg abs hvalue

/-- A close stable `K`-column span has a linear projected code with lower
margin `a/(2K)`, and every selected row has this same operator-norm lower
bound. The construction assumes no sign restriction on codes. -/
theorem exists_projected_coefficient_map_with_row_bounds {d M K : ℕ}
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (a b γ δ : ℝ) (hK : 0 < K) (ha : 0 < a) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hT : T.card = K) (hstable : SparseLowerStable B γ (2 * K))
    (hunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hlower : ∀ z, a * ‖z‖ ≤ ‖F z‖) (hupper : ∀ z, ‖F z‖ ≤ b * ‖z‖)
    (hsmall : δ * b ≤ a / 2)
    (hgap : ‖(LinearMap.range F.toLinearMap).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ) :
    ∃ D : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation M,
      (∀ z, nonzeroSupport ((representationToEuclidean M).symm (D z)) ⊆ T) ∧
      (∀ z, representationToEuclidean d
        (B.mulVec ((representationToEuclidean M).symm (D z))) =
          (euclideanColumnSpan B T).starProjection (F z)) ∧
      (∀ z, ‖F z - representationToEuclidean d
        (B.mulVec ((representationToEuclidean M).symm (D z)))‖ ≤ δ * ‖F z‖) ∧
      (∀ z, (a / (2 * (K : ℝ))) * ‖z‖ ≤ ‖D z‖) ∧
      (∀ j ∈ T, a / (2 * (K : ℝ)) ≤
        ‖(PiLp.proj 2 (fun _ : Fin M => ℝ) j).comp D‖) ∧
      ∀ z u, (nonzeroSupport u).card ≤ K →
        γ * ‖representationToEuclidean M u - D z‖ ≤
          ‖F z - representationToEuclidean d (B.mulVec u)‖ + δ * ‖F z‖ := by
  obtain ⟨D, hsupport, hD⟩ := exists_projected_support_coefficient_map F B T γ hγ hstable hT.le
  have hDlower := projected_coefficient_norm_lower_bound F B T D hK hT.le
    hsupport hD hunit a b δ hδ hlower hupper hsmall hgap
  have hc : 0 < a / (2 * (K : ℝ)) := by positivity
  refine ⟨D, hsupport, hD, projected_coefficient_residual_le F B T D hD δ hgap,
    hDlower, ?_, ?_⟩
  · exact coordinate_functional_norm_ge_of_supported_lower_bound
      D T hT hsupport _ hc hDlower
  · exact actual_code_distance_le_projected_residuals F B T D hT.le hsupport hD γ hstable δ hgap

end PKG26AtomicFeatures
