import PKG26AtomicFeatures.SparseCodeGeometry
import PKG26AtomicFeatures.OvercompleteIdentifiability
import PKG26AtomicFeatures.StableSupportIntersections

/-!
# Source support coordinates

Selecting distinct source columns preserves the Euclidean coefficient norm,
the sparse lower margin, and a dimension-only upper synthesis bound. These
bridges instantiate the incidence theorem from the paper's actual matrix.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators

/-- Insert a coefficient vector into distinct ambient coordinates. -/
noncomputable def insertSupportCode {K M : ℕ} (e : Fin K ↪ Fin M)
    (z : FeatureVector K) : FeatureVector M := embedSourceCode e (fun _ => 1) z

@[simp] theorem insertSupportCode_apply {K M : ℕ} (e : Fin K ↪ Fin M)
    (z : FeatureVector K) (i : Fin K) : insertSupportCode e z (e i) = z i := by
  simp [insertSupportCode]

theorem insertSupportCode_support_subset {K M : ℕ} (e : Fin K ↪ Fin M)
    (z : FeatureVector K) :
    nonzeroSupport (insertSupportCode e z) ⊆ Finset.univ.image e := by
  exact (nonzeroSupport_embedSourceCode_subset e (fun _ => 1) z).trans
    (Finset.image_mono e (Finset.subset_univ _))

theorem insertSupportCode_sparse {K M : ℕ} (e : Fin K ↪ Fin M)
    (z : FeatureVector K) : (nonzeroSupport (insertSupportCode e z)).card ≤ K := by
  calc
    _ ≤ (Finset.univ.image e).card := Finset.card_le_card (insertSupportCode_support_subset e z)
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = K := by simp

theorem insertSupportCode_norm {K M : ℕ} (e : Fin K ↪ Fin M)
    (z : FeatureVector K) :
    ‖representationToEuclidean M (insertSupportCode e z)‖ =
      ‖representationToEuclidean K z‖ := by
  classical
  have hsq : ‖representationToEuclidean M (insertSupportCode e z)‖ ^ 2 =
      ‖representationToEuclidean K z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    change (∑ j : Fin M, (insertSupportCode e z j) ^ 2) = ∑ i : Fin K, (z i) ^ 2
    calc
      _ = ∑ j ∈ Finset.univ.image e, (insertSupportCode e z j) ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        have hz : insertSupportCode e z j = 0 := by
          by_contra hn
          exact hj (insertSupportCode_support_subset e z (mem_nonzeroSupport_iff _ _ |>.mpr hn))
        simp [hz]
      _ = ∑ i : Fin K, (insertSupportCode e z (e i)) ^ 2 := by
        rw [Finset.sum_image]
        intro i _ j _ hij
        exact e.injective hij
      _ = _ := by simp
  nlinarith [norm_nonneg (representationToEuclidean M (insertSupportCode e z)),
    norm_nonneg (representationToEuclidean K z)]

/-- A source dictionary restricted to distinct selected columns, as a map
between genuine Euclidean spaces. -/
noncomputable def selectedSourceSynthesis {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (e : Fin K ↪ Fin M) :
    EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d :=
  ((representationToEuclidean d).toLinearMap.comp
    (((A.submatrix id e).mulVecLin).comp
      (representationToEuclidean K).symm.toLinearMap)).toContinuousLinearMap

theorem selectedSourceSynthesis_apply {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (e : Fin K ↪ Fin M)
    (z : EuclideanRepresentation K) :
    selectedSourceSynthesis A e z = representationToEuclidean d
      (A.mulVec (insertSupportCode e ((representationToEuclidean K).symm z))) := by
  have h := mulVec_embedSourceCode (A.submatrix id e) A e (fun _ => 1)
    (fun _ => by rw [one_smul]; rfl)
    ((representationToEuclidean K).symm z)
  exact congrArg (representationToEuclidean d) h.symm

/-- Sparse stability of the full dictionary supplies the lower bound on
every selected source support. -/
theorem selectedSourceSynthesis_lower {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (e : Fin K ↪ Fin M) (γ : ℝ)
    (hA : SparseLowerStable A γ (2 * K)) :
    ∀ z, γ * ‖z‖ ≤ ‖selectedSourceSynthesis A e z‖ := by
  intro z
  have h := hA (insertSupportCode e ((representationToEuclidean K).symm z))
    ((insertSupportCode_sparse e _).trans (by omega))
  rw [insertSupportCode_norm, (representationToEuclidean K).apply_symm_apply] at h
  rwa [selectedSourceSynthesis_apply]

/-- Unit upper column bounds give upper constant `K`, independent of
ambient dimension or total source width. -/
theorem selectedSourceSynthesis_upper {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (e : Fin K ↪ Fin M)
    (hA : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1) :
    ∀ z, ‖selectedSourceSynthesis A e z‖ ≤ (K : ℝ) * ‖z‖ := by
  intro z
  change ‖representationToEuclidean d ((A.submatrix id e).mulVec
    ((representationToEuclidean K).symm z))‖ ≤ _
  calc
    _ ≤ ∑ i ∈ nonzeroSupport ((representationToEuclidean K).symm z),
        |((representationToEuclidean K).symm z) i| :=
      euclidean_mulVec_norm_le_sum_abs (A.submatrix id e) (fun j => hA (e j)) _
    _ ≤ ∑ _i ∈ nonzeroSupport ((representationToEuclidean K).symm z), ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact PiLp.norm_apply_le z i
    _ = ((nonzeroSupport ((representationToEuclidean K).symm z)).card : ℝ) * ‖z‖ := by simp
    _ ≤ (K : ℝ) * ‖z‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact_mod_cast (show (nonzeroSupport ((representationToEuclidean K).symm z)).card ≤ K by
        simpa only [Fintype.card_fin] using
          Finset.card_le_univ (nonzeroSupport ((representationToEuclidean K).symm z)))

/-- Reading the selected coordinates and reinserting them recovers any
ambient code supported on those coordinates. -/
theorem insertSupportCode_restrict {K M : ℕ} (e : Fin K ↪ Fin M)
    (z : FeatureVector M) (hz : nonzeroSupport z ⊆ Finset.univ.image e) :
    insertSupportCode e (fun i => z (e i)) = z := by
  classical
  ext j
  by_cases hj : j ∈ Finset.univ.image e
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact insertSupportCode_apply e _ i
  · have hzj : z j = 0 := by
      by_contra hn
      exact hj (hz ((mem_nonzeroSupport_iff z j).mpr hn))
    have hinsert : insertSupportCode e (fun i => z (e i)) j = 0 := by
      by_contra hn
      exact hj (insertSupportCode_support_subset e _ ((mem_nonzeroSupport_iff _ _).mpr hn))
    exact hinsert.trans hzj.symm

/-- The selected map has exactly the source column span associated with
its support. This bridge uses no independence assumption. -/
theorem range_selectedSourceSynthesis {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (e : Fin K ↪ Fin M) :
    LinearMap.range (selectedSourceSynthesis A e).toLinearMap =
      euclideanColumnSpan A (Finset.univ.image e) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    apply (mem_euclideanColumnSpan_iff_exists_code A _ _).mpr
    refine ⟨insertSupportCode e ((representationToEuclidean K).symm z),
      insertSupportCode_support_subset e _, ?_⟩
    exact (selectedSourceSynthesis_apply A e z).symm
  · intro hx
    obtain ⟨z, hz, hzx⟩ := (mem_euclideanColumnSpan_iff_exists_code A _ x).mp hx
    refine ⟨representationToEuclidean K (fun i => z (e i)), ?_⟩
    change selectedSourceSynthesis A e (representationToEuclidean K (fun i => z (e i))) = x
    rw [selectedSourceSynthesis_apply, (representationToEuclidean K).symm_apply_apply,
      insertSupportCode_restrict e z hz]
    exact hzx

end PKG26AtomicFeatures
