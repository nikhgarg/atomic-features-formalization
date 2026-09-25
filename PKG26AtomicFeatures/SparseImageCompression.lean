import PKG26AtomicFeatures.FiniteDimensionalCovering
import PKG26AtomicFeatures.SparseCodeGeometry

namespace PKG26AtomicFeatures

/-- Multiplication by a scalar cannot introduce an active coordinate. -/
theorem nonzeroSupport_smul_subset {M : ℕ} (t : ℝ) (u : FeatureVector M) :
    nonzeroSupport (t • u) ⊆ nonzeroSupport u := by
  intro j hj
  simp only [mem_nonzeroSupport_iff, Pi.smul_apply, smul_eq_mul] at hj ⊢
  exact (mul_ne_zero_iff.mp hj).2

/-- Subtracting the coefficient on a coordinate removes exactly that
coordinate from the nonzero support. -/
theorem nonzeroSupport_erase_coordinate {M : ℕ} (u : FeatureVector M) (i : Fin M) :
    nonzeroSupport (u - u i • (Pi.single i 1 : FeatureVector M)) =
      (nonzeroSupport u).erase i := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- Removing the coefficient of an atom leaves synthesis unchanged after
orthogonal projection perpendicular to that atom. -/
theorem projected_synthesis_erase_coordinate {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (u : FeatureVector M) (i : Fin M) :
    (ℝ ∙ representationToEuclidean d (B.col i))ᗮ.starProjection
        (representationToEuclidean d
          (B.mulVec (u - u i • (Pi.single i 1 : FeatureVector M)))) =
      (ℝ ∙ representationToEuclidean d (B.col i))ᗮ.starProjection
        (representationToEuclidean d (B.mulVec u)) := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one,
    map_sub, map_smul, Submodule.starProjection_orthogonalComplement_singleton_eq_zero,
    smul_zero, sub_zero]

/-- An approximation after projection perpendicular to one atom lifts to
an approximation using that atom and the original support. The added
coefficient exactly recovers the parallel component of the residual. -/
theorem exists_lift_projected_sparse_approximation {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (i : Fin M)
    (x : EuclideanRepresentation d) (u : FeatureVector M) (T : Finset (Fin M))
    (hu : nonzeroSupport u ⊆ T) (η : ℝ)
    (herr : ‖(ℝ ∙ representationToEuclidean d (B.col i))ᗮ.starProjection x -
      (ℝ ∙ representationToEuclidean d (B.col i))ᗮ.starProjection
        (representationToEuclidean d (B.mulVec u))‖ ≤ η) :
    ∃ v : FeatureVector M, nonzeroSupport v ⊆ insert i T ∧
      ‖x - representationToEuclidean d (B.mulVec v)‖ ≤ η := by
  classical
  let W : Submodule ℝ (EuclideanRepresentation d) :=
    ℝ ∙ representationToEuclidean d (B.col i)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (W.starProjection_apply_mem (x - representationToEuclidean d (B.mulVec u)))
  refine ⟨u + t • (Pi.single i 1 : FeatureVector M), ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · exact Finset.mem_insert.mpr (Or.inl hji)
    · apply Finset.mem_insert_of_mem
      apply hu
      simpa [Pi.single_eq_of_ne hji] using hj
  · have heq : x - representationToEuclidean d
          (B.mulVec (u + t • (Pi.single i 1 : FeatureVector M))) =
        Wᗮ.starProjection x - Wᗮ.starProjection
          (representationToEuclidean d (B.mulVec u)) := by
      rw [← map_sub, Submodule.starProjection_orthogonal_val, ← ht]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one,
        map_add, map_smul]
      abel
    rw [heq]
    exact herr

/-- Erasing an active coordinate and normalizing a nontrivial perpendicular
projection reduces sparsity by one and changes `c * η^(k+1)` error into at
most `c * η^k` error. -/
theorem exists_normalized_projected_sparse_code {d M k : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (allowed : Finset (Fin M))
    (i : Fin M) (x : EuclideanRepresentation d) (u : FeatureVector M)
    (hu : nonzeroSupport u ⊆ allowed) (hucard : (nonzeroSupport u).card ≤ k + 1)
    (hi : i ∈ nonzeroSupport u) (c η : ℝ) (hc : 0 ≤ c) (hη : 0 < η)
    (herr : ‖x - representationToEuclidean d (B.mulVec u)‖ ≤ c * η ^ (k + 1))
    (hr : η < ‖(ℝ ∙ representationToEuclidean d (B.col i))ᗮ.starProjection x‖) :
    ∃ v : FeatureVector M, nonzeroSupport v ⊆ allowed.erase i ∧
      (nonzeroSupport v).card ≤ k ∧
      ‖‖(ℝ ∙ representationToEuclidean d (B.col i))ᗮ.starProjection x‖⁻¹ •
          (ℝ ∙ representationToEuclidean d (B.col i))ᗮ.starProjection x -
        representationToEuclidean d
          ((postcomposeEuclideanDictionary
            (ℝ ∙ representationToEuclidean d (B.col i))ᗮ.starProjection B).mulVec v)‖
        ≤ c * η ^ k := by
  classical
  let Q := (ℝ ∙ representationToEuclidean d (B.col i))ᗮ.starProjection
  let r := ‖Q x‖
  let erased := u - u i • (Pi.single i 1 : FeatureVector M)
  have hrpos : 0 < r := hη.trans hr
  have hsupport : nonzeroSupport (r⁻¹ • erased) ⊆ (nonzeroSupport u).erase i :=
    (nonzeroSupport_smul_subset _ _).trans (by rw [nonzeroSupport_erase_coordinate])
  refine ⟨r⁻¹ • erased, hsupport.trans (Finset.erase_subset_erase i hu), ?_, ?_⟩
  · have hcard := Finset.card_le_card hsupport
    rw [Finset.card_erase_of_mem hi] at hcard
    omega
  · have hprojected : ‖Q x - Q (representationToEuclidean d (B.mulVec u))‖ ≤
        c * η ^ (k + 1) := by
      rw [← map_sub]
      exact ((ℝ ∙ representationToEuclidean d (B.col i))ᗮ.norm_starProjection_apply_le _).trans herr
    have heq :
        ‖r⁻¹ • Q x - representationToEuclidean d
          ((postcomposeEuclideanDictionary Q B).mulVec (r⁻¹ • erased))‖ =
        r⁻¹ * ‖Q x - Q (representationToEuclidean d (B.mulVec u))‖ := by
      rw [postcomposeEuclideanDictionary_mulVec, Matrix.mulVec_smul, map_smul, map_smul]
      change ‖r⁻¹ • Q x - r⁻¹ • Q
        (representationToEuclidean d
          (B.mulVec (u - u i • (Pi.single i 1 : FeatureVector M))))‖ = _
      rw [projected_synthesis_erase_coordinate, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrpos)]
    change ‖r⁻¹ • Q x - representationToEuclidean d
      ((postcomposeEuclideanDictionary Q B).mulVec (r⁻¹ • erased))‖ ≤ _
    rw [heq]
    calc
      _ ≤ r⁻¹ * (c * η ^ (k + 1)) :=
        mul_le_mul_of_nonneg_left hprojected (inv_nonneg.mpr hrpos.le)
      _ ≤ c * η ^ k := by
        rw [← div_eq_inv_mul, div_le_iff₀ hrpos, pow_succ]
        have hnonneg : 0 ≤ c * η ^ k := mul_nonneg hc (pow_nonneg hη.le k)
        nlinarith

/-- A substantial coefficient cannot vanish between sufficiently close
approximate sparse reconstructions. -/
theorem SparseLowerStableOn.large_coordinate_persists {d M k K : ℕ}
    {B : Matrix (Fin d) (Fin M) ℝ} {allowed : Finset (Fin M)} {γ : ℝ}
    (hstable : SparseLowerStableOn B γ (2 * k) allowed)
    (hγ : 0 < γ) (hK : 0 < K)
    (u v : FeatureVector M) (x y : EuclideanRepresentation d) (i : Fin M)
    (hu : nonzeroSupport u ⊆ allowed) (hv : nonzeroSupport v ⊆ allowed)
    (hucard : (nonzeroSupport u).card ≤ k) (hvcard : (nonzeroSupport v).card ≤ k)
    (hlarge : 1 / (2 * (K : ℝ)) ≤ |u i|)
    (c r : ℝ) (hsmall : 2 * c + r ≤ γ * (1 / (4 * (K : ℝ))))
    (hxu : ‖x - representationToEuclidean d (B.mulVec u)‖ ≤ c)
    (hyv : ‖y - representationToEuclidean d (B.mulVec v)‖ ≤ c)
    (hxy : ‖x - y‖ ≤ r) : i ∈ nonzeroSupport v := by
  have hdist := hstable.code_distance_le_three_errors u v x y hu hv hucard hvcard
  rw [norm_sub_rev (representationToEuclidean d (B.mulVec u)) x] at hdist
  have hnorm : ‖representationToEuclidean M (u - v)‖ ≤ 1 / (4 * (K : ℝ)) := by
    apply (mul_le_mul_iff_right₀ hγ).mp
    linarith
  have hcoordinate := (abs_coordinate_sub_le_euclidean_norm u v i).trans hnorm
  apply (mem_nonzeroSupport_iff v i).mpr
  intro hz
  rw [hz, sub_zero] at hcoordinate
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hgap : 1 / (4 * (K : ℝ)) < 1 / (2 * (K : ℝ)) := by
    apply one_div_lt_one_div_of_lt <;> linarith
  exact (not_le_of_gt hgap) (hlarge.trans hcoordinate)

private theorem sparse_image_compression_induction
    (K D P : ℕ) (γ c radius : ℝ) (hK : 0 < K) (hγ : 0 < γ)
    (hc : 0 ≤ c) (hcsmall : c ≤ 1 / 4)
    (hsmall : 2 * c + radius ≤ γ * (1 / (4 * (K : ℝ))))
    (hnet : ∀ (d : ℕ) (U : Submodule ℝ (EuclideanRepresentation d)),
      Module.finrank ℝ U ≤ D → ∀ E : Set U,
      E ⊆ Metric.closedBall 0 1 →
      ∃ F : Finset U, (↑F : Set U) ⊆ E ∧ F.card ≤ P ∧
        ∀ x ∈ E, ∃ y ∈ F, dist x y < radius)
    (k : ℕ) (hk : k ≤ K) :
    ∀ (d M : ℕ) (B : Matrix (Fin d) (Fin M) ℝ) (allowed : Finset (Fin M))
      (U : Submodule ℝ (EuclideanRepresentation d)) (η : ℝ),
      (∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1) →
      SparseLowerStableOn B γ (2 * k) allowed →
      Module.finrank ℝ U ≤ D → 0 < η → η ≤ 1 →
      ∃ family : Finset (Finset (Fin M)), ∅ ∈ family ∧
        family.card ≤ (P + 1) ^ k ∧
        (∀ T ∈ family, T ⊆ allowed ∧ T.card ≤ k) ∧
        ∀ (x : EuclideanRepresentation d), x ∈ U → ‖x‖ = 1 →
          ∀ u : FeatureVector M, nonzeroSupport u ⊆ allowed →
            (nonzeroSupport u).card ≤ k →
            ‖x - representationToEuclidean d (B.mulVec u)‖ ≤ c * η ^ k →
            ∃ T ∈ family, ∃ v : FeatureVector M,
              nonzeroSupport v ⊆ T ∧
              ‖x - representationToEuclidean d (B.mulVec v)‖ ≤ η := by
  classical
  induction k with
  | zero =>
      intro d M B allowed U η hunit hstable hdim hη hηone
      refine ⟨{∅}, by simp, by simp, ?_, ?_⟩
      · intro T hT
        have hT0 : T = ∅ := Finset.mem_singleton.mp hT
        subst T
        simp
      · intro x hx hxnorm u hu hucard herr
        have husupport : nonzeroSupport u = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hucard)
        have huzero : u = 0 := by
          ext j
          have hj : j ∉ nonzeroSupport u := by rw [husupport]; simp
          simpa using hj
        simp only [huzero, Matrix.mulVec_zero, map_zero, sub_zero, hxnorm, pow_zero,
          mul_one] at herr
        linarith
  | succ k ih =>
      intro d M B allowed U η hunit hstable hdim hη hηone
      have hkK : k ≤ K := Nat.le_trans (Nat.le_succ k) hk
      have herror : c * η ^ (k + 1) ≤ c := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hη.le hηone) hc
      let E : Set U := {x | ‖(x : EuclideanRepresentation d)‖ = 1 ∧
        ∃ u : FeatureVector M, nonzeroSupport u ⊆ allowed ∧
          (nonzeroSupport u).card ≤ k + 1 ∧
          ‖(x : EuclideanRepresentation d) -
            representationToEuclidean d (B.mulVec u)‖ ≤ c * η ^ (k + 1)}
      have hE : E ⊆ Metric.closedBall 0 1 := by
        intro x hx
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hx.1.le
      obtain ⟨centers, hcenters, hcentercard, hcover⟩ := hnet d U hdim E hE
      have hdata (z : centers) : ∃ (u : FeatureVector M) (i : Fin M),
          nonzeroSupport u ⊆ allowed ∧ (nonzeroSupport u).card ≤ k + 1 ∧
          ‖(z.1 : EuclideanRepresentation d) -
            representationToEuclidean d (B.mulVec u)‖ ≤ c * η ^ (k + 1) ∧
          i ∈ nonzeroSupport u ∧ 1 / (2 * (K : ℝ)) ≤ |u i| := by
        obtain ⟨hznorm, u, hu, hucard, herr⟩ := hcenters z.2
        obtain ⟨i, hi, hlarge⟩ := exists_large_sparse_coordinate B hunit u z.1 hK
          (hucard.trans hk) hznorm (herr.trans (herror.trans hcsmall))
        exact ⟨u, i, hu, hucard, herr, hi, hlarge⟩
      choose code atom hcodeallowed hcodecard hcodeerr hatom hlarge using hdata
      let Q (z : centers) :=
        (ℝ ∙ representationToEuclidean d (B.col (atom z)))ᗮ.starProjection
      let projectedB (z : centers) := postcomposeEuclideanDictionary (Q z) B
      let projectedU (z : centers) := U.map (Q z).toLinearMap
      have hchild (z : centers) :
          ∃ family : Finset (Finset (Fin M)), ∅ ∈ family ∧
            family.card ≤ (P + 1) ^ k ∧
            (∀ T ∈ family, T ⊆ allowed.erase (atom z) ∧ T.card ≤ k) ∧
            ∀ (x : EuclideanRepresentation d), x ∈ projectedU z → ‖x‖ = 1 →
              ∀ u : FeatureVector M, nonzeroSupport u ⊆ allowed.erase (atom z) →
                (nonzeroSupport u).card ≤ k →
                ‖x - representationToEuclidean d ((projectedB z).mulVec u)‖ ≤ c * η ^ k →
                ∃ T ∈ family, ∃ v : FeatureVector M, nonzeroSupport v ⊆ T ∧
                  ‖x - representationToEuclidean d ((projectedB z).mulVec v)‖ ≤ η := by
        apply ih hkK d M (projectedB z) (allowed.erase (atom z)) (projectedU z) η
        · exact projected_dictionary_column_norm_le B _ hunit
        · simpa only [Nat.add_sub_cancel] using
            hstable.project_erase hγ.le (Nat.succ_pos k) (atom z)
              (hcodeallowed z (hatom z))
        · exact (Submodule.finrank_map_le (Q z).toLinearMap U).trans hdim
        · exact hη
        · exact hηone
      choose child hempty hchildcard hchildgood hchildcover using hchild
      let family := insert (∅ : Finset (Fin M))
        (centers.attach.biUnion fun z => (child z).image (insert (atom z)))
      have hinsert (z : centers) (T : Finset (Fin M)) (hT : T ∈ child z) :
          insert (atom z) T ∈ family := by
        apply Finset.mem_insert_of_mem
        exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_attach _ _,
          Finset.mem_image.mpr ⟨T, hT, rfl⟩⟩
      refine ⟨family, Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
      · calc
          family.card ≤ (centers.attach.biUnion
              fun z => (child z).image (insert (atom z))).card + 1 := Finset.card_insert_le _ _
          _ ≤ (∑ z ∈ centers.attach, ((child z).image (insert (atom z))).card) + 1 :=
            Nat.add_le_add_right (Finset.card_biUnion_le) 1
          _ ≤ (∑ _z ∈ centers.attach, (P + 1) ^ k) + 1 := by
            apply Nat.add_le_add_right
            exact Finset.sum_le_sum fun z _ => Finset.card_image_le.trans (hchildcard z)
          _ = centers.card * (P + 1) ^ k + 1 := by simp
          _ ≤ P * (P + 1) ^ k + 1 := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hcentercard) _
          _ ≤ (P + 1) ^ (k + 1) := by
            have hpow : 1 ≤ (P + 1) ^ k := Nat.one_le_pow k _ (by omega)
            rw [pow_succ]
            nlinarith
      · intro T hT
        rcases Finset.mem_insert.mp hT with rfl | hT
        · simp
        · obtain ⟨z, _, hmem⟩ := Finset.mem_biUnion.mp hT
          obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hmem
          refine ⟨Finset.insert_subset (hcodeallowed z (hatom z))
            ((hchildgood z R hR).1.trans (Finset.erase_subset _ _)), ?_⟩
          exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hchildgood z R hR).2 1)
      · intro x hx hxnorm u hu hucard herr
        have hxE : (⟨x, hx⟩ : U) ∈ E := ⟨hxnorm, u, hu, hucard, herr⟩
        obtain ⟨z, hz, hxz⟩ := hcover ⟨x, hx⟩ hxE
        let z' : centers := ⟨z, hz⟩
        have hnear : ‖(z : EuclideanRepresentation d) - x‖ ≤ radius := by
          have hd : ‖x - (z : EuclideanRepresentation d)‖ < radius := by
            simpa only [dist_eq_norm, Submodule.norm_coe] using hxz
          simpa only [norm_sub_rev] using hd.le
        have hactive : atom z' ∈ nonzeroSupport u :=
          hstable.large_coordinate_persists hγ hK (code z') u z x (atom z')
            (hcodeallowed z') hu (hcodecard z') hucard (hlarge z') c radius hsmall
            ((hcodeerr z').trans herror) (herr.trans herror) hnear
        by_cases hshort : ‖Q z' x‖ ≤ η
        · obtain ⟨v, hv, hvapprox⟩ := exists_lift_projected_sparse_approximation
            B (atom z') x 0 ∅ (by simp [nonzeroSupport]) η (by
              simpa only [Matrix.mulVec_zero, map_zero, sub_zero] using hshort)
          exact ⟨insert (atom z') ∅, hinsert z' ∅ (hempty z'), v, hv, hvapprox⟩
        · have hlong : η < ‖Q z' x‖ := lt_of_not_ge hshort
          let r := ‖Q z' x‖
          have hrpos : 0 < r := hη.trans hlong
          have hrone : r ≤ 1 := (Submodule.norm_starProjection_apply_le _ x).trans hxnorm.le
          let y := r⁻¹ • Q z' x
          have hyU : y ∈ projectedU z' :=
            (projectedU z').smul_mem _ (Submodule.mem_map_of_mem hx)
          have hynorm : ‖y‖ = 1 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrpos)]
            exact inv_mul_cancel₀ hrpos.ne'
          obtain ⟨v, hvallowed, hvcard, hverr⟩ := exists_normalized_projected_sparse_code
            B allowed (atom z') x u hu hucard hactive c η hc hη herr hlong
          obtain ⟨T, hT, w, hw, hwerr⟩ :=
            hchildcover z' y hyU hynorm v hvallowed hvcard hverr
          have hscaled : ‖Q z' x - Q z'
              (representationToEuclidean d (B.mulVec (r • w)))‖ ≤ η := by
            have hscale : r • y = Q z' x := by
              dsimp [y]
              rw [smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
            calc
              _ = ‖r • (y - representationToEuclidean d ((projectedB z').mulVec w))‖ := by
                rw [smul_sub, hscale, Matrix.mulVec_smul, map_smul, map_smul]
                rw [postcomposeEuclideanDictionary_mulVec]
              _ = r * ‖y - representationToEuclidean d ((projectedB z').mulVec w)‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
              _ ≤ r * η := mul_le_mul_of_nonneg_left hwerr hrpos.le
              _ ≤ η := by nlinarith
          obtain ⟨w', hw', hwapprox⟩ := exists_lift_projected_sparse_approximation
            B (atom z') x (r • w) T ((nonzeroSupport_smul_subset r w).trans hw) η hscaled
          exact ⟨insert (atom z') T, hinsert z' T hT, w', hw', hwapprox⟩

/-- For fixed sparsity, subspace dimension, and positive decoding margin,
finitely many learned supports uniformly cover the unit vectors of the
subspace that have sufficiently accurate sparse reconstructions.

The number of selected supports is independent of the dictionary width,
ambient dimension, subspace, and accuracy parameter. The empty support is
included. Reconstructions and approximations are expressed by actual codes. -/
theorem exists_uniform_sparse_image_compression
    (K D : ℕ) (γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) :
    ∃ N : ℕ, ∀ (d M : ℕ) (B : Matrix (Fin d) (Fin M) ℝ)
      (allowed : Finset (Fin M)) (U : Submodule ℝ (EuclideanRepresentation d)) (η : ℝ),
      (∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1) →
      SparseLowerStableOn B γ (2 * K) allowed →
      Module.finrank ℝ U ≤ D → 0 < η → η ≤ 1 →
      ∃ family : Finset (Finset (Fin M)), ∅ ∈ family ∧ family.card ≤ N ∧
        (∀ T ∈ family, T ⊆ allowed ∧ T.card ≤ K) ∧
        ∀ (x : EuclideanRepresentation d), x ∈ U → ‖x‖ = 1 →
          ∀ u : FeatureVector M, nonzeroSupport u ⊆ allowed →
            (nonzeroSupport u).card ≤ K →
            ‖x - representationToEuclidean d (B.mulVec u)‖ ≤
              (γ / (16 * (K : ℝ))) * η ^ K →
            ∃ T ∈ family, ∃ v : FeatureVector M, nonzeroSupport v ⊆ T ∧
              ‖x - representationToEuclidean d (B.mulVec v)‖ ≤ η := by
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hKone : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  obtain ⟨P, hnet⟩ := exists_uniform_subspace_internal_net_bound D
    (γ / (8 * (K : ℝ))) (by positivity)
  refine ⟨(P + 1) ^ K, ?_⟩
  apply sparse_image_compression_induction K D P γ (γ / (16 * (K : ℝ)))
    (γ / (8 * (K : ℝ))) hK hγ (by positivity) ?_ ?_ hnet K le_rfl
  · apply (div_le_iff₀ (by positivity : 0 < 16 * (K : ℝ))).mpr
    nlinarith
  · have heq : 2 * (γ / (16 * (K : ℝ))) + γ / (8 * (K : ℝ)) =
        γ * (1 / (4 * (K : ℝ))) := by field_simp; ring
    exact heq.le

end PKG26AtomicFeatures
