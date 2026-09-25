import PKG26AtomicFeatures.SparseCodeGeometry
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Gram-preserving ambient compression

Finite-dimensional spectral decomposition and orthonormal completion allow
linear dictionary objectives supported on a source subspace to be maximized
inside that subspace without changing the dictionary Gram matrix.
-/

namespace PKG26AtomicFeatures

open Module InnerProductSpace
open scoped BigOperators

/-- An orthonormal partial family extends to an orthonormal frame whenever
the target dimension is at least the number of frame coordinates. -/
theorem exists_orthonormal_frame_extension
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {r : ℕ} (hr : r ≤ finrank ℝ F) (v : Fin r → F) (s : Set (Fin r))
    (hv : Orthonormal ℝ (s.restrict v)) :
    ∃ w : Fin r → F, Orthonormal ℝ w ∧ ∀ i ∈ s, w i = v i := by
  classical
  let e : Fin r ↪ Fin (finrank ℝ F) := ⟨Fin.castLE hr, Fin.castLE_injective hr⟩
  let v' : Fin (finrank ℝ F) → F := Function.extend e v (fun _ => 0)
  let s' : Set (Fin (finrank ℝ F)) := e '' s
  have he (i : Fin r) : v' (e i) = v i := e.injective.extend_apply v (fun _ => 0) i
  have hv' : Orthonormal ℝ (s'.restrict v') := by
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨i, hi, rfl⟩ := hj
      change ‖v' (e i)‖ = 1
      rw [he]
      exact hv.norm_eq_one ⟨i, hi⟩
    · rintro ⟨j, hj⟩ ⟨k, hk⟩ hjk
      obtain ⟨i, hi, rfl⟩ := hj
      obtain ⟨l, hl, rfl⟩ := hk
      change inner ℝ (v' (e i)) (v' (e l)) = 0
      rw [he, he]
      exact hv.inner_eq_zero (i := ⟨i, hi⟩) (j := ⟨l, hl⟩)
        (by intro h; apply hjk; exact Subtype.ext (congrArg e (congrArg Subtype.val h)))
  obtain ⟨b, hb⟩ := hv'.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨fun i => b (e i), b.orthonormal.comp e e.injective, ?_⟩
  intro i hi
  exact (hb (e i) ⟨i, hi, rfl⟩).trans (he i)

/-- Normalize the nonzero images of an eigenbasis of T* T. Their pairwise
orthogonality follows from the actual adjoint equation. -/
theorem orthonormal_normalized_singular_images
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →ₗ[ℝ] F) :
    let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
    Orthonormal ℝ ({i | T (b i) ≠ 0}.restrict fun i => NormedSpace.normalize (T (b i))) := by
  classical
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  change Orthonormal ℝ ({i | T (b i) ≠ 0}.restrict fun i => NormedSpace.normalize (T (b i)))
  constructor
  · intro i
    exact NormedSpace.norm_normalize i.2
  · intro i j hij
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have horth : inner ℝ (T (b i.1)) (T (b j.1)) = 0 := by
      rw [← T.adjoint_inner_right]
      change inner ℝ (b i.1) ((T.adjoint ∘ₗ T) (b j.1)) = 0
      rw [T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl j.1,
        real_inner_smul_right, b.inner_eq_zero hne, mul_zero]
    change inner ℝ (NormedSpace.normalize (T (b i.1)))
      (NormedSpace.normalize (T (b j.1))) = 0
    simp only [NormedSpace.normalize, real_inner_smul_left, real_inner_smul_right, horth,
      mul_zero]

/-- A rectangular linear map has an isometric frame whose pairing with its
singular images dominates every contraction. The maximizing frame is derived
from the map; no singular-vector or polar-factor witness is assumed. -/
theorem exists_linearIsometry_pairing_ge_contraction
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : finrank ℝ E ≤ finrank ℝ F) (T : E →ₗ[ℝ] F)
    (A : E →ₗ[ℝ] F) (hA : ∀ x, ‖A x‖ ≤ ‖x‖) :
    ∃ U : E →ₗᵢ[ℝ] F,
      let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
      (∑ i, inner ℝ (T (b i)) (A (b i))) ≤ ∑ i, inner ℝ (T (b i)) (U (b i)) := by
  classical
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  obtain ⟨w, hw, hwmatch⟩ := exists_orthonormal_frame_extension hdim
    (fun i => NormedSpace.normalize (T (b i))) {i | T (b i) ≠ 0}
    (orthonormal_normalized_singular_images T)
  let L := b.toBasis.constr ℝ w
  have hL (i) : L (b i) = w i := b.toBasis.constr_basis ℝ w i
  have hLortho : Orthonormal ℝ (L ∘ b.toBasis) := by
    simpa only [Function.comp_def, OrthonormalBasis.coe_toBasis, hL] using hw
  let U := L.isometryOfOrthonormal b.orthonormal hLortho
  refine ⟨U, ?_⟩
  change (∑ i, inner ℝ (T (b i)) (A (b i))) ≤ ∑ i, inner ℝ (T (b i)) (U (b i))
  apply Finset.sum_le_sum
  intro i _
  have hU : U (b i) = w i := hL i
  rw [hU]
  by_cases hi : T (b i) = 0
  · simp [hi]
  · rw [hwmatch i hi]
    have hbound : inner ℝ (T (b i)) (A (b i)) ≤ ‖T (b i)‖ := by
      apply (real_inner_le_norm _ _).trans
      have hAi : ‖A (b i)‖ ≤ 1 := (hA (b i)).trans_eq (b.norm_eq_one i)
      exact mul_le_of_le_one_right (norm_nonneg _) hAi
    have hnorm : ‖T (b i)‖ ≠ 0 := norm_ne_zero_iff.mpr hi
    simpa only [NormedSpace.normalize, real_inner_smul_right, real_inner_self_eq_norm_sq,
      pow_two, inv_mul_cancel_left₀ hnorm] using hbound

/-- Expanding a finite rank-one operator in an orthonormal basis gives
exactly the finite dictionary pairing, independent of the chosen basis. -/
theorem sum_inner_rankOne_operator_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis κ ℝ E) (v : ι → E) (c : ι → F) (A : E →ₗ[ℝ] F) :
    (∑ k, inner ℝ ((∑ j, (rankOne ℝ (c j) (v j)).toLinearMap) (b k)) (A (b k))) =
      ∑ j, inner ℝ (c j) (A (v j)) := by
  classical
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
    sum_inner, real_inner_smul_left]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ k, inner ℝ (v j) (b k) * inner ℝ (c j) (A (b k))) =
        inner ℝ (c j) (A (∑ k, inner ℝ (b k) (v j) • b k)) := by
      simp only [map_sum, map_smul, inner_sum, real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro k _
      rw [real_inner_comm (v j) (b k)]
    _ = _ := by rw [b.sum_repr']

/-- Every finite linear dictionary objective supported on a sufficiently
large subspace has a Gram-preserving compression into that subspace. The
original vectors may be linearly dependent or zero. -/
theorem exists_gram_preserving_subspace_compression
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]
    (S : Submodule ℝ E) (hdim : Fintype.card ι ≤ finrank ℝ S)
    (v c : ι → E) (hc : ∀ j, c j ∈ S) :
    ∃ w : ι → E,
      (∀ j, w j ∈ S) ∧
      (∀ i j, inner ℝ (w i) (w j) = inner ℝ (v i) (v j)) ∧
      (∑ j, inner ℝ (c j) (v j)) ≤ ∑ j, inner ℝ (c j) (w j) := by
  classical
  let V := Submodule.span ℝ (Set.range v)
  let vV : ι → V := fun j => ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩
  let cS : ι → S := fun j => ⟨c j, hc j⟩
  let T : V →ₗ[ℝ] S := ∑ j, (rankOne ℝ (cS j) (vV j)).toLinearMap
  let A : V →ₗ[ℝ] S := S.orthogonalProjection.toLinearMap.comp V.subtype
  have hA (x : V) : ‖A x‖ ≤ ‖x‖ := S.norm_orthogonalProjection_apply_le x
  have hdimV : finrank ℝ V ≤ finrank ℝ S := by
    letI := Fintype.ofFinite (Set.range v)
    have hcard : (Set.range v).toFinset.card ≤ Fintype.card ι := by
      simpa only [Set.toFinset_card] using Fintype.card_range_le v
    exact ((finrank_span_le_card (Set.range v)).trans hcard).trans hdim
  obtain ⟨U, hU⟩ := exists_linearIsometry_pairing_ge_contraction hdimV T A hA
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  change (∑ i, inner ℝ (T (b i)) (A (b i))) ≤ ∑ i, inner ℝ (T (b i)) (U (b i)) at hU
  have hleft := sum_inner_rankOne_operator_eq b vV cS A
  have hright := sum_inner_rankOne_operator_eq b vV cS U.toLinearMap
  change (∑ i, inner ℝ (T (b i)) (A (b i))) = _ at hleft
  change (∑ i, inner ℝ (T (b i)) (U (b i))) = _ at hright
  rw [hleft, hright] at hU
  refine ⟨fun j => (U (vV j) : E), fun j => (U (vV j)).2, ?_, ?_⟩
  · intro i j
    exact U.inner_map_map (vV i) (vV j)
  · have heq (j) : inner ℝ (cS j) (A (vV j)) = inner ℝ (c j) (v j) :=
      S.inner_orthogonalProjection_eq_of_mem_left (cS j) (v j)
    simp_rw [heq] at hU
    exact hU

/-- Equal column Gram matrices preserve the genuine Euclidean synthesis
norm for every coefficient vector, with no sparsity restriction. -/
theorem euclidean_synthesis_norm_eq_of_column_gram_eq {d m : ℕ}
    (B B' : Matrix (Fin d) (Fin m) ℝ)
    (hgram : ∀ i j,
      inner ℝ (representationToEuclidean d (B'.col i)) (representationToEuclidean d (B'.col j)) =
      inner ℝ (representationToEuclidean d (B.col i)) (representationToEuclidean d (B.col j)))
    (u : FeatureVector m) :
    ‖representationToEuclidean d (B'.mulVec u)‖ = ‖representationToEuclidean d (B.mulVec u)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [← real_inner_self_eq_norm_sq, euclidean_mulVec_eq_sum,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hgram]

/-- Matrix form of finite ambient compression: the source-supported linear
objective improves while the complete Gram matrix and all synthesis norms
are preserved. This endpoint does not assume dictionary independence. -/
theorem exists_gram_preserving_dictionary_compression {d m : ℕ}
    (S : Submodule ℝ (EuclideanRepresentation d)) (hdim : m ≤ finrank ℝ S)
    (B : Matrix (Fin d) (Fin m) ℝ) (c : Fin m → EuclideanRepresentation d)
    (hc : ∀ j, c j ∈ S) :
    ∃ B' : Matrix (Fin d) (Fin m) ℝ,
      (∀ j, representationToEuclidean d (B'.col j) ∈ S) ∧
      (∀ i j,
        inner ℝ (representationToEuclidean d (B'.col i)) (representationToEuclidean d (B'.col j)) =
        inner ℝ (representationToEuclidean d (B.col i)) (representationToEuclidean d (B.col j))) ∧
      (∀ u : FeatureVector m,
        ‖representationToEuclidean d (B'.mulVec u)‖ = ‖representationToEuclidean d (B.mulVec u)‖) ∧
      (∑ j, inner ℝ (c j) (representationToEuclidean d (B.col j))) ≤
        ∑ j, inner ℝ (c j) (representationToEuclidean d (B'.col j)) := by
  obtain ⟨w, hwS, hwgram, hwobj⟩ := exists_gram_preserving_subspace_compression S
    (by simpa using hdim) (fun j => representationToEuclidean d (B.col j)) c hc
  let B' : Matrix (Fin d) (Fin m) ℝ := fun i j => w j i
  have hcol (j) : representationToEuclidean d (B'.col j) = w j := by
    ext i
    rfl
  refine ⟨B', ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hcol]
    exact hwS j
  · simpa only [hcol] using hwgram
  · exact euclidean_synthesis_norm_eq_of_column_gram_eq B B' (by simpa only [hcol] using hwgram)
  · simpa only [hcol] using hwobj

/-- In particular, ambient compression preserves unit columns and every
specified sparse lower-stability margin. -/
theorem exists_unit_stable_dictionary_compression {d m s : ℕ}
    (S : Submodule ℝ (EuclideanRepresentation d)) (hdim : m ≤ finrank ℝ S)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ)
    (hunit : HasUnitEuclideanColumns B) (hstable : SparseLowerStable B γ s)
    (c : Fin m → EuclideanRepresentation d) (hc : ∀ j, c j ∈ S) :
    ∃ B' : Matrix (Fin d) (Fin m) ℝ,
      (∀ j, representationToEuclidean d (B'.col j) ∈ S) ∧
      HasUnitEuclideanColumns B' ∧ SparseLowerStable B' γ s ∧
      (∀ i j,
        inner ℝ (representationToEuclidean d (B'.col i)) (representationToEuclidean d (B'.col j)) =
        inner ℝ (representationToEuclidean d (B.col i)) (representationToEuclidean d (B.col j))) ∧
      (∀ u : FeatureVector m,
        ‖representationToEuclidean d (B'.mulVec u)‖ = ‖representationToEuclidean d (B.mulVec u)‖) ∧
      (∑ j, inner ℝ (c j) (representationToEuclidean d (B.col j))) ≤
        ∑ j, inner ℝ (c j) (representationToEuclidean d (B'.col j)) := by
  obtain ⟨B', hS, hgram, hnorm, hobj⟩ :=
    exists_gram_preserving_dictionary_compression S hdim B c hc
  refine ⟨B', hS, ?_, ?_, hgram, hnorm, hobj⟩
  · intro j
    have h := hgram j j
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hunit j] at h
    nlinarith [norm_nonneg (representationToEuclidean d (B'.col j))]
  · intro u hu
    rw [hnorm]
    exact hstable u hu

end PKG26AtomicFeatures
