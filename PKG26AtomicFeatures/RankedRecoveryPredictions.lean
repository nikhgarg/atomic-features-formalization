import PKG26AtomicFeatures.RankedFeatureTail

/-!
# Ranked prefixes for the matching predictions

Under decreasing prevalence order, the tail-recoverable feature set is
exactly the concrete ranked prefix ending at its last recoverable rank.
Its cardinality is that rank, including the empty case. Two populations
retain their own rankings and recovery ranks when their recovered sets are
intersected.
-/

namespace PKG26AtomicFeatures

/-- A decreasing prevalence ordering identifies the recoverable features
with the image of the concrete prefix embedding of length equal to the
recovery rank. The checked bound on the rank supplies the embedding domain. -/
theorem tailRecoverableFeatures_eq_rankedPrefix_image
    {M : ℕ} (p : Fin M → ℝ) (σ : Equiv.Perm (Fin M))
    (horder : Antitone (fun j : Fin M => p (σ j))) (C : ℝ) (m : ℕ) :
    tailRecoverableFeatures p σ C m =
      Finset.univ.image (rankedPrefixEmbedding σ (tailRecoverableRank_le p σ C m)) := by
  classical
  ext i
  rw [mem_rankedPrefixEmbedding_image]
  simpa only [σ.apply_symm_apply] using
    mem_tailRecoverableFeatures_iff_rank_lt p σ horder C m (σ.symm i)

/-- The last recoverable rank equals the number of recovered features
when prevalence is in decreasing order. In particular, an empty recovered
set has rank zero without requiring a nonempty maximum. -/
theorem tailRecoverableFeatures_card_eq_rank
    {M : ℕ} (p : Fin M → ℝ) (σ : Equiv.Perm (Fin M))
    (horder : Antitone (fun j : Fin M => p (σ j))) (C : ℝ) (m : ℕ) :
    (tailRecoverableFeatures p σ C m).card = tailRecoverableRank p σ C m := by
  rw [tailRecoverableFeatures_eq_rankedPrefix_image p σ horder C m,
    Finset.card_image_of_injective _
      (rankedPrefixEmbedding σ (tailRecoverableRank_le p σ C m)).injective]
  simp only [Finset.card_univ, Fintype.card_fin]

/-- An equivalent prefix description uses original rank indices below
`r`, then applies the ranking permutation. This is the finite-set meaning
of the paper's notation `σ([r])`. -/
theorem tailRecoverableFeatures_eq_image_rank_filter
    {M : ℕ} (p : Fin M → ℝ) (σ : Equiv.Perm (Fin M))
    (horder : Antitone (fun j : Fin M => p (σ j))) (C : ℝ) (m : ℕ) :
    tailRecoverableFeatures p σ C m =
      (Finset.univ.filter fun j : Fin M => j.val < tailRecoverableRank p σ C m).image σ := by
  classical
  ext i
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    refine ⟨σ.symm i, ?_, σ.apply_symm_apply i⟩
    apply (mem_tailRecoverableFeatures_iff_rank_lt p σ horder C m (σ.symm i)).mp
    simpa only [σ.apply_symm_apply] using hi
  · rintro ⟨j, hj, rfl⟩
    exact (mem_tailRecoverableFeatures_iff_rank_lt p σ horder C m j).mpr hj

/-- Common recovery across two ranked populations is the intersection
of their own ranked prefixes. Both recovery ranks are computed separately;
neither their values nor their ranking permutations are identified. -/
theorem tailRecoverableFeatures_inter_eq_rankedPrefix_inter
    {M : ℕ} (p p' : Fin M → ℝ) (σ σ' : Equiv.Perm (Fin M))
    (horder : Antitone (fun j : Fin M => p (σ j)))
    (horder' : Antitone (fun j : Fin M => p' (σ' j)))
    (C C' : ℝ) (m m' : ℕ) :
    tailRecoverableFeatures p σ C m ∩ tailRecoverableFeatures p' σ' C' m' =
      Finset.univ.image (rankedPrefixEmbedding σ (tailRecoverableRank_le p σ C m)) ∩
        Finset.univ.image (rankedPrefixEmbedding σ' (tailRecoverableRank_le p' σ' C' m')) := by
  rw [tailRecoverableFeatures_eq_rankedPrefix_image p σ horder C m,
    tailRecoverableFeatures_eq_rankedPrefix_image p' σ' horder' C' m']

end PKG26AtomicFeatures
