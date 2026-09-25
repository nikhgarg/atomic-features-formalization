import PKG26AtomicFeatures.MesoscaleReferenceBenchmark
import PKG26AtomicFeatures.NonnegativeLeastSquaresIsometry
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Feasible first-order conditions for the mesoscale reference problem

All common ambient isometries preserve the feasible dictionary class. The
value identity moves such a variation to the inputs of a fixed cone, whose
squared distance is differentiable even at active-set changes. Consequently
every actual global reference optimum satisfies the rotation stationarity
condition, with no interiority assumption on its Gram constraint.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators InnerProductSpace Topology

/-- Global minimization of the actual reference objective over the actual
unit, half-stable width-two dictionaries. -/
def IsMesoscaleReferenceMinimizer (B : Matrix (Fin 3) (Fin 2) ℝ)
    (hstable : SparseLowerStable B (1 / 2) 4) : Prop :=
  HasUnitEuclideanColumns B ∧
    ∀ (C : Matrix (Fin 3) (Fin 2) ℝ), HasUnitEuclideanColumns C →
      ∀ hC : SparseLowerStable C (1 / 2) 4,
        mesoscaleReferenceNNLSRisk B hstable ≤ mesoscaleReferenceNNLSRisk C hC

theorem IsMesoscaleReferenceMinimizer.referenceRisk_lt
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable) :
    mesoscaleReferenceNNLSRisk B hstable < 49 / 100 :=
  (hmin.2 mesoscaleBenchmarkDictionary mesoscaleBenchmarkDictionary_unit
    mesoscaleBenchmarkDictionary_stable).trans_lt mesoscaleBenchmark_referenceRisk_lt

/-- The derivative along any differentiable common orthogonal variation
vanishes at an actual optimum. The variation is expressed by its inverse
action on the three observed inputs. -/
theorem IsMesoscaleReferenceMinimizer.isometry_stationarity
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable)
    (Q : ℝ → EuclideanRepresentation 3 ≃ₗᵢ[ℝ] EuclideanRepresentation 3)
    (hQzero : Q 0 = LinearIsometryEquiv.refl ℝ (EuclideanRepresentation 3))
    (v : Fin 3 → EuclideanRepresentation 3)
    (hQ : ∀ s, HasDerivAt (fun t => (Q t).symm (mesoscaleReferenceInput s)) (v s) 0) :
    ∑ s, mesoscaleReferenceWeight s * inner ℝ
      (mesoscaleReferenceInput s - representationToEuclidean 3
        (B.mulVec (nonnegativeLeastSquaresCode B (1 / 2) (by norm_num)
          (hstable.global_bound_of_width_le (by norm_num)) (mesoscaleReferenceInput s))))
      (v s) = 0 := by
  let hlower := hstable.global_bound_of_width_le (show 2 ≤ 4 by norm_num)
  let value := nonnegativeLeastSquaresValue B (1 / 2) (by norm_num) hlower
  let g : ℝ → ℝ := fun t => ∑ s, mesoscaleReferenceWeight s *
    value ((Q t).symm (mesoscaleReferenceInput s))
  have hg0 : g 0 = mesoscaleReferenceNNLSRisk B hstable := by
    simp only [g, hQzero]
    rfl
  have hgt (t : ℝ) :
      g t = mesoscaleReferenceNNLSRisk (isometricDictionary (Q t) B)
        (hstable.isometricDictionary (Q t)) := by
    unfold g mesoscaleReferenceNNLSRisk
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    exact (nonnegativeLeastSquaresValue_isometricDictionary (Q t) B (1 / 2)
      (by norm_num) hlower
      ((hstable.isometricDictionary (Q t)).global_bound_of_width_le (by norm_num))
      (mesoscaleReferenceInput s)).symm
  have hlocal : IsLocalMin g 0 := by
    apply Filter.Eventually.of_forall
    intro t
    rw [hg0, hgt]
    exact hmin.2 _ (hmin.1.isometricDictionary (Q t)) _
  have hderivative : HasDerivAt g
      (∑ s, mesoscaleReferenceWeight s * (2 * inner ℝ
        (mesoscaleReferenceInput s - representationToEuclidean 3
          (B.mulVec (nonnegativeLeastSquaresCode B (1 / 2) (by norm_num) hlower
            (mesoscaleReferenceInput s)))) (v s))) 0 := by
    apply HasDerivAt.fun_sum
    intro s _
    apply HasDerivAt.const_mul
    have hvalue := hasFDerivAt_nonnegativeLeastSquaresValue B (1 / 2)
      (by norm_num) hlower (mesoscaleReferenceInput s)
    have hinput : (Q 0).symm (mesoscaleReferenceInput s) = mesoscaleReferenceInput s := by
      rw [hQzero]
      rfl
    simpa only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
      using hvalue.comp_hasDerivAt_of_eq 0 (hQ s) hinput.symm
  have hzero := hlocal.hasDerivAt_eq_zero hderivative
  have hfactor : (∑ s, mesoscaleReferenceWeight s * (2 * inner ℝ
        (mesoscaleReferenceInput s - representationToEuclidean 3
          (B.mulVec (nonnegativeLeastSquaresCode B (1 / 2) (by norm_num) hlower
            (mesoscaleReferenceInput s)))) (v s))) =
      2 * ∑ s, mesoscaleReferenceWeight s * inner ℝ
        (mesoscaleReferenceInput s - representationToEuclidean 3
          (B.mulVec (nonnegativeLeastSquaresCode B (1 / 2) (by norm_num) hlower
            (mesoscaleReferenceInput s)))) (v s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hfactor] at hzero
  linarith

end PKG26AtomicFeatures
