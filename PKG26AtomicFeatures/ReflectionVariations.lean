import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Feasible orthogonal variations from two reflections

The actual path is a composition of linear isometries, so orthogonality
constraints hold for every parameter value. At a unit normal n, moving its
reflection line in an orthogonal direction v generates the full elementary
skew variation. The inverse-action derivative is proved from the singleton
reflection formula and the ordinary scalar quotient rule.
-/

namespace PKG26AtomicFeatures

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A globally defined path of actual orthogonal transformations. With
Mathlib's composition convention, it applies the moving reflection first. -/
noncomputable def reflectionVariation (n v : E) (t : ℝ) : E ≃ₗᵢ[ℝ] E :=
  (Submodule.reflection (ℝ ∙ (n + t • v))).trans (Submodule.reflection (ℝ ∙ n))

/-- The two reflections cancel at parameter zero. -/
@[simp] theorem reflectionVariation_zero (n v : E) :
    reflectionVariation n v 0 = LinearIsometryEquiv.refl ℝ E := by
  simp [reflectionVariation]

/-- The inverse action reverses the order of the two involutions. -/
theorem reflectionVariation_symm_apply (n v x : E) (t : ℝ) :
    (reflectionVariation n v t).symm x =
      (Submodule.reflection (ℝ ∙ (n + t • v))) ((Submodule.reflection (ℝ ∙ n)) x) := by
  simp [reflectionVariation, LinearIsometryEquiv.symm_trans]

/-- The moving reflection line never vanishes under the unit and
orthogonality assumptions, and its squared norm has this exact polynomial. -/
theorem norm_sq_unit_add_orthogonal_smul (n v : E)
    (hn : ‖n‖ = 1) (horth : inner ℝ n v = 0) (t : ℝ) :
    ‖n + t • v‖ ^ 2 = 1 + t ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real]
  simp [hn, horth, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow]

/-- The derivative of a single moving-line reflection, before composition
with the fixed reflection. -/
theorem hasDerivAt_moving_reflection (n v x : E)
    (hn : ‖n‖ = 1) (horth : inner ℝ n v = 0) :
    HasDerivAt (fun t : ℝ => (Submodule.reflection (ℝ ∙ (n + t • v))) x)
      ((2 : ℝ) • (inner ℝ n x • v + inner ℝ v x • n)) 0 := by
  have hpath : HasDerivAt (fun t : ℝ => n + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add n
  have hnum : HasDerivAt (fun t : ℝ => inner ℝ (n + t • v) x) (inner ℝ v x) 0 := by
    simpa using hpath.inner ℝ (hasDerivAt_const (0 : ℝ) x)
  have hden : HasDerivAt (fun t : ℝ => ‖n + t • v‖ ^ 2) 0 0 := by
    simpa [horth] using hpath.norm_sq
  have hquot : HasDerivAt
      (fun t : ℝ => inner ℝ (n + t • v) x / ‖n + t • v‖ ^ 2) (inner ℝ v x) 0 := by
    simpa [hn] using hnum.div hden (by simp [hn])
  have hproduct := ((hquot.smul hpath).const_smul (2 : ℝ)).sub_const x
  convert hproduct using 1
  · ext t
    rw [Submodule.reflection_singleton_apply]
    simp [two_smul]
  · simp [hn]

/-- A unit-line reflection preserves the normal component and negates
components orthogonal to that normal. -/
theorem unit_reflection_inner_components (n v x : E)
    (hn : ‖n‖ = 1) (horth : inner ℝ n v = 0) :
    inner ℝ n ((Submodule.reflection (ℝ ∙ n)) x) = inner ℝ n x ∧
    inner ℝ v ((Submodule.reflection (ℝ ∙ n)) x) = -inner ℝ v x := by
  have hreflect : (Submodule.reflection (ℝ ∙ n)) x =
      (2 : ℝ) • (inner ℝ n x • n) - x := by
    simpa [hn, two_smul, add_smul] using
      (Submodule.reflection_singleton_apply (𝕜 := ℝ) n x)
  rw [hreflect]
  simp only [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm n v, horth, hn, one_pow]
  constructor <;> ring

/-- The inverse path generates the desired skew variation at zero. Its
hypotheses concern only the actual unit normal and its orthogonal tangent;
the path itself consists of linear isometries for every real parameter. -/
theorem hasDerivAt_reflectionVariation_symm (n v x : E)
    (hn : ‖n‖ = 1) (horth : inner ℝ n v = 0) :
    HasDerivAt (fun t : ℝ => (reflectionVariation n v t).symm x)
      ((2 : ℝ) • (inner ℝ n x • v - inner ℝ v x • n)) 0 := by
  have h := hasDerivAt_moving_reflection n v ((Submodule.reflection (ℝ ∙ n)) x) hn horth
  obtain ⟨hnx, hvx⟩ := unit_reflection_inner_components n v x hn horth
  simpa only [reflectionVariation_symm_apply, hnx, hvx, neg_smul, sub_eq_add_neg] using h

/-- The ordinary derivative form of the inverse-action identity. -/
theorem deriv_reflectionVariation_symm (n v x : E)
    (hn : ‖n‖ = 1) (horth : inner ℝ n v = 0) :
    deriv (fun t : ℝ => (reflectionVariation n v t).symm x) 0 =
      (2 : ℝ) • (inner ℝ n x • v - inner ℝ v x • n) :=
  (hasDerivAt_reflectionVariation_symm n v x hn horth).deriv

end PKG26AtomicFeatures
