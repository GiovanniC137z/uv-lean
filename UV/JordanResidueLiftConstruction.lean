import UV.JordanResidueWinding
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.MeanValue

/-! Every nonzero C1 curve has an actual C1 logarithmic lift. The lift is
constructed by an indefinite integral; its exponential identity follows
from a derived zero derivative, rather than being assumed. -/

noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology

namespace UV

def contourLogDerivative {a b : ℂ} (γ : Path a b) (p : ℂ) (t : ℝ) : ℂ :=
  derivWithin γ.extend (Icc (0 : ℝ) 1) t/(γ.extend t-p)

def contourLogDerivativeExtension {a b : ℂ} (γ : Path a b) (p : ℂ) : ℝ → ℂ :=
  Set.IccExtend zero_le_one (fun t : Icc (0 : ℝ) 1 => contourLogDerivative γ p t)

def contourLogPrimitive {a b : ℂ} (γ : Path a b) (p : ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, contourLogDerivativeExtension γ p s

theorem contourLogDerivativeExtension_continuous {a b p : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p) :
    Continuous (contourLogDerivativeExtension γ p) := by
  have hk : ContinuousOn (contourLogDerivative γ p) (Icc (0 : ℝ) 1) :=
    (hγ.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl).div
      (hγ.continuousOn.sub continuousOn_const) (fun t ht => sub_ne_zero.mpr (havoid t ht))
  exact continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_restrict.mp hk)

theorem contourLogPrimitive_hasDerivAt {a b p : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p) (t : ℝ) :
    HasDerivAt (contourLogPrimitive γ p) (contourLogDerivativeExtension γ p t) t := by
  have hk := contourLogDerivativeExtension_continuous γ hγ havoid
  exact intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable _ _)
    hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt

theorem contourLogPrimitive_c1 {a b p : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p) :
    ContDiff ℝ 1 (contourLogPrimitive γ p) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (contourLogPrimitive_hasDerivAt γ hγ havoid t).differentiableAt, ?_⟩
  have he : deriv (contourLogPrimitive γ p) = contourLogDerivativeExtension γ p :=
    funext (fun t => (contourLogPrimitive_hasDerivAt γ hγ havoid t).deriv)
  rw [he]
  exact contourLogDerivativeExtension_continuous γ hγ havoid

/-- The constructed logarithmic primitive solves the exponential transport
identity on the whole parameter interval. -/
theorem contourLogPrimitive_exponential {a b p : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    exp (contourLogPrimitive γ p t)*(a-p) = γ.extend t-p := by
  let A := contourLogPrimitive γ p
  let H : ℝ → ℂ := fun t => exp (-A t)*(γ.extend t-p)
  have hH : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H 0 (Icc (0 : ℝ) 1) u := by
    intro u hu
    have hA : HasDerivWithinAt A (contourLogDerivativeExtension γ p u) (Icc (0 : ℝ) 1) u :=
      (contourLogPrimitive_hasDerivAt γ hγ havoid u).hasDerivWithinAt
    have hExt : contourLogDerivativeExtension γ p u = contourLogDerivative γ p u :=
      Set.IccExtend_of_mem zero_le_one _ hu
    rw [hExt] at hA
    have hG := (hγ.differentiableOn (by norm_num) u hu).hasDerivWithinAt
    have hcancel : contourLogDerivative γ p u*(γ.extend u-p) =
        derivWithin γ.extend (Icc (0 : ℝ) 1) u :=
      div_mul_cancel₀ _ (sub_ne_zero.mpr (havoid u hu))
    have hz : exp (-A u)*(-contourLogDerivative γ p u)*(γ.extend u-p)+
        exp (-A u)*derivWithin γ.extend (Icc (0 : ℝ) 1) u = 0 := by
      calc
        _ = -(exp (-A u)*(contourLogDerivative γ p u*(γ.extend u-p)))+
            exp (-A u)*derivWithin γ.extend (Icc (0 : ℝ) 1) u := by ring
        _ = 0 := by rw [hcancel]; ring
    exact (hA.neg.cexp.mul (hG.sub_const p)).congr_deriv hz
  have hdiff : DifferentiableOn ℝ H (Icc (0 : ℝ) 1) :=
    fun u hu => (hH u hu).differentiableWithinAt
  have hzero : ∀ u ∈ Icc (0 : ℝ) 1, fderivWithin ℝ H (Icc (0 : ℝ) 1) u = 0 := by
    intro u hu
    rw [(hH u hu).hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc zero_lt_one u hu)]
    ext
    simp
  have hconst := (convex_Icc (0 : ℝ) 1).is_const_of_fderivWithin_eq_zero hdiff hzero
    ht (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
  have hH0 : H 0 = a-p := by simp [H, A, contourLogPrimitive]
  have htransport : exp (-A t)*(γ.extend t-p) = a-p := hconst.trans hH0
  calc
    _ = exp (A t)*(exp (-A t)*(γ.extend t-p)) := by rw [htransport]
    _ = (exp (A t)*exp (-A t))*(γ.extend t-p) := by ring
    _ = γ.extend t-p := by rw [← exp_add, add_neg_cancel, exp_zero, one_mul]

/-- Actual logarithmic lift for every C1 curve that avoids the pole. -/
def constructedContourLogLift {a b p : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ p) : C1ContourLogLift γ p where
  value t := contourLogPrimitive γ p t+log (a-p)
  c1 := ((contourLogPrimitive_c1 γ hγ havoid).add contDiff_const).contDiffOn
  exponential t ht := by
    have han : a-p ≠ 0 := by
      simpa using sub_ne_zero.mpr (havoid 0 ⟨le_rfl, zero_le_one⟩)
    rw [exp_add, exp_log han]
    exact contourLogPrimitive_exponential γ hγ havoid ht

/-- The geometric winding does not depend on which logarithmic lift was
used. Its contour computation is already a theorem. -/
theorem contourLiftWinding_independent {a p : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (L M : C1ContourLogLift γ p) : contourLiftWinding L = contourLiftWinding M := by
  have h := (parametrizedContourIntegral_cauchyKernel_winding γ hγ L).symm.trans
    (parametrizedContourIntegral_cauchyKernel_winding γ hγ M)
  exact_mod_cast mul_right_cancel₀ (by simp [Real.pi_ne_zero]) h

end UV
