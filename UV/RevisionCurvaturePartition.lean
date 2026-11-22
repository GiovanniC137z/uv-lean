import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Finite-coupling relative normalization with one common depth weight.
This argument starts after construction of the underlying field law. -/

namespace UV.RevisionCurvaturePartition

open MeasureTheory Filter Set
open scoped Topology

variable {Ω : Type*}

noncomputable def curvatureWeight (H V : Ω → ℝ) (g : ℝ) (ω : Ω) : ℝ :=
  H ω * Real.exp (-g * V ω)

theorem curvature_weight_bounds {H V : Ω → ℝ} {g : ℝ} (hg : 0 ≤ g)
    {ω : Ω} (h0 : 0 ≤ H ω) (h1 : H ω ≤ 1) (hV : 0 ≤ V ω) :
    0 ≤ curvatureWeight H V g ω ∧ curvatureWeight H V g ω ≤ 1 := by
  have he : Real.exp (-g * V ω) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg) hV)
  exact ⟨mul_nonneg h0 (Real.exp_nonneg _), (mul_le_mul_of_nonneg_left he h0).trans (by linarith)⟩

variable [MeasurableSpace Ω]

/-- The positive-depth set contributes positive total relative mass for
every nonnegative coupling. -/
theorem relative_partition_positive (ν : Measure Ω) [IsFiniteMeasure ν]
    (H V : Ω → ℝ) (hH : Measurable H) (hV : Measurable V)
    (h0 : ∀ ω, 0 ≤ H ω) (h1 : ∀ ω, H ω ≤ 1) (hpos : ∀ ω, 0 ≤ V ω)
    (S : Set Ω) (hS : ν S ≠ 0) (hHS : ∀ ω ∈ S, 0 < H ω)
    {g : ℝ} (hg : 0 ≤ g) :
    0 < (∫ ω, curvatureWeight H V g ω ∂ν) ∧
      (∫ ω, curvatureWeight H V g ω ∂ν) ≤ (ν univ).toReal := by
  have hw (ω : Ω) := curvature_weight_bounds hg (h0 ω) (h1 ω) (hpos ω)
  have hm : Measurable (curvatureWeight H V g) := by
    unfold curvatureWeight
    fun_prop
  have hi : Integrable (curvatureWeight H V g) ν := by
    refine (integrable_const 1).mono' hm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    simpa only [Real.norm_of_nonneg (hw ω).1] using (hw ω).2
  constructor
  · apply (integral_pos_iff_support_of_nonneg (fun ω => (hw ω).1) hi).mpr
    apply pos_iff_ne_zero.mpr
    intro hz
    refine hS (measure_mono_null (fun ω hω => ?_) hz)
    exact (mul_pos (hHS ω hω) (Real.exp_pos _)).ne'
  · simpa using integral_mono hi (integrable_const 1) (fun ω => (hw ω).2)

/-- Once the cut-off densities converge on a common preparation with the
source's unit bound, normalized moments converge for any moment with a
common integrable envelope. -/
theorem relative_normalized_moments_tendsto (ν : Measure Ω) [IsFiniteMeasure ν]
    (W : ℕ → Ω → ℝ) (w : Ω → ℝ) (F : ℕ → Ω → ℝ) (f b : Ω → ℝ)
    (hwm : ∀ j, AEStronglyMeasurable (W j) ν) (hfm : ∀ j, AEStronglyMeasurable (F j) ν)
    (hwBound : ∀ j, ∀ᵐ ω ∂ν, ‖W j ω‖ ≤ 1)
    (hfBound : ∀ j, ∀ᵐ ω ∂ν, ‖F j ω‖ ≤ b ω)
    (hb : Integrable b ν)
    (hw : ∀ᵐ ω ∂ν, Tendsto (fun j => W j ω) atTop (𝓝 (w ω)))
    (hf : ∀ᵐ ω ∂ν, Tendsto (fun j => F j ω) atTop (𝓝 (f ω)))
    (hz : (∫ ω, w ω ∂ν) ≠ 0) :
    Tendsto (fun j => (∫ ω, W j ω * F j ω ∂ν) / (∫ ω, W j ω ∂ν)) atTop
      (𝓝 ((∫ ω, w ω * f ω ∂ν) / (∫ ω, w ω ∂ν))) := by
  have hd := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => 1)
    hwm (integrable_const 1) hwBound hw
  have hn := tendsto_integral_of_dominated_convergence (μ := ν) b
    (fun j => (hwm j).mul (hfm j)) hb
    (fun j => by
      filter_upwards [hwBound j, hfBound j] with ω hω hF
      change ‖W j ω * F j ω‖ ≤ b ω
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hω (norm_nonneg _)).trans (by simpa using hF))
    (by filter_upwards [hw, hf] with ω hω hF using hω.mul hF)
  exact hn.div hd hz

end UV.RevisionCurvaturePartition
