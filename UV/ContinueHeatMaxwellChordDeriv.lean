import UV.ContinueHeatMaxwellSignMarks
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation under the chord parameter integrals for the transverse
Wilson marks. All momenta and polarization vectors use the Euclidean
continuation of the selected sector plane. -/

noncomputable section
namespace UV.HeatMaxwell
open UV.RelativeSoft UV.SectorPlane MeasureTheory Filter Set Metric
open scoped RealInnerProductSpace Topology

private theorem heat_chord_range {v t s : ℝ} (hv : |v|≤1) (hs : |s-t|<1) :
    v*s ∈ Icc (-(|t|+1)) (|t|+1) := by
  apply abs_le.mp
  rw [abs_mul]
  have hit : |s| ≤ |s-t|+|t| := by simpa using abs_add_le (s-t) t
  calc |v| * |s| ≤ 1*|s| := mul_le_mul_of_nonneg_right hv (abs_nonneg _)
       _ ≤ |t|+1 := by linarith

private theorem heat_chord_weight_bound {v : ℝ} (hv : |v|≤1) (n : ℕ) : ‖v^n‖ ≤ 1 := by
  rw [norm_pow,Real.norm_eq_abs]
  exact pow_le_one₀ (abs_nonneg _) hv

variable {ι V : Type*} [MeasurableSpace ι] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Moments of the actual parameter distribution, with the same bounded
parameter used before and after differentiation. -/
def heatChordMoment (μ : Measure ι) (a : ι → ℝ) (n : ℕ) (f : ℝ → V) (t : ℝ) : V :=
  ∫ z, (a z)^n • f (a z*t) ∂μ

theorem heat_chord_moment_hasDerivAt {μ : Measure ι} [IsFiniteMeasure μ]
    {a : ι→ℝ} (ha : Measurable a) (hab : ∀ᵐ z ∂μ, |a z|≤1)
    {f g : ℝ→V} (hg : Continuous g) (hfg : ∀ s, HasDerivAt f (g s) s) (n : ℕ) (t : ℝ) :
    HasDerivAt (heatChordMoment μ a n f) (heatChordMoment μ a (n+1) g t) t := by
  let K := Icc (-(|t|+1)) (|t|+1)
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun s => (hfg s).continuousAt
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image (K:=K) hg.norm.continuousOn
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (K:=K) hf.norm.continuousOn
  let F := fun (s : ℝ) (z : ι) => (a z)^n • f (a z*s)
  let D := fun (s : ℝ) (z : ι) => (a z)^(n+1) • g (a z*s)
  have hFm (s : ℝ) : AEStronglyMeasurable (F s) μ :=
    (ha.pow_const n).aestronglyMeasurable.smul (hf.comp_aestronglyMeasurable (ha.mul_const s).aestronglyMeasurable)
  have hDm (s : ℝ) : AEStronglyMeasurable (D s) μ :=
    (ha.pow_const _).aestronglyMeasurable.smul (hg.comp_aestronglyMeasurable (ha.mul_const s).aestronglyMeasurable)
  have hi : Integrable (F t) μ := by
    apply (integrable_const B).mono' (hFm t)
    filter_upwards [hab] with z hz
    rw [show F t z = (a z)^n • f (a z*t) from rfl,norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (heat_chord_weight_bound hz n)).trans
      (hB ⟨_,heat_chord_range hz (by simp),rfl⟩)
  have hdiff (z s) : HasDerivAt (fun s => F s z) (D s z) s := by
    have h := ((hfg (a z*s)).scomp s ((hasDerivAt_id s).const_mul (a z))).const_smul ((a z)^n)
    simpa [F,D,Function.comp_def,smul_smul,pow_succ] using h
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ) (x₀:=t) (F:=F) (F':=D)
    (bound:=fun _ => C) (show (0:ℝ)<1 by norm_num) (Eventually.of_forall hFm) hi (hDm t) ?_
    (integrable_const _) (Eventually.of_forall fun z s _ => hdiff z s)).2
  filter_upwards [hab] with z hz
  intro s hs
  rw [show D s z = (a z)^(n+1) • g (a z*s) from rfl,norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (heat_chord_weight_bound hz (n+1))).trans
    (hC ⟨_,heat_chord_range hz (by simpa [Real.dist_eq] using hs),rfl⟩)

/-- The double derivative of the averaged chord uses its second moment,
also when the mark is a contact that lives on a single chord. -/
theorem heat_chord_second_at_zero [CompleteSpace V] {μ : Measure ι} [IsFiniteMeasure μ]
    {a : ι → ℝ} (ha : Measurable a) (hab : ∀ᵐ z ∂μ, |a z|≤1) {f : ℝ→V} (hf : ContDiff ℝ 2 f) :
    deriv (deriv (heatChordMoment μ a 0 f)) 0 = (∫ z, (a z)^2 ∂μ) • deriv (deriv f) 0 := by
  have h1 (s) := (hf.differentiable (by norm_num)).differentiableAt (x:=s) |>.hasDerivAt
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have h2 (s) := (hf'.differentiable (by norm_num)).differentiableAt (x:=s) |>.hasDerivAt
  have he : deriv (heatChordMoment μ a 0 f) = heatChordMoment μ a 1 (deriv f) :=
    funext fun s => (heat_chord_moment_hasDerivAt ha hab hf'.continuous h1 0 s).deriv
  rw [he,(heat_chord_moment_hasDerivAt ha hab (hf'.continuous_deriv (by norm_num)) h2 1 0).deriv]
  simp [heatChordMoment,integral_smul_const]

end UV.HeatMaxwell
