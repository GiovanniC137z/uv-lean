import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! The fundamental theorem for genuinely Lipschitz curves. Almost
everywhere differentiability comes from bounded variation. Dominated
difference quotients identify the integral with the endpoint difference,
so no everywhere differentiability or C1 reparametrization is assumed. -/

/- Ported from the verified UV 4.24 development to Lean/mathlib 4.32.2;
the clamped-extension definition is unfolded explicitly. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal Interval

namespace UV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lipschitz_difference_quotient_bound {f : ℝ → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {h : ℝ} (hh : h ≠ 0) (t : ℝ) :
    ‖h⁻¹ • (f (t+h)-f t)‖ ≤ K := by
  have hdiff : ‖f (t+h)-f t‖ ≤ (K : ℝ)*|h| := by
    simpa only [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs] using hf.dist_le_mul (t+h) t
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    _ ≤ |h|⁻¹*((K : ℝ)*|h|) := mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = K := by field_simp [abs_ne_zero.mpr hh]

/-- Translation reduces the integral of a difference quotient to the two
short boundary averages, before taking any limit. -/
theorem integral_shift_quotient_boundary {f : ℝ → E} (hf : Continuous f)
    (a b h : ℝ) :
    (∫ t in a..b, h⁻¹ • (f (t+h)-f t)) =
      h⁻¹ • ((∫ t in b..b+h, f t)-(∫ t in a..a+h, f t)) := by
  rw [intervalIntegral.integral_smul,
    intervalIntegral.integral_sub (f := fun t => f (t+h)) (g := f)
      ((hf.comp (continuous_id.add continuous_const)).intervalIntegrable a b)
      (hf.intervalIntegrable a b), intervalIntegral.integral_comp_add_right]
  congr 1
  exact intervalIntegral.integral_interval_sub_interval_comm'
    (hf.intervalIntegrable (a+h) (b+h)) (hf.intervalIntegrable a b)
    (hf.intervalIntegrable (a+h) a)

omit [NormedSpace ℝ E] in
/-- Clamping a Lipschitz interval curve gives a genuine global Lipschitz
extension, with the same Lipschitz constant. -/
theorem lipschitz_IccExtend {f : ℝ → E} {a b : ℝ} {K : ℝ≥0}
    (hab : a ≤ b) (hf : LipschitzOnWith K f (Icc a b)) :
    LipschitzWith K (IccExtend hab (fun x : Icc a b => f x)) := by
  have hg : LipschitzWith K (fun x : Icc a b => f x) :=
    LipschitzWith.of_dist_le_mul (fun x y => hf.dist_le_mul x x.property y y.property)
  simpa only [mul_one, IccExtend] using hg.comp (LipschitzWith.projIcc hab)

variable [CompleteSpace E]

/-- The actual derivative of a Lipschitz curve is interval integrable. -/
theorem lipschitz_deriv_intervalIntegrable {f : ℝ → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) : IntervalIntegrable (deriv f) volume a b := by
  rw [intervalIntegrable_iff]
  have hb : IntervalIntegrable (fun _ : ℝ => (K : ℝ)) volume a b := intervalIntegrable_const
  apply (intervalIntegrable_iff.mp hb).mono' (aestronglyMeasurable_deriv f _)
  exact Eventually.of_forall (fun _ => norm_deriv_le_of_lipschitz hf)

/-- Fundamental theorem for a Lipschitz function with genuine a.e.
derivatives, including Banach-valued compositions of scalar curves. -/
theorem lipschitz_integral_deriv_of_ae_differentiable {f : ℝ → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hAE : ∀ᵐ t : ℝ, DifferentiableAt ℝ f t) (a b : ℝ) :
    (∫ t in a..b, deriv f t) = f b-f a := by
  have hcont := hf.continuous
  have hlim (c : ℝ) :
      Tendsto (fun h : ℝ => h⁻¹ • (∫ t in c..c+h, f t)) (𝓝[>] 0) (𝓝 (f c)) := by
    have hp := intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable c c)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
    simpa only [intervalIntegral.integral_same, sub_zero] using hp.tendsto_slope_zero_right
  have hboundary : Tendsto
      (fun h : ℝ => h⁻¹ • ((∫ t in b..b+h, f t)-(∫ t in a..a+h, f t)))
      (𝓝[>] 0) (𝓝 (f b-f a)) := by
    simpa only [smul_sub] using (hlim b).sub (hlim a)
  have hright : Tendsto (fun h : ℝ => ∫ t in a..b, h⁻¹ • (f (t+h)-f t))
      (𝓝[>] 0) (𝓝 (f b-f a)) := by
    simpa only [integral_shift_quotient_boundary hcont] using hboundary
  have hleft := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ))
    (a := a) (b := b) (μ := volume) (f := deriv f)
    (F := fun h t : ℝ => h⁻¹ • (f (t+h)-f t)) (fun _ => (K : ℝ))
    (Eventually.of_forall (fun h =>
      (((hcont.comp (continuous_id.add continuous_const)).sub hcont).const_smul h⁻¹).aestronglyMeasurable))
    (by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact Eventually.of_forall (fun t _ => lipschitz_difference_quotient_bound hf (ne_of_gt hh) t))
    intervalIntegrable_const
    (by
      filter_upwards [hAE] with t ht
      intro _
      exact ht.hasDerivAt.tendsto_slope_zero_right)
  exact tendsto_nhds_unique hleft hright

/-- Finite-dimensional Lipschitz curves have the required a.e. derivatives
by the bounded-variation theorem, so the endpoint identity is unconditional. -/
theorem lipschitz_integral_deriv [FiniteDimensional ℝ E] {f : ℝ → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) :
    (∫ t in a..b, deriv f t) = f b-f a :=
  lipschitz_integral_deriv_of_ae_differentiable hf hf.ae_differentiableAt_real a b

/-- The local-interval form transfers integrability and the endpoint identity
from the clamped extension. This includes non-smooth Lipschitz parameters. -/
theorem lipschitzOn_derivWithin_properties [FiniteDimensional ℝ E]
    {f : ℝ → E} {a b : ℝ} {K : ℝ≥0} (hab : a ≤ b)
    (hf : LipschitzOnWith K f (Icc a b)) :
    IntervalIntegrable (derivWithin f (Icc a b)) volume a b ∧
      (∫ t in a..b, derivWithin f (Icc a b) t) = f b-f a := by
  by_cases he : a = b
  · subst b
    simp
  let F : ℝ → E := IccExtend hab (fun x : Icc a b => f x)
  have hF : LipschitzWith K F := lipschitz_IccExtend hab hf
  have hEq : EqOn F f (Icc a b) := by
    intro x hx
    exact IccExtend_of_mem (h := hab) (fun t : Icc a b => f t) hx
  have hder : ∀ᵐ x : ℝ ∂volume, x ∈ Ι a b →
      derivWithin f (Icc a b) x = deriv F x := by
    have hnb : ∀ᵐ x : ℝ ∂volume, x ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [hnb] with x hxb
    intro hx
    have hx' : x ∈ Ioc a b := by simpa only [uIoc_of_le hab] using hx
    have hxb' : x < b := lt_of_le_of_ne hx'.2 hxb
    exact (derivWithin_congr hEq (hEq ⟨hx'.1.le, hx'.2⟩)).symm.trans
      (derivWithin_of_mem_nhds (Icc_mem_nhds hx'.1 hxb'))
  have hAE : derivWithin f (Icc a b) =ᵐ[volume.restrict (Ι a b)] deriv F :=
    (ae_restrict_iff' measurableSet_uIoc).2 hder
  refine ⟨(intervalIntegrable_congr_ae hAE).2 (lipschitz_deriv_intervalIntegrable hF a b), ?_⟩
  calc
    _ = ∫ t in a..b, deriv F t := intervalIntegral.integral_congr_ae hder
    _ = F b-F a := lipschitz_integral_deriv hF a b
    _ = f b-f a := by rw [hEq (right_mem_Icc.mpr hab), hEq (left_mem_Icc.mpr hab)]

end UV
