import UV.ContinueOrderedHopTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The actual first-order covariant onsite inverse on a slab. The
positive-mass slot uses the left endpoint, the negative-mass slot the
right endpoint. The connection is real and continuous on the carrier
line at the specified spatial point. -/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace UV.SectorPlane

private def orderedOnsiteExponent (μ q : ℝ) (A : ℝ → ℝ) (t : ℝ) : ℂ :=
  (μ:ℂ)*(t:ℂ)+Complex.I*(q:ℂ)*((∫ s in (0:ℝ)..t, A s):ℝ)

def orderedOnsiteCoefficient (μ q : ℝ) (A : ℝ → ℝ) (t : ℝ) : ℂ :=
  (μ:ℂ)+Complex.I*(q:ℂ)*(A t:ℂ)

private theorem orderedOnsite_exponent_deriv (μ q : ℝ) {A : ℝ → ℝ} (hA : Continuous A) (t : ℝ) :
    HasDerivAt (orderedOnsiteExponent μ q A) (orderedOnsiteCoefficient μ q A t) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right (hA.intervalIntegrable (μ := volume) 0 t)
    hA.aestronglyMeasurable.stronglyMeasurableAtFilter hA.continuousAt
  simpa only [orderedOnsiteCoefficient,Complex.ofReal_one,mul_one] using
    (((hasDerivAt_id t).ofReal_comp.const_mul (μ:ℂ)).add (hi.ofReal_comp.const_mul (Complex.I*(q:ℂ))))

def orderedOnsiteKernel (μ q : ℝ) (A : ℝ → ℝ) (t s : ℝ) : ℂ :=
  Complex.exp (-Complex.I*(q:ℂ)*((∫ r in s..t, A r):ℝ)) * (Real.exp (-μ*(t-s)):ℂ)

theorem orderedOnsite_kernel_norm (μ q : ℝ) (A : ℝ → ℝ) (t s : ℝ) :
    ‖orderedOnsiteKernel μ q A t s‖ = Real.exp (-μ*(t-s)) := by
  simp [orderedOnsiteKernel,Complex.norm_exp,Complex.mul_re]

private theorem orderedOnsite_kernel_factor (μ q : ℝ) {A : ℝ → ℝ} (hA : Continuous A) (t s : ℝ) :
    orderedOnsiteKernel μ q A t s =
      Complex.exp (-orderedOnsiteExponent μ q A t)*Complex.exp (orderedOnsiteExponent μ q A s) := by
  have hi := intervalIntegral.integral_interval_sub_left (hA.intervalIntegrable (μ := volume) 0 t)
    (hA.intervalIntegrable (μ := volume) 0 s)
  simp only [orderedOnsiteKernel,←hi,orderedOnsiteExponent,Complex.ofReal_exp,←Complex.exp_add,
    Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_sub]
  congr 1
  ring

/-- The oriented Green integral vanishes at the prescribed onsite endpoint. -/
def orderedOnsiteSolution (μ q : ℝ) (A : ℝ → ℝ) (T : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in T..t, orderedOnsiteKernel μ q A t s * f s

theorem orderedOnsite_endpoint (μ q : ℝ) (A : ℝ → ℝ) (T : ℝ) (f : ℝ → ℂ) :
    orderedOnsiteSolution μ q A T f T = 0 := by simp [orderedOnsiteSolution]

private theorem orderedOnsite_solution_factor (μ q : ℝ) {A : ℝ → ℝ} (hA : Continuous A) (T : ℝ) (f : ℝ → ℂ) (t : ℝ) :
    orderedOnsiteSolution μ q A T f t = Complex.exp (-orderedOnsiteExponent μ q A t) *
      ∫ s in T..t, Complex.exp (orderedOnsiteExponent μ q A s)*f s := by
  simp only [orderedOnsiteSolution,orderedOnsite_kernel_factor μ q hA,mul_assoc,intervalIntegral.integral_const_mul]

/-- Applying ∂τ + μ + i q A to the Wilson-transported Green integral recovers
the original source (positive or negative mass, both endpoint orientations). -/
theorem orderedOnsite_solution_deriv (μ q : ℝ) {A : ℝ → ℝ} (hA : Continuous A)
    (T : ℝ) {f : ℝ → ℂ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (orderedOnsiteSolution μ q A T f)
      (f t - orderedOnsiteCoefficient μ q A t * orderedOnsiteSolution μ q A T f t) t := by
  let H := orderedOnsiteExponent μ q A
  have hH := orderedOnsite_exponent_deriv μ q hA
  have hcont : Continuous H := continuous_iff_continuousAt.mpr fun s => (hH s).continuousAt
  have hc : Continuous (fun s => Complex.exp (H s)*f s) := (Complex.continuous_exp.comp hcont).mul hf
  have hI := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (μ := volume) T t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he := ((hH t).neg.cexp).mul hI
  rw [show orderedOnsiteSolution μ q A T f = fun u => Complex.exp (-H u) *
    ∫ s in T..u, Complex.exp (H s)*f s from funext (orderedOnsite_solution_factor μ q hA T f)]
  convert he using 1
  simp only [Pi.neg_apply]
  change _ = Complex.exp (-H t)*(-orderedOnsiteCoefficient μ q A t)*
    (∫ s in T..t, Complex.exp (H s)*f s) + Complex.exp (-H t)*(Complex.exp (H t)*f t)
  rw [←mul_assoc (Complex.exp (-H t)) (Complex.exp (H t)),←Complex.exp_add,neg_add_cancel,Complex.exp_zero,one_mul]
  ring

theorem orderedOnsite_solution_unique (μ q : ℝ) {A : ℝ → ℝ} (hA : Continuous A)
    (T : ℝ) {f F : ℝ → ℂ} (hf : Continuous f) (hT : F T = 0)
    (hF : ∀ t, HasDerivAt F (f t-orderedOnsiteCoefficient μ q A t*F t) t) :
    F = orderedOnsiteSolution μ q A T f := by
  let Y := orderedOnsiteSolution μ q A T f
  let D := fun t => Complex.exp (orderedOnsiteExponent μ q A t)*(F t-Y t)
  have hD (t : ℝ) : HasDerivAt D 0 t := by
    have h := ((orderedOnsite_exponent_deriv μ q hA t).cexp).mul
      ((hF t).sub (orderedOnsite_solution_deriv μ q hA T hf t))
    convert h using 1
    simp only [Pi.sub_apply]
    ring
  have hzero : D T = 0 := by simp [D,Y,hT,orderedOnsite_endpoint]
  funext t
  have h := (is_const_of_deriv_eq_zero (fun s => (hD s).differentiableAt) (fun s => (hD s).deriv) t T).trans hzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _))

/-- A point representative of the two directed kernels, zero on the diagonal. -/
def orderedOnsiteDirected (m q : ℝ) (A : ℝ → ℝ) (positive : Bool) (t s : ℝ) : ℂ :=
  if positive then (if s < t then orderedOnsiteKernel m q A t s else 0)
  else (if t < s then -orderedOnsiteKernel (-m) q A t s else 0)

theorem orderedOnsite_directed_bound (m q : ℝ) (A : ℝ → ℝ) (positive : Bool) (t s : ℝ) :
    ‖orderedOnsiteDirected m q A positive t s‖ ≤ Real.exp (-m*|t-s|) := by
  cases positive <;> unfold orderedOnsiteDirected <;> simp only [Bool.false_eq_true,↓reduceIte]
  · split_ifs with h
    · rw [norm_neg,orderedOnsite_kernel_norm,abs_of_neg (sub_neg.mpr h),neg_neg,neg_mul_neg]
    · simp only [norm_zero]; positivity
  · split_ifs with h
    · rw [orderedOnsite_kernel_norm,abs_of_pos (sub_pos.mpr h)]
    · simp only [norm_zero]; positivity

/-- Both causal kernels give their assigned endpoint inverse by integration on
the same slab. The value of the kernel at its jump has zero measure. -/
theorem orderedOnsite_slab (m q : ℝ) (A : ℝ → ℝ) (a b t : ℝ) (ha : a ≤ t) (hb : t ≤ b) (f : ℝ → ℂ) :
    (∫ s in a..b, orderedOnsiteDirected m q A true t s * f s) = orderedOnsiteSolution m q A a f t ∧
    (∫ s in a..b, orderedOnsiteDirected m q A false t s * f s) = orderedOnsiteSolution (-m) q A b f t := by
  constructor
  · have he (s : ℝ) : orderedOnsiteDirected m q A true t s*f s =
        (Iio t).indicator (fun s => orderedOnsiteKernel m q A t s*f s) s := by
      by_cases h : s < t <;> simp [orderedOnsiteDirected,mem_Iio,h]
    simp only [he,orderedOnsiteSolution,intervalIntegral.integral_of_le (ha.trans hb),intervalIntegral.integral_of_le ha,
      setIntegral_indicator measurableSet_Iio]
    have hs : Ioc a b ∩ Iio t = Ioo a t := by
      ext s; simp only [mem_inter_iff,mem_Ioc,mem_Iio,mem_Ioo]; constructor <;> rintro ⟨h,k⟩
      · exact ⟨h.1,k⟩
      · exact ⟨⟨h,k.le.trans hb⟩,k⟩
    rw [hs,←integral_Ioc_eq_integral_Ioo]
  · have he (s : ℝ) : orderedOnsiteDirected m q A false t s*f s =
        -((Ioi t).indicator (fun s => orderedOnsiteKernel (-m) q A t s*f s) s) := by
      by_cases h : t < s <;> simp [orderedOnsiteDirected,mem_Ioi,h]
    rw [orderedOnsiteSolution,intervalIntegral.integral_symm t b]
    simp only [he,intervalIntegral.integral_of_le (ha.trans hb),intervalIntegral.integral_of_le hb,integral_neg,
      setIntegral_indicator measurableSet_Ioi,Ioc_inter_Ioi,sup_of_le_right ha]

/-- The directed Green kernel times the exact spatial heat density is the
slot weight in the ordered trace, with its temporal Wilson phase restored. -/
theorem orderedOnsite_directed_heat (m q σ : ℝ) (A : ℝ → ℝ) (positive : Bool) (t s : ℝ) (z : Spatial) :
    orderedOnsiteDirected m q A positive t s * (twoBandDisplacementDensity σ z:ℂ) =
      Complex.exp (-Complex.I*(q:ℂ)*((∫ r in s..t, A r):ℝ)) *
        (orderedHopOrientedWeight m σ positive (t-s,z):ℂ) := by
  cases positive <;> simp only [orderedOnsiteDirected,orderedHopOrientedWeight,Bool.false_eq_true,↓reduceIte]
  · by_cases h : t < s
    · simp [h,sub_neg.mpr h,orderedOnsiteKernel,orderedHopDensity,abs_of_neg (sub_neg.mpr h),mul_assoc]
      left
      congr 1
      ring
    · simp [h,show ¬t-s<0 from fun ht => h (sub_neg.mp ht)]
  · by_cases h : s < t
    · simp [h,sub_pos.mpr h,orderedOnsiteKernel,orderedHopDensity,abs_of_pos (sub_pos.mpr h),mul_assoc]
    · simp [h,show ¬0<t-s from fun ht => h (sub_pos.mp ht)]

end UV.SectorPlane
