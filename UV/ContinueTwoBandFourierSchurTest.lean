import UV.ContinueTwoBandFourierKernel

/-! Schur's row/column test with constant weight for a concrete complex
integral operator on a finite slab. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace UV.SectorPlane.SlabKernel

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (K : Bounded X)

omit [IsFiniteMeasure μ] in
private theorem square_norm_integral (f : Lp ℂ 2 μ) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) f f)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)] at h
  simpa only [← norm_sq_eq_re_inner] using h

private theorem row_cauchy (x : X) (f : Lp ℂ 2 μ) :
    ‖∫ y, K.val x y * f y ∂μ‖^2 ≤ (∫ y, ‖K.val x y‖ ∂μ) *
      ∫ y, ‖K.val x y‖*‖f y‖^2 ∂μ := by
  let H := fun y => ‖K.val x y‖
  let u := fun y => Real.sqrt (H y)
  let v := fun y => u y * ‖f y‖
  have hH : Measurable H := (K.measurable.comp (measurable_const.prodMk measurable_id)).norm
  have hu : Measurable u := hH.sqrt
  have hv : Measurable v := hu.mul (Lp.stronglyMeasurable f).measurable.norm
  have huSq (y : X) : (u y)^2 = H y := Real.sq_sqrt (norm_nonneg _)
  have hvSq (y : X) : (v y)^2 = H y*‖f y‖^2 := by unfold v; rw [mul_pow,huSq]
  have hu2 : MemLp u 2 μ := MemLp.of_bound hu.aestronglyMeasurable (Real.sqrt K.bound)
    (ae_of_all _ fun y => by rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]; exact Real.sqrt_le_sqrt (K.bounded _ _))
  have vi : Integrable (fun y => H y*‖f y‖^2) μ :=
    ((Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num)).bdd_mul' hH.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact K.bounded _ _)
  have hv2 : MemLp v 2 μ := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr (by
    simpa only [Real.norm_eq_abs,sq_abs,hvSq] using vi)
  have hpq : (2:ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (f := u) (g := v) hpq
    (ae_of_all μ (fun y => (Real.sqrt_nonneg _ : 0 ≤ u y)))
    (ae_of_all μ (fun y => (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _) : 0 ≤ v y)))
    (show MemLp u (ENNReal.ofReal (2:ℝ)) μ by simpa using hu2)
    (show MemLp v (ENNReal.ofReal (2:ℝ)) μ by simpa using hv2)
  have huv (y) : u y * v y = ‖K.val x y * f y‖ := by
    rw [norm_mul]
    change u y * (u y*‖f y‖) = H y * ‖f y‖
    rw [← huSq y]
    ring
  simp only [huv,Real.rpow_two,huSq,hvSq,← Real.sqrt_eq_rpow] at hcs
  have hpos : 0 ≤ ∫ y, H y ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hpos' : 0 ≤ ∫ y, H y * ‖f y‖^2 ∂μ := integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
  calc
    _ ≤ (Real.sqrt (∫ y,H y ∂μ)*Real.sqrt (∫ y,H y*‖f y‖^2 ∂μ))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((norm_integral_le_integral_norm _).trans hcs) 2
    _ = _ := by rw [mul_pow,Real.sq_sqrt hpos,Real.sq_sqrt hpos']

theorem schur_test {M : ℝ} (hM : 0 ≤ M)
    (hrow : ∀ x, (∫ y, ‖K.val x y‖ ∂μ) ≤ M) (hcol : ∀ y, (∫ x, ‖K.val x y‖ ∂μ) ≤ M) :
    ‖operator μ K‖ ≤ M := by
  apply (operator μ K).opNorm_le_bound hM
  intro f
  let J := fun x y => ‖K.val x y‖*‖f y‖^2
  have hj : Integrable (Function.uncurry J) (μ.prod μ) := by
    apply (((Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num)).comp_snd μ).bdd_mul'
      K.measurable.norm.aestronglyMeasurable
    exact ae_of_all _ fun p => by simpa using K.bounded p.1 p.2
  have hj' : Integrable (fun x => ∫ y, J x y ∂μ) μ := hj.integral_prod_left
  have hpoint : ∀ᵐ x ∂μ, ‖operator μ K f x‖^2 ≤ M*(∫ y, J x y ∂μ) := by
    filter_upwards [operator_coe μ K f] with x hx
    rw [hx]
    exact (row_cauchy μ K x f).trans (mul_le_mul_of_nonneg_right (hrow x)
      (integral_nonneg fun y => mul_nonneg (norm_nonneg _) (sq_nonneg _)))
  have H : ‖operator μ K f‖^2 ≤ M*(M*‖f‖^2) := by
    rw [square_norm_integral μ (operator μ K f), square_norm_integral μ f]
    apply (integral_mono_ae ((Lp.memLp _).integrable_norm_pow (p := 2) (by norm_num)) (hj'.const_mul M) hpoint).trans
    rw [integral_const_mul,integral_integral_swap (f := J) hj,← integral_const_mul M (fun y => ‖f y‖^2)]
    apply mul_le_mul_of_nonneg_left _ hM
    apply integral_mono (hj.swap.integral_prod_left) (((Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num)).const_mul M)
    intro y
    dsimp [J]
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _)
  nlinarith only [H,mul_nonneg hM (norm_nonneg f),norm_nonneg (operator μ K f)]

end UV.SectorPlane.SlabKernel
