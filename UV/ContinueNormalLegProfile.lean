import UV.ContinueNormalRankReadout
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Reality and an explicit positive low-frequency bound for the
actual A4 shell characteristic. This locates a nonvanishing charged
normal mode for every holonomy in the five-dimensional readout. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter Metric UV.SectorPlane
open scoped RealInnerProductSpace ComplexConjugate

namespace UV

variable {ι : Type*} [Fintype ι]

theorem normal_shell_characteristic_continuous : Continuous (normalShellCharacteristic (ι := ι)) := by
  have hc : Continuous (fun z : WilsonBallSpace ι × WilsonBallSpace ι => Complex.exp (Complex.I*(⟪z.1,z.2⟫:ℝ))) := by fun_prop
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun q => (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun q => Eventually.of_forall fun y => by simp [Complex.norm_exp,Complex.mul_re])
    (integrable_const 1)
  exact Eventually.of_forall fun y => (hc.comp (continuous_id.prodMk continuous_const)).tendsto p

theorem normal_shell_characteristic_real (p : WilsonBallSpace ι) :
    ((normalShellCharacteristic p).re : ℂ) = normalShellCharacteristic p := by
  have h : conj (normalShellCharacteristic p) = normalShellCharacteristic (-p) := by
    unfold normalShellCharacteristic
    rw [←integral_conj]
    apply integral_congr_ae (Eventually.of_forall fun y => ?_)
    rw [←Complex.exp_conj,inner_neg_left]
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal,Complex.ofReal_neg,neg_mul,mul_neg]
  rw [normal_shell_characteristic_radial (norm_neg p)] at h
  exact Complex.conj_eq_iff_re.mp h

theorem normal_shell_axis_cosine [DecidableEq ι] (i : ι) (a : ℝ) :
    (normalShellCharacteristic (EuclideanSpace.single i a)).re = ∫ y : WilsonBallSpace ι, Real.cos (a*y i) ∂wilsonBallMeasure ι := by
  let f := fun y : WilsonBallSpace ι => Complex.exp (Complex.I*((⟪EuclideanSpace.single i a,y⟫:ℝ):ℂ))
  have hf : Integrable f (wilsonBallMeasure ι) := (integrable_const (1:ℝ)).mono'
    (show Continuous f by dsimp [f]; fun_prop).aestronglyMeasurable
    (Eventually.of_forall fun y => by simp [f,Complex.norm_exp,Complex.mul_re])
  change (∫ y, f y ∂wilsonBallMeasure ι).re = _
  rw [←RCLike.re_eq_complex_re,←integral_re hf]
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [f,EuclideanSpace.inner_single_left,Complex.exp_re,Complex.mul_re,Complex.mul_im]

theorem normal_shell_positive_pi (hn : 5 ≤ Fintype.card ι) {p : WilsonBallSpace ι} (hp : ‖p‖ ≤ Real.pi) :
    0 < (normalShellCharacteristic p).re := by
  classical
  let μ := wilsonBallMeasure ι
  let a := ‖p‖
  let f := fun (i : ι) (y : WilsonBallSpace ι) => Real.cos (a*y i)
  have hev (i : ι) : (∫ y, f i y ∂μ) = (normalShellCharacteristic p).re := by
    rw [←normal_shell_axis_cosine]
    congr 1
    apply normal_shell_characteristic_radial
    simp [a,EuclideanSpace.norm_single]
  have hi (i) : Integrable (f i) μ := (integrable_const (1:ℝ)).mono'
    (show Continuous (f i) by dsimp [f]; fun_prop).aestronglyMeasurable
    (Eventually.of_forall fun y => Real.abs_cos_le_one _)
  have hs : (∫ y, ∑ i, f i y ∂μ) = (Fintype.card ι:ℝ)*(normalShellCharacteristic p).re := by
    rw [integral_finset_sum _ (fun i _ => hi i)]
    simp only [hev,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hb : ∀ᵐ y ∂μ, y ∈ ball (0:WilsonBallSpace ι) 1 := ae_cond_mem measurableSet_ball
  have hbound : ∀ᵐ y ∂μ, (Fintype.card ι:ℝ)-a^2/2 ≤ ∑ i, f i y := by
    filter_upwards [hb] with y hy
    have hy' : ‖y‖ < 1 := by simpa using hy
    have hy2 : ∑ i, (y i)^2 ≤ 1 := by
      have he := EuclideanSpace.norm_sq_eq y
      simp only [Real.norm_eq_abs,sq_abs] at he
      nlinarith [norm_nonneg y]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun (i : ι) _ => Real.one_sub_sq_div_two_le_cos (x := a*y i))
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,mul_pow,
      ←Finset.sum_div,←Finset.mul_sum] at h
    exact le_trans (by nlinarith [mul_le_mul_of_nonneg_left hy2 (sq_nonneg a)]) h
  have hh := integral_mono_ae (integrable_const ((Fintype.card ι:ℝ)-a^2/2)) (integrable_finset_sum _ (fun i _ => hi i)) hbound
  rw [hs,integral_const] at hh
  simp only [measureReal_univ_eq_one,one_smul] at hh
  have hN : (5:ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hp2 : a^2 < 10 := by nlinarith [mul_self_le_mul_self (norm_nonneg p) hp,Real.pi_lt_d2,Real.pi_pos]
  have hpos : 0 < (Fintype.card ι:ℝ)*(normalShellCharacteristic p).re := by linarith
  exact pos_of_mul_pos_right hpos (by positivity : (0:ℝ) ≤ Fintype.card ι)

/-- A nearest shifted mode has dimensionless normal momentum at most π. -/
theorem normal_nearest_holonomy (θ : ℝ) : ∃ j : ℤ, |2*Real.pi*(j:ℝ)+θ| ≤ Real.pi := by
  let a := θ/(2*Real.pi)
  refine ⟨-round a,?_⟩
  have h : 2*Real.pi*((-round a:ℤ):ℝ)+θ = 2*Real.pi*(a-(round a:ℝ)) := by
    dsimp [a]; push_cast; field_simp; ring
  rw [h,abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
  exact (mul_le_mul_of_nonneg_left (abs_sub_round a) (by positivity)).trans_eq (by ring)

end UV
