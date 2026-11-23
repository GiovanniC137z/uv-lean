import UV.ContinueWilsonShellRotation
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Slicing the genuine Euclidean shell ball in one coordinate and
integrating its parabolic disk cross-section against the angular phase. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped RealInnerProductSpace ENNReal

namespace UV

abbrev NormalBall (n : ℕ) := EuclideanSpace ℝ (Fin n)

def normalBallJoin {n : ℕ} (t : ℝ) (y : NormalBall n) : NormalBall (n+1) :=
  WithLp.toLp 2 (Fin.cons t (WithLp.ofLp y))

theorem normal_ball_join_norm {n : ℕ} (t : ℝ) (y : NormalBall n) :
    ‖normalBallJoin t y‖^2 = t^2+‖y‖^2 := by
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,EuclideanSpace.norm_sq_eq]
  simp only [normalBallJoin,Real.norm_eq_abs,sq_abs]
  rfl

private def normalBallSplit (n : ℕ) : NormalBall (n+1) ≃ᵐ ℝ × NormalBall n :=
  (EuclideanSpace.measurableEquiv (Fin (n+1))).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (EuclideanSpace.measurableEquiv (Fin n)).symm))

private theorem normal_ball_split_preserving (n : ℕ) : MeasurePreserving (normalBallSplit n) volume volume :=
  ((MeasurePreserving.id (μ := (volume : Measure ℝ))).prod
    ((EuclideanSpace.volume_preserving_measurableEquiv (Fin n)).symm _)).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).comp
    (EuclideanSpace.volume_preserving_measurableEquiv (Fin (n+1))))

private theorem normal_ball_split_inverse {n : ℕ} (t : ℝ) (y : NormalBall n) :
    (normalBallSplit n).symm (t,y) = normalBallJoin t y := by
  change WithLp.toLp 2 ((0 : Fin (n+1)).insertNth (α := fun _ => ℝ) t (fun i : Fin n => y i)) = _
  rw [Fin.insertNth_zero']; rfl

theorem normal_ball_slice {n : ℕ} {R : ℝ} (hR : 0 ≤ R) (f : NormalBall (n+1) → ℂ) (hf : Continuous f) :
    (∫ x in ball 0 R, f x) = ∫ t in Ioo (-R) R, ∫ y in ball 0 (Real.sqrt (R^2-t^2)), f (normalBallJoin t y) := by
  let A : Set (NormalBall (n+1)) := ball 0 R
  let g := A.indicator f
  have hi : Integrable g := (integrable_indicator_iff measurableSet_ball).mpr
    ((hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set ball_subset_closedBall)
  let e := normalBallSplit n
  have he := (normal_ball_split_preserving n).symm e
  rw [←integral_indicator measurableSet_ball]
  change (∫ x, g x) = _
  rw [←he.integral_comp e.symm.measurableEmbedding g,Measure.volume_eq_prod ℝ (NormalBall n),
    integral_prod (fun z => g (e.symm z)) (he.integrable_comp_of_integrable hi),←integral_indicator measurableSet_Ioo]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Ioo (-R) R
  · rw [indicator_of_mem ht,←integral_indicator measurableSet_ball]
    have hsq : 0 < R^2-t^2 := by nlinarith [mul_pos (sub_pos.mpr ht.2) (by linarith [ht.1] : 0 < R+t)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only [e]
    rw [normal_ball_split_inverse]
    have hy : normalBallJoin t y ∈ A ↔ y ∈ ball 0 (Real.sqrt (R^2-t^2)) := by
      change ‖normalBallJoin t y-0‖ < R ↔ ‖y-0‖ < _
      rw [sub_zero,sub_zero,Real.lt_sqrt (norm_nonneg _)]
      constructor <;> intro h <;> nlinarith [normal_ball_join_norm t y,norm_nonneg (normalBallJoin t y),norm_nonneg y]
    dsimp only [g]
    by_cases hy' : normalBallJoin t y ∈ A
    · rw [indicator_of_mem hy',indicator_of_mem (hy.mp hy')]
    · rw [indicator_of_notMem hy',indicator_of_notMem (mt hy.mpr hy')]
  · rw [indicator_of_notMem ht]
    apply integral_eq_zero_of_ae
    refine Eventually.of_forall fun y => ?_
    dsimp only [e]
    rw [normal_ball_split_inverse]
    apply indicator_of_notMem
    intro hy
    have hy' : ‖normalBallJoin t y‖ < R := by simpa only [A,mem_ball,dist_zero_right] using hy
    apply ht
    constructor <;> nlinarith [normal_ball_join_norm t y,sq_nonneg ‖y‖,norm_nonneg (normalBallJoin t y)]

/-- The disk cross-section of a three-ball is quadratic. The primitive
exhibits the inverse-square Fourier decay including both interval ends. -/
theorem normal_parabolic_fourier_bound {R a : ℝ} (hR : 0 ≤ R) (hR' : R ≤ 1) (ha : 1 ≤ a) :
    ‖∫ t in Ioo (-R) R, (((R:ℂ)^2-(t:ℂ)^2)*Complex.exp ((Complex.I*(a:ℂ))*(t:ℂ)))‖ ≤ 8/(a^2) := by
  let c := Complex.I*(a:ℂ)
  have ha' : 0 < a := by linarith
  have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ha'.ne')
  let H := fun z : ℂ => ((R:ℂ)^2-z^2)*c⁻¹+2*z*c⁻¹^2-2*c⁻¹^3
  let F := fun z : ℂ => H z*Complex.exp (c*z)
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => F s) (((R:ℂ)^2-(t:ℂ)^2)*Complex.exp (c*t)) t := by
    have hz := hasDerivAt_id (t:ℂ)
    have hp := ((((hasDerivAt_const _ ((R:ℂ)^2)).sub (hz.pow 2)).mul_const c⁻¹).add
      ((hz.const_mul 2).mul_const (c⁻¹^2))).sub_const (2*c⁻¹^3)
    have h := (hp.mul (hz.const_mul c).cexp).comp_ofReal
    convert h using 1
    dsimp [H,id]
    field_simp [hc]
    ring
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (by linarith : -R ≤ R),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (by apply Continuous.intervalIntegrable; fun_prop)]
  have hcabs : ‖c‖ = a := by simp [c,abs_of_pos ha']
  have hp (t : ℝ) (ht : |t| = R) : ‖F t‖ ≤ 4/(a^2) := by
    have ht2 : (R:ℂ)^2=(t:ℂ)^2 := by exact_mod_cast (show R^2=t^2 by rw [←ht,sq_abs])
    have hexp : ‖Complex.exp (c*(t:ℂ))‖ = 1 := by simp [c,Complex.norm_exp,Complex.mul_re]
    change ‖(((R:ℂ)^2-(t:ℂ)^2)*c⁻¹+2*(t:ℂ)*c⁻¹^2-2*c⁻¹^3)*Complex.exp (c*(t:ℂ))‖ ≤ _
    rw [norm_mul,hexp,mul_one,sub_eq_zero.mpr ht2,zero_mul,zero_add]
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,ht,hcabs,Complex.norm_ofNat]
    have h1 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha'.le
    have h2 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
    have h3 : a⁻¹^3 ≤ a⁻¹^2 := by nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg a⁻¹)]
    rw [div_eq_mul_inv,←inv_pow]
    nlinarith [mul_le_mul_of_nonneg_right hR' (sq_nonneg a⁻¹)]
  exact (norm_sub_le _ _).trans ((add_le_add (hp R (abs_of_nonneg hR)) (hp (-R) (by simp [abs_of_nonneg hR]))).trans_eq (by ring))

end UV
