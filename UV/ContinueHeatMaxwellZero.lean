import UV.ContinueHeatMaxwellLoopInputs
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! At zero external transfer the bubble plus direct contact is a single
transverse momentum derivative. Haar integration gives exact cancellation. -/

noncomputable section
open MeasureTheory Set Metric Real UV.SectorPlane UV.RelativeSoft
open scoped RealInnerProductSpace Topology
namespace UV.HeatMaxwell

private abbrev K := EuclideanPlaneMomentum
local instance heatZeroSectorMeasurable : MeasurableSpace K := borel _
local instance heatZeroSectorBorel : BorelSpace K := ⟨rfl⟩

theorem heat_chord_marks_zero (k : K) :
    heatFirstChord k 0 = heatFirstLocal k 0 ∧ heatContactChord k 0 = heatContactLocal k 0 := by
  constructor
  · simp [heatFirstChord,heatChordMoment,Measure.real,Real.volume_Ioc]
    norm_num
  · have hu : heatUnitLaw univ = 1 := by norm_num [heatUnitLaw,Real.volume_Ioc]
    have hp : heatContactLaw univ = 1 := by rw [←univ_prod_univ,Measure.prod_prod,hu,one_mul]
    simp [heatContactChord,heatChordMoment,Measure.real,hp]

private def heatZeroPrimitive (m : ℝ) (k : K) :=
  -⟪heatSymbol k,heatFirstChord k 0⟫ / (‖heatSymbol k‖^2+m^2)

theorem heat_zero_is_directional_derivative {m : ℝ} (hm : 0<m) (k : K) :
    HasLineDerivAt ℝ (heatZeroPrimitive m) (heatNativeResponse m k 0) k softTransverse.val := by
  let v := softTransverse.val
  let H := fun t : ℝ => heatSymbol (k+t • v)
  have hL : ContDiff ℝ 2 (fun t : ℝ => k+t • v) := by fun_prop
  have hH : ContDiff ℝ 2 H := (hL.norm_sq ℝ).neg.exp.smul hL
  have hH' : ContDiff ℝ 1 (deriv H) := hH.deriv'
  have h₁ := (hH.differentiable (by norm_num) 0).hasDerivAt
  have h₂ := (hH'.differentiable (by norm_num) 0).hasDerivAt
  have hlocal (s : ℝ) : heatFirstChord (k+s • v) 0 = deriv H s := by
    rw [(heat_chord_marks_zero _).1]
    unfold heatFirstLocal
    simp only [zero_smul,add_zero]
    have he : (fun t : ℝ => heatSymbol (k+s • v+t • softTransverse.val)) = fun t => H (s+t) := by
      funext t; simp only [H,v,add_smul,add_assoc]
    rw [he,deriv_comp_const_add,add_zero]
  have hW : heatContactChord k 0 = deriv (deriv H) 0 := by
    rw [(heat_chord_marks_zero _).2]; simp [heatContactLocal,H,v]
  have hD : HasDerivAt (fun t => ‖H t‖^2+m^2) (2*⟪H 0,deriv H 0⟫) 0 := by
    have hh := (h₁.inner ℝ h₁).add_const (m^2)
    simpa only [real_inner_self_eq_norm_sq,real_inner_comm (deriv H 0) (H 0),two_mul] using hh
  have hd : ‖H 0‖^2+m^2 ≠ 0 := by positivity
  have h := (h₁.inner ℝ h₂).neg.div hD hd
  change HasDerivAt (fun t : ℝ => -⟪H t,heatFirstChord (k+t • v) 0⟫/(‖H t‖^2+m^2)) _ 0
  simp_rw [hlocal]
  convert h using 1
  have hV : heatFirstChord k 0 = deriv H 0 := by simpa using hlocal 0
  have h0 : heatSymbol k=H 0 := by simp [H]
  simp only [heatNativeResponse,neg_zero,zero_div,zero_smul,add_zero,h0,hV,hW,real_inner_self_eq_norm_sq,Pi.neg_apply]
  field_simp
  ring

private theorem heat_zero_primitive_integrable {m : ℝ} (hm : 0<m) : Integrable (heatZeroPrimitive m) := by
  have hi := heat_first_chord_integrable (t := 0) (by norm_num)
  have hc : Continuous heatSymbol := by unfold heatSymbol; fun_prop
  have hc' : Continuous (fun k => (‖heatSymbol k‖^2+m^2)⁻¹) :=
    ((hc.norm.pow 2).add continuous_const).inv₀ (fun _ => by positivity)
  have hg : AEStronglyMeasurable (heatZeroPrimitive m) volume := by
    unfold heatZeroPrimitive
    simp_rw [div_eq_mul_inv]
    exact (hc.aestronglyMeasurable.inner hi.aestronglyMeasurable).neg.mul hc'.aestronglyMeasurable
  apply (hi.norm.const_mul ((2*m)⁻¹)).mono' hg
  filter_upwards with k
  let h := heatSymbol k
  let v := heatFirstChord k 0
  have hd : 0<‖h‖^2+m^2 := by positivity
  change ‖-⟪h,v⟫ / (‖h‖^2 + m^2)‖ ≤ (2*m)⁻¹ * ‖v‖
  rw [Real.norm_eq_abs,abs_div,abs_neg,abs_of_pos hd,div_le_iff₀ hd]
  apply (abs_real_inner_le_norm h v).trans
  have ha : ‖h‖*(2*m) ≤ ‖h‖^2+m^2 := by nlinarith [sq_nonneg (‖h‖-m)]
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right ha (norm_nonneg v)]

/-- The unit transverse translation annihilates the entire zero-transfer
response after both native marks have been summed. -/
theorem heat_native_zero_integral {m : ℝ} (hm : 0<m) : (∫ k : K, heatNativeResponse m k 0) = 0 := by
  have hi := heat_native_response_integrable hm (t := 0) (by norm_num)
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := (volume : Measure K))
    (f := fun _ : K => (1:ℝ)) (f' := fun _ => (0:ℝ))
    (g := heatZeroPrimitive m) (g' := fun k => heatNativeResponse m k 0)
    (v := softTransverse.val) (B := ContinuousLinearMap.mul ℝ ℝ)
    (by simp)
    (by simpa using hi) (by simpa using heat_zero_primitive_integrable hm)
    (fun _ => hasDerivAt_const _ _) (heat_zero_is_directional_derivative hm)
  simpa using h

end UV.HeatMaxwell
