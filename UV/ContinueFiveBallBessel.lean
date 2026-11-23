import UV.ContinueFiveBallEnergy
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! Radial Fourier equation of the actual polynomial or fractional
power cross-section. All normal-coordinate integrals are over [-1,1].
The boundary terms vanish in the integration by parts. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped Topology

namespace UV

def normalBallSectionWeight (α t : ℝ) := (1-t^2)^α

theorem normal_section_weight_continuous {α : ℝ} (hα : 0 ≤ α) : Continuous (normalBallSectionWeight α) :=
  (continuous_const.sub (continuous_id.pow 2)).rpow_const (fun _ => Or.inr hα)

def normalBallCosine (α a : ℝ) := ∫ t in (-1:ℝ)..1, normalBallSectionWeight α t*Real.cos (a*t)
def normalBallCosineSlope (α a : ℝ) := ∫ t in (-1:ℝ)..1, -t*normalBallSectionWeight α t*Real.sin (a*t)
def normalBallCosineCurvature (α a : ℝ) := ∫ t in (-1:ℝ)..1, -(t^2)*normalBallSectionWeight α t*Real.cos (a*t)

private theorem normal_interval_deriv (F G : ℝ → ℝ → ℝ) (B : ℝ → ℝ)
    (hF : ∀ a, Continuous (F a)) (hG : ∀ a, Continuous (G a)) (hB : Continuous B)
    (hbound : ∀ a t, ‖G a t‖ ≤ B t) (hg : ∀ a t, HasDerivAt (fun b => F b t) (G a t) a) (a : ℝ) :
    HasDerivAt (fun b => ∫ t in (-1:ℝ)..1, F b t) (∫ t in (-1:ℝ)..1, G a t) a :=
  (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := G) (bound := B) (by norm_num : (0:ℝ)<1)
    (Eventually.of_forall fun b => (hF b).aestronglyMeasurable) ((hF a).intervalIntegrable ..)
    (hG a).aestronglyMeasurable (Eventually.of_forall fun t _ b _ => hbound b t) (hB.intervalIntegrable ..)
    (Eventually.of_forall fun t _ b _ => hg b t)).2

theorem normal_ball_cosine_derivatives {α : ℝ} (hα : 0 ≤ α) (a : ℝ) :
    HasDerivAt (normalBallCosine α) (normalBallCosineSlope α a) a ∧
    HasDerivAt (normalBallCosineSlope α) (normalBallCosineCurvature α a) a := by
  let w := normalBallSectionWeight α
  have hw : Continuous w := normal_section_weight_continuous hα
  let F := fun a t : ℝ => w t*Real.cos (a*t)
  let G := fun a t : ℝ => -t*w t*Real.sin (a*t)
  let H := fun a t : ℝ => -(t^2)*w t*Real.cos (a*t)
  have hF (b : ℝ) : Continuous (F b) := by dsimp [F]; fun_prop
  have hG (b : ℝ) : Continuous (G b) := by dsimp [G]; fun_prop
  have hH (b : ℝ) : Continuous (H b) := by dsimp [H]; fun_prop
  constructor
  · apply normal_interval_deriv F G (fun t => |-t*w t|) hF hG (by fun_prop) _ _ a
    · intro b t
      simpa only [G,Real.norm_eq_abs,abs_mul] using mul_le_of_le_one_right (abs_nonneg (-t*w t)) (Real.abs_sin_le_one (b*t))
    · intro b t
      convert ((((hasDerivAt_id b).mul_const t).cos).const_mul (w t)) using 1
      dsimp [G,id]; ring
  · apply normal_interval_deriv G H (fun t => |-(t^2)*w t|) hG hH (by fun_prop) _ _ a
    · intro b t
      change |(-(t^2)*w t)*Real.cos (b*t)| ≤ |-(t^2)*w t|
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · intro b t
      convert ((((hasDerivAt_id b).mul_const t).sin).const_mul (-t*w t)) using 1
      dsimp [H,id]; ring

theorem normal_ball_cosine_ode {α : ℝ} (hα : 0 ≤ α) (a : ℝ) :
    a*(normalBallCosineCurvature α a+normalBallCosine α a)+2*(α+1)*normalBallCosineSlope α a=0 := by
  let w := normalBallSectionWeight α
  let F := fun t : ℝ => w t*Real.cos (a*t)
  let G := fun t : ℝ => -t*w t*Real.sin (a*t)
  let H := fun t : ℝ => -(t^2)*w t*Real.cos (a*t)
  let P := fun t : ℝ => normalBallSectionWeight (α+1) t*Real.sin (a*t)
  let K := fun t : ℝ => a*(H t+F t)+2*(α+1)*G t
  have hw : Continuous w := normal_section_weight_continuous hα
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hH : Continuous H := by dsimp [H]; fun_prop
  have hK : Continuous K := by dsimp [K]; fun_prop
  have hβ : 0 < α+1 := by linarith
  have hd (t : ℝ) (ht : t ∈ uIcc (-1:ℝ) 1) : HasDerivAt P (K t) t := by
    have ht' : t ∈ Icc (-1:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using ht
    have hq : 0 ≤ 1-t^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht'.2) (by linarith [ht'.1] : 0 ≤ t+1)]
    have hdq := (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)
    have hdw := hdq.rpow_const (p := α+1) (Or.inr (by linarith))
    convert hdw.mul (((hasDerivAt_id t).const_mul a).sin) using 1
    dsimp [K,H,F,G,w,normalBallSectionWeight,id]
    rw [add_sub_cancel_right,Real.rpow_add_one' hq hβ.ne']
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hK.intervalIntegrable ..)
  have hend : P 1-P (-1)=0 := by simp [P,normalBallSectionWeight,Real.zero_rpow hβ.ne']
  change a*((∫ t in (-1:ℝ)..1, H t)+(∫ t in (-1:ℝ)..1, F t))+2*(α+1)*(∫ t in (-1:ℝ)..1, G t)=0
  rw [←intervalIntegral.integral_add (hH.intervalIntegrable ..) (hF.intervalIntegrable ..),
    ←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul,
    ←intervalIntegral.integral_add ((continuous_const.mul (hH.add hF)).intervalIntegrable ..) ((continuous_const.mul hG).intervalIntegrable ..)]
  exact he.trans hend

theorem normal_ball_cosine_decay {α : ℝ} (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ≥ 1, |normalBallCosine α a| ≤ C/a^(α+1) :=
  normal_ball_oscillator_energy (by linarith : 1 ≤ α+1) _ _ _ (fun a _ => (normal_ball_cosine_derivatives hα a).1)
    (fun a _ => (normal_ball_cosine_derivatives hα a).2) (fun a _ => normal_ball_cosine_ode hα a)

end UV
