import UV.ContinueTransverseKinematicsJacobian
import UV.ExtendStablePole
import UV.EvenDescent

/-! At the equal-positive-mass rest threshold the two shifted scalar
shells meet at zero spatial radius. The axial factors below retain both
evolution signs in one locked sector plane and one common height. -/

noncomputable section

namespace UV.SectorPlane

open Complex

variable {E : Type*} [NormedAddCommGroup E]

/-- Positive-real-part root for the axial factors of a shifted threshold
shell. Its imaginary part keeps the signed height of that line. -/
def Plane.restThresholdRoot (diamond : Plane E) (ε : Evolution) (h : Height)
    (m r : ℝ) : ℂ :=
  principalSqrt ((↑(m ^ 2 + r ^ 2) : ℂ) - I * ↑(diamond.eta ε * (h : ℝ)))

theorem Plane.rest_threshold_root_sq (diamond : Plane E) (ε : Evolution) (h : Height)
    (m r : ℝ) :
    diamond.restThresholdRoot ε h m r ^ 2 =
      (↑(m ^ 2 + r ^ 2) : ℂ) - I * ↑(diamond.eta ε * (h : ℝ)) :=
  principalSqrt_sq _

theorem Plane.rest_threshold_root_re_lower (diamond : Plane E) (ε : Evolution) (h : Height)
    (m r : ℝ) :
    Real.sqrt (m ^ 2 + r ^ 2) ≤ (diamond.restThresholdRoot ε h m r).re := by
  unfold Plane.restThresholdRoot
  have hl := principalSqrt_re_lower ((↑(m ^ 2 + r ^ 2) : ℂ) - I * ↑(diamond.eta ε * (h : ℝ)))
  simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using hl

theorem Plane.rest_threshold_root_re_pos (diamond : Plane E) (ε : Evolution) (h : Height)
    {m : ℝ} (hm : 0 < m) (r : ℝ) : 0 < (diamond.restThresholdRoot ε h m r).re :=
  lt_of_lt_of_le (Real.sqrt_pos.2 (by positivity)) (diamond.rest_threshold_root_re_lower ε h m r)

theorem Plane.rest_threshold_root_im (diamond : Plane E) (ε : Evolution) (h : Height)
    {m : ℝ} (hm : 0 < m) (r : ℝ) :
    (diamond.restThresholdRoot ε h m r).im =
      -(diamond.eta ε * (h : ℝ)) / (2 * (diamond.restThresholdRoot ε h m r).re) := by
  have hh := congrArg Complex.im (diamond.rest_threshold_root_sq ε h m r)
  rw [pow_two, Complex.mul_im] at hh
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, zero_sub] at hh
  have hp := diamond.rest_threshold_root_re_pos ε h hm r
  apply (eq_div_iff (by positivity : 2 * (diamond.restThresholdRoot ε h m r).re ≠ 0)).mpr
  linarith only [hh, mul_comm (diamond.restThresholdRoot ε h m r).re
    (diamond.restThresholdRoot ε h m r).im, show (diamond.restThresholdRoot ε h m r).im *
    (2 * (diamond.restThresholdRoot ε h m r).re) = 2 *
      ((diamond.restThresholdRoot ε h m r).im * (diamond.restThresholdRoot ε h m r).re) by ring]

def Plane.restThresholdNearPlus (diamond : Plane E) (ε : Evolution) (h : Height)
    (m r : ℝ) : ℂ := diamond.restThresholdRoot ε h m r - (m : ℂ)

def Plane.restThresholdNearMinus (diamond : Plane E) (ε : Evolution) (h : Height)
    (m r : ℝ) : ℂ := (m : ℂ) - diamond.restThresholdRoot ε h m r

theorem Plane.rest_threshold_near_plus_factor (diamond : Plane E) (ε : Evolution) (h : Height)
    (m : ℝ) (z : ℝ × ℝ) :
    diamond.shiftedShellCoefficient ε h (restAxialRadialNormals m (2 * m) z).1 =
      ((z.1 : ℂ) - diamond.restThresholdNearPlus ε h m z.2) *
        ((z.1 : ℂ) + (m : ℂ) + diamond.restThresholdRoot ε h m z.2) := by
  rw [Plane.restThresholdNearPlus, show
    ((z.1 : ℂ) - (diamond.restThresholdRoot ε h m z.2 - (m : ℂ))) *
      ((z.1 : ℂ) + (m : ℂ) + diamond.restThresholdRoot ε h m z.2) =
    ((z.1 : ℂ) + (m : ℂ)) ^ 2 - diamond.restThresholdRoot ε h m z.2 ^ 2 by ring,
    diamond.rest_threshold_root_sq]
  simp [Plane.shiftedShellCoefficient, restAxialRadialNormals]
  ring

theorem Plane.rest_threshold_near_minus_factor (diamond : Plane E) (ε : Evolution) (h : Height)
    (m : ℝ) (z : ℝ × ℝ) :
    diamond.shiftedShellCoefficient ε h (restAxialRadialNormals m (2 * m) z).2 =
      ((z.1 : ℂ) - diamond.restThresholdNearMinus ε h m z.2) *
        ((z.1 : ℂ) - (m : ℂ) - diamond.restThresholdRoot ε h m z.2) := by
  rw [Plane.restThresholdNearMinus, show
    ((z.1 : ℂ) - ((m : ℂ) - diamond.restThresholdRoot ε h m z.2)) *
      ((z.1 : ℂ) - (m : ℂ) - diamond.restThresholdRoot ε h m z.2) =
    ((z.1 : ℂ) - (m : ℂ)) ^ 2 - diamond.restThresholdRoot ε h m z.2 ^ 2 by ring,
    diamond.rest_threshold_root_sq]
  simp [Plane.shiftedShellCoefficient, restAxialRadialNormals]
  ring

theorem Plane.rest_threshold_root_tendsto (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) (r : ℝ) :
    Filter.Tendsto (fun h : Height => diamond.restThresholdRoot ε h m r)
      (Filter.comap Subtype.val (nhds (0 : ℝ))) (nhds (↑(Real.sqrt (m ^ 2 + r ^ 2)) : ℂ)) := by
  let w : ℝ → ℂ := fun h => (↑(m ^ 2 + r ^ 2) : ℂ) -
    I * (↑(diamond.eta ε * h) : ℂ)
  have hc : ContinuousAt w 0 := by unfold w; fun_prop
  have hw : w 0 = (↑(m ^ 2 + r ^ 2) : ℂ) := by
    simp only [w, mul_zero, Complex.ofReal_zero, sub_zero]
  have hz : 0 < (w 0).re := by
    rw [hw, Complex.ofReal_re]
    positivity
  have hs : ContinuousAt (principalSqrt ∘ w) 0 :=
    (principalSqrt_differentiableAt hz).continuousAt.comp hc
  have he := hs.tendsto.comp (Filter.tendsto_comap :
    Filter.Tendsto (Subtype.val : Height → ℝ) (Filter.comap Subtype.val (nhds 0)) (nhds 0))
  rw [show (principalSqrt ∘ w) 0 = (↑(Real.sqrt (m ^ 2 + r ^ 2)) : ℂ) by
    rw [Function.comp_apply, hw, principalSqrt_ofReal (by positivity)]] at he
  exact he

end UV.SectorPlane
