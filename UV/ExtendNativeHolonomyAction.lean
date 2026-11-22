import UV.ExtendNativeHolonomyResponse
import UV.ScalarSubtraction

/-! The linear and contact vertices of the same quadratic normal action.
The heat comparison combines the two full Hessians before proper-time
integration and retains the exact two-line carrier Gaussian. -/

noncomputable section
open MeasureTheory Set

namespace UV.ExtendNativeHolonomy

variable {E : Type} [NormedAddCommGroup E]

def normalModeMass (C : NormalCircle E) (n : ℤ) (θ : ℝ) : ℝ :=
  C.mass ^ 2 + (modeNumber C n + θ / C.length) ^ 2

def linearNormalVertex (C : NormalCircle E) (n : ℤ) : ℝ :=
  2 * modeNumber C n / C.length

def contactNormalVertex (C : NormalCircle E) : ℝ := 2 / C.length ^ 2

theorem modeMass_derivative (C : NormalCircle E) (n : ℤ) (θ : ℝ) :
    HasDerivAt (normalModeMass C n)
      (2 * (modeNumber C n + θ / C.length) / C.length) θ := by
  have h := (((hasDerivAt_id θ).div_const C.length).const_add (modeNumber C n)).pow 2
  convert h.const_add (C.mass ^ 2) using 1
  simp only [id_eq]
  ring

theorem linear_and_contact_normal_vertices (C : NormalCircle E) (n : ℤ) :
    deriv (normalModeMass C n) 0 = linearNormalVertex C n ∧
    iteratedDeriv 2 (normalModeMass C n) 0 = contactNormalVertex C := by
  constructor
  · simpa only [linearNormalVertex, zero_div, add_zero] using
      (modeMass_derivative C n 0).deriv
  · have he : deriv (normalModeMass C n) = fun θ =>
        2 * (modeNumber C n + θ / C.length) / C.length := by
      funext θ
      exact (modeMass_derivative C n θ).deriv
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ', iteratedDeriv_one, he]
    have h := ((((hasDerivAt_id (0 : ℝ)).div_const C.length).const_add
      (modeNumber C n)).const_mul 2).div_const C.length
    have hd := h.deriv
    simp only [id_eq] at hd
    rw [hd]
    unfold contactNormalVertex
    ring

/-- The complete two-source comparison after common contact cancellation.
This is the actual bare two-line carrier Gaussian difference at each
normal mass, times the square of its prescribed linear vertex. -/
theorem responseMode_eq_bare_two_time (C : NormalCircle E) (q : UV.ScalarMomentum) (n : ℤ) :
    responseModeProper C q n =
      linearNormalVertex C n ^ 2 *
        (∫ t : ℝ × ℝ, UV.scalarZeroSubtraction (Real.sqrt (normalModeMass C n 0))
          (‖q‖ ^ 2) t ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hM : 0 < normalModeMass C n 0 := by
    unfold normalModeMass
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos C.mass_pos) (sq_nonneg _)
  rw [responseMode_proper_eq_log, ← UV.scalarDepthExtension_zero_proper (M := 0),
    UV.scalarDepthExtension_zero_log (Real.sqrt_pos.mpr hM) (sq_nonneg _) 0,
    UV.scalarFeynmanSubtraction_interval]
  rw [Real.sq_sqrt hM.le]
  unfold responseModeLog normalModeMass linearNormalVertex holonomyFactor curvedFeynmanWidth
  simp only [zero_div, add_zero]
  ring

end UV.ExtendNativeHolonomy
