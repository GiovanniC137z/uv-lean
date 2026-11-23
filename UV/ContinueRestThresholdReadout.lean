import UV.ContinueRestThresholdRadial
import UV.ContinueShiftedScalar

/-! Exact finite-height disintegration of the original directed scalar
pair at the equal-mass rest threshold, on a strip with fixed running
unit directions. The actual norm-one spatial sphere is retained. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set UV.Carrier
open scoped UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

/-- The two near Cauchy factors after factoring the remote roots. -/
def Plane.restThresholdAxialDifference (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (m : ℝ) (z : ℝ × ℝ) : ℂ :=
  ((z.1 : ℂ) - diamond.restThresholdNearPlus ε₁ h m z.2)⁻¹ -
    ((z.1 : ℂ) - diamond.restThresholdNearMinus ε₂ h m z.2)⁻¹

def Plane.restThresholdRemoteFactor (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (m : ℝ) (z : ℝ × ℝ) : ℂ :=
  (((z.1 : ℂ) + (m : ℂ) + diamond.restThresholdRoot ε₁ h m z.2) *
    ((z.1 : ℂ) - (m : ℂ) - diamond.restThresholdRoot ε₂ h m z.2))⁻¹

/-- The direction and phase of each actual running numerator are
constant throughout the strip. The kernel arguments keep the same
two translated axial slots and common positive vectorial height. -/
def Plane.restThresholdKernelProduct (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ m : ℝ) (z : ℝ × ℝ) : ℂ :=
  (diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) *
    (diamond.scalarKernelReadout ε₁ a₁ φ₁ h ((z.1 + m) ^ 2 - z.2 ^ 2) *
      diamond.scalarKernelReadout ε₂ a₂ φ₂ h ((z.1 - m) ^ 2 - z.2 ^ 2))

theorem Plane.rest_threshold_kernel_product_continuous (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {φ₁ φ₂ : ℂ → ℂ} (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂)
    (a₁ a₂ m : ℝ) :
    Continuous (diamond.restThresholdKernelProduct ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m) := by
  unfold Plane.restThresholdKernelProduct Plane.scalarKernelReadout Plane.shiftedShellCoefficient
  fun_prop

theorem Plane.rest_threshold_kernel_product_eq (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ : ℝ) {m : ℝ} (hm : 0 < m)
    (q : MassiveMomentum) (hq : |q.1| ≤ m / 2) :
    diamond.restThresholdKernelProduct ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m (q.1, ‖q.2‖) =
      diamond.shiftedScalarNumerator ε₁ ε₂ h φ₁ φ₂ a₁ a₂
        (axialTransfer m) (axialTransfer (-m)) q := by
  have hs := threshold_axial_signs hm hq
  simp only [Plane.restThresholdKernelProduct, Plane.shiftedScalarNumerator,
    axial_transfer_coordinates, Prod.fst_add, Prod.snd_add, add_zero, shellSquare,
    ← sub_eq_add_neg, axialSign, if_pos hs.1, if_neg hs.2.not_gt, if_pos hs.2,
    Complex.ofReal_one, Complex.ofReal_neg, mul_one]
  ring

private theorem cone_spatial_mean_mul_radial (f : MassiveMomentum → ℂ) (k : (ℝ × ℝ) → ℂ)
    (z : ℝ × ℝ) (hz : 0 ≤ z.2) :
    coneSpatialMean (fun q => f q * k (q.1, ‖q.2‖)) z = coneSpatialMean f z * k z := by
  have H (ω : ConeSpatialSphere) : ‖z.2 • (ω : Spatial)‖ = z.2 := by
    rw [norm_smul, cone_spatial_direction_norm ω, mul_one, Real.norm_of_nonneg hz]
  unfold coneSpatialMean
  simp_rw [H, Prod.eta]
  rw [integral_mul_const, smul_mul_assoc]

private theorem rest_threshold_normals_eval (m : ℝ) (q : MassiveMomentum) :
    (shiftedD m (axialTransfer m) q, shiftedD m (axialTransfer (-m)) q) =
    restAxialRadialNormals m (2 * m) (q.1, ‖q.2‖) := by
  simp only [restAxialRadialNormals, show (2 * m) / 2 = m by ring, axial_transfer_coordinates,
    shiftedD, massiveD, shellSquare, Prod.fst_add, Prod.snd_add, add_zero, sub_eq_add_neg]

/-- The original compactly tested pair in one locked plane is the
intrinsic radial integral of the exact partial fractions, with the radial
Jacobian absorbed into the near-pole separation. -/
theorem Plane.rest_threshold_scalar_pairing_radial_of_numerator (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (φ₁ φ₂ : ℂ → ℂ)
    (a₁ a₂ : ℝ) {m : ℝ} (hm : 0 < m)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    {U : ℝ × ℝ → ℂ} (hUc : Continuous U)
    (hU : ∀ q, f q ≠ 0 → U (q.1, ‖q.2‖) =
      diamond.shiftedScalarNumerator ε₁ ε₂ h φ₁ φ₂ a₁ a₂ (axialTransfer m) (axialTransfer (-m)) q) :
    diamond.shiftedScalarPairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m m
      (axialTransfer m) (axialTransfer (-m)) f =
      directed ((4 * Real.pi) • ∫ z in univ ×ˢ Ioi (0 : ℝ),
        coneSpatialMean f z * U z *
          diamond.restThresholdRemoteFactor ε₁ ε₂ h m z *
          diamond.restThresholdRadialCoefficient ε₁ ε₂ h m z.2 *
          diamond.restThresholdAxialDifference ε₁ ε₂ h m z) := by
  let P (z : ℝ × ℝ) := diamond.poleCoefficient ε₁ h (restAxialRadialNormals m (2 * m) z).1 *
    diamond.poleCoefficient ε₂ h (restAxialRadialNormals m (2 * m) z).2
  let n : MassiveMomentum → ℝ × ℝ := fun q => (q.1, ‖q.2‖)
  let F (q : MassiveMomentum) := f q * (U (n q) * P (n q))
  have hPc : Continuous P := by
    have hL (e : Evolution) := diamond.pole_coefficient_continuous e h
    unfold P restAxialRadialNormals
    exact ((hL ε₁).comp (by fun_prop)).mul ((hL ε₂).comp (by fun_prop))
  have hFc : Continuous F :=
    hf.mul ((hUc.mul hPc).comp
      (continuous_fst.prodMk (continuous_norm.comp continuous_snd)))
  have hFs : HasCompactSupport F := hs.mul_right
  have hi : Integrable F := hFc.integrable_of_hasCompactSupport hFs
  have hP (q : MassiveMomentum) :
      P (n q) = diamond.poleCoefficient ε₁ h (shiftedD m (axialTransfer m) q) *
        diamond.poleCoefficient ε₂ h (shiftedD m (axialTransfer (-m)) q) := by
    unfold P n
    rw [← rest_threshold_normals_eval m q]
  have hi' : Integrable (fun q => f q * (U (n q) *
      (diamond.poleCoefficient ε₁ h (shiftedD m (axialTransfer m) q) *
        diamond.poleCoefficient ε₂ h (shiftedD m (axialTransfer (-m)) q)))) := by
    simpa only [F, hP] using hi
  rw [diamond.shifted_scalar_pairing_eq_of_numerator _ _ h φ₁ φ₂ a₁ a₂ m m _ _ hi'
    (fun q hq _ _ => hU q hq)]
  congr 1
  simp_rw [← hP]
  change (∫ q, F q) = _
  rw [cone_axial_spatial_integral hFc hFs]
  congr 1
  refine setIntegral_congr_fun (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi) fun z hz => ?_
  have hr : 0 < z.2 := hz.2
  change z.2 ^ 2 • coneSpatialMean (fun q => f q * (U (n q) * P (n q))) z = _
  change z.2 ^ 2 • coneSpatialMean (fun q => f q * ((fun z => U z * P z) (q.1, ‖q.2‖))) z = _
  rw [cone_spatial_mean_mul_radial f (fun z => U z * P z) z hr.le]
  have hp : P z = diamond.restThresholdRemoteFactor ε₁ ε₂ h m z *
      (diamond.restThresholdNearPlus ε₁ h m z.2 - diamond.restThresholdNearMinus ε₂ h m z.2)⁻¹ *
      diamond.restThresholdAxialDifference ε₁ ε₂ h m z := by
    unfold P Plane.restThresholdRemoteFactor Plane.restThresholdAxialDifference
    rw [diamond.pole_coefficient_eq_inv, diamond.pole_coefficient_eq_inv]
    exact diamond.rest_threshold_product_axial_partial_fractions ε₁ ε₂ h hm z.1 z.2
  rw [hp, Complex.real_smul, Plane.restThresholdRadialCoefficient]
  ring

theorem Plane.rest_threshold_scalar_pairing_radial (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {φ₁ φ₂ : ℂ → ℂ} (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂)
    (a₁ a₂ : ℝ) {m : ℝ} (hm : 0 < m)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (hfStrip : ∀ q, f q ≠ 0 → |q.1| ≤ m / 2) :
    diamond.shiftedScalarPairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m m
      (axialTransfer m) (axialTransfer (-m)) f =
      directed ((4 * Real.pi) • ∫ z in univ ×ˢ Ioi (0 : ℝ),
        coneSpatialMean f z * diamond.restThresholdKernelProduct ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m z *
          diamond.restThresholdRemoteFactor ε₁ ε₂ h m z *
          diamond.restThresholdRadialCoefficient ε₁ ε₂ h m z.2 *
          diamond.restThresholdAxialDifference ε₁ ε₂ h m z) :=
  diamond.rest_threshold_scalar_pairing_radial_of_numerator ε₁ ε₂ h φ₁ φ₂ a₁ a₂ hm hf hs
    (diamond.rest_threshold_kernel_product_continuous ε₁ ε₂ h hφ₁ hφ₂ a₁ a₂ m)
    (fun q hq => diamond.rest_threshold_kernel_product_eq ε₁ ε₂ h φ₁ φ₂ a₁ a₂ hm q (hfStrip q hq))

end UV.SectorPlane
