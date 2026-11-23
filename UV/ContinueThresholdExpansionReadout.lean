import UV.ContinueThresholdExpansionGeometry

/-! Exact partial fractions of the unequal-mass scalar pair and its
disintegration over the actual normalized spatial sphere. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set UV.Carrier
open scoped UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.unequal_threshold_translate_pairing (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ m₁ m₂ : ℝ) (f : MassiveMomentum → ℂ) :
    diamond.shiftedScalarPairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂
        (axialTransfer ((m₁ + m₂) / 2)) (axialTransfer (-((m₁ + m₂) / 2))) f =
      diamond.shiftedScalarPairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂
        (axialTransfer m₁) (axialTransfer (-m₂)) (fun q => f (q + thresholdRestCenter m₁ m₂)) := by
  unfold Plane.shiftedScalarPairing
  have hvol : MeasurePreserving (fun q : MassiveMomentum => q + thresholdRestCenter m₁ m₂)
      volume volume := by
    have he : (fun q : MassiveMomentum => q + thresholdRestCenter m₁ m₂) =
        Prod.map (fun x : ℝ => x + (m₁ - m₂) / 2) (id : Spatial → Spatial) := by
      funext q
      apply Prod.ext
      · simp [thresholdRestCenter, axial_transfer_coordinates, Prod.fst_add]
      · simp [thresholdRestCenter, axial_transfer_coordinates, Prod.snd_add]
    rw [he]
    exact (measurePreserving_add_right (volume : Measure ℝ) ((m₁ - m₂) / 2)).prod
      (MeasurePreserving.id (volume : Measure Spatial))
  rw [← hvol.integral_comp (Homeomorph.addRight (thresholdRestCenter m₁ m₂)).measurableEmbedding]
  simp only [threshold_rest_translate_plus, threshold_rest_translate_minus]

def unequalThresholdNormals (m₁ m₂ : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((z.1 + m₁) ^ 2 - z.2 ^ 2 - m₁ ^ 2, (z.1 - m₂) ^ 2 - z.2 ^ 2 - m₂ ^ 2)

theorem unequal_threshold_normals_eval (m₁ m₂ : ℝ) (q : MassiveMomentum) :
    (shiftedD m₁ (axialTransfer m₁) q, shiftedD m₂ (axialTransfer (-m₂)) q) =
      unequalThresholdNormals m₁ m₂ (q.1, ‖q.2‖) := by
  simp [unequalThresholdNormals, axial_transfer_coordinates, shiftedD, massiveD, shellSquare, sub_eq_add_neg]

def Plane.unequalThresholdRemoteFactor (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (m₁ m₂ : ℝ) (z : ℝ × ℝ) : ℂ :=
  (((z.1 : ℂ) + (m₁ : ℂ) + diamond.restThresholdRoot ε₁ h m₁ z.2) *
    ((z.1 : ℂ) - (m₂ : ℂ) - diamond.restThresholdRoot ε₂ h m₂ z.2))⁻¹

def Plane.unequalThresholdAxialDifference (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (m₁ m₂ : ℝ) (z : ℝ × ℝ) : ℂ :=
  ((z.1 : ℂ) - diamond.restThresholdNearPlus ε₁ h m₁ z.2)⁻¹ -
    ((z.1 : ℂ) - diamond.restThresholdNearMinus ε₂ h m₂ z.2)⁻¹

theorem Plane.unequal_threshold_product_axial_partial_fractions (diamond : Plane E)
    (ε₁ ε₂ : Evolution) (h : Height) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (z : ℝ × ℝ) :
    diamond.poleCoefficient ε₁ h (unequalThresholdNormals m₁ m₂ z).1 *
      diamond.poleCoefficient ε₂ h (unequalThresholdNormals m₁ m₂ z).2 =
      diamond.unequalThresholdRemoteFactor ε₁ ε₂ h m₁ m₂ z *
        (diamond.unequalThresholdNearGap ε₁ ε₂ h m₁ m₂ z.2)⁻¹ *
        diamond.unequalThresholdAxialDifference ε₁ ε₂ h m₁ m₂ z := by
  have he (m : ℝ) : 2 * m / 2 = m := by ring
  have h₁ : (unequalThresholdNormals m₁ m₂ z).1 = (restAxialRadialNormals m₁ (2 * m₁) z).1 := by
    simp only [unequalThresholdNormals, restAxialRadialNormals, he]
  have h₂ : (unequalThresholdNormals m₁ m₂ z).2 = (restAxialRadialNormals m₂ (2 * m₂) z).2 := by
    simp only [unequalThresholdNormals, restAxialRadialNormals, he]
  rw [h₁, h₂, diamond.pole_coefficient_eq_inv, diamond.pole_coefficient_eq_inv,
    diamond.rest_threshold_near_plus_factor, diamond.rest_threshold_near_minus_factor]
  let a := diamond.restThresholdNearPlus ε₁ h m₁ z.2
  let b := diamond.restThresholdNearMinus ε₂ h m₂ z.2
  let A := (z.1 : ℂ) + (m₁ : ℂ) + diamond.restThresholdRoot ε₁ h m₁ z.2
  let B := (z.1 : ℂ) - (m₂ : ℂ) - diamond.restThresholdRoot ε₂ h m₂ z.2
  have hd : a - b ≠ 0 := diamond.unequal_threshold_gap_ne_zero ε₁ ε₂ h hm₁ hm₂ z.2
  have ha : (z.1 : ℂ) - a ≠ 0 := fun hz => by
    have hi := congrArg Complex.im hz
    simp only [a, Plane.restThresholdNearPlus, Complex.sub_im, Complex.ofReal_im,
      sub_zero, zero_sub, Complex.zero_im, neg_eq_zero] at hi
    exact diamond.rest_threshold_root_im_ne_zero ε₁ h hm₁ z.2 hi
  have hb : (z.1 : ℂ) - b ≠ 0 := fun hz => by
    have hi := congrArg Complex.im hz
    simp only [b, Plane.restThresholdNearMinus, Complex.sub_im, Complex.ofReal_im,
      zero_sub, neg_neg, Complex.zero_im] at hi
    exact diamond.rest_threshold_root_im_ne_zero ε₂ h hm₂ z.2 hi
  change (((z.1 : ℂ) - a) * A)⁻¹ * (((z.1 : ℂ) - b) * B)⁻¹ = (A * B)⁻¹ * (a - b)⁻¹ *
    (((z.1 : ℂ) - a)⁻¹ - ((z.1 : ℂ) - b)⁻¹)
  rw [inv_sub_inv ha hb, show (z.1 : ℂ) - b - ((z.1 : ℂ) - a) = a - b by ring]
  simp only [div_eq_mul_inv, mul_inv]
  calc
    _ = A⁻¹ * B⁻¹ * ((a - b)⁻¹ * (a - b)) * (((z.1 : ℂ) - a)⁻¹ * ((z.1 : ℂ) - b)⁻¹) := by
      rw [inv_mul_cancel₀ hd, mul_one]
      ring
    _ = _ := by ring

private theorem threshold_sphere_mean_mul_radial (f : MassiveMomentum → ℂ) (k : (ℝ × ℝ) → ℂ)
    (z : ℝ × ℝ) (hz : 0 ≤ z.2) :
    coneSpatialMean (fun q => f q * k (q.1, ‖q.2‖)) z = coneSpatialMean f z * k z := by
  have H (w : ConeSpatialSphere) : ‖z.2 • (w : Spatial)‖ = z.2 := by
    rw [norm_smul, cone_spatial_direction_norm w, mul_one, Real.norm_of_nonneg hz]
  unfold coneSpatialMean
  simp_rw [H, Prod.eta]
  rw [integral_mul_const, smul_mul_assoc]

/-- Finite-height unequal scalar pair against the original compact test,
with the compensated weight and the actual spatial angular measure. -/
theorem Plane.unequal_threshold_pairing_radial_of_numerator (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ : ℝ) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    {U : ℝ × ℝ → ℂ} (hUc : Continuous U)
    (hU : ∀ q, f q ≠ 0 → U (q.1, ‖q.2‖) =
      diamond.shiftedScalarNumerator ε₁ ε₂ h φ₁ φ₂ a₁ a₂ (axialTransfer m₁) (axialTransfer (-m₂)) q) :
    diamond.shiftedScalarPairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂ (axialTransfer m₁) (axialTransfer (-m₂)) f =
      directed ((4 * Real.pi) • ∫ z in univ ×ˢ Ioi (0 : ℝ),
        coneSpatialMean f z * U z * diamond.unequalThresholdRemoteFactor ε₁ ε₂ h m₁ m₂ z *
          diamond.unequalThresholdRadialCoefficient ε₁ ε₂ h m₁ m₂ z.2 *
          diamond.unequalThresholdAxialDifference ε₁ ε₂ h m₁ m₂ z) := by
  let P (z : ℝ × ℝ) := diamond.poleCoefficient ε₁ h (unequalThresholdNormals m₁ m₂ z).1 *
    diamond.poleCoefficient ε₂ h (unequalThresholdNormals m₁ m₂ z).2
  let n : MassiveMomentum → ℝ × ℝ := fun q => (q.1, ‖q.2‖)
  let F (q : MassiveMomentum) := f q * (U (n q) * P (n q))
  have hPc : Continuous P := by
    have hL (e : Evolution) := diamond.pole_coefficient_continuous e h
    unfold P unequalThresholdNormals
    exact ((hL ε₁).comp (by fun_prop)).mul ((hL ε₂).comp (by fun_prop))
  have hFc : Continuous F :=
    hf.mul ((hUc.mul hPc).comp (continuous_fst.prodMk (continuous_norm.comp continuous_snd)))
  have hFs : HasCompactSupport F := hs.mul_right
  have hi : Integrable F := hFc.integrable_of_hasCompactSupport hFs
  have hP (q : MassiveMomentum) :
      P (n q) = diamond.poleCoefficient ε₁ h (shiftedD m₁ (axialTransfer m₁) q) *
        diamond.poleCoefficient ε₂ h (shiftedD m₂ (axialTransfer (-m₂)) q) := by
    unfold P n
    rw [← unequal_threshold_normals_eval m₁ m₂ q]
  have hi' : Integrable (fun q => f q * (U (n q) *
      (diamond.poleCoefficient ε₁ h (shiftedD m₁ (axialTransfer m₁) q) *
        diamond.poleCoefficient ε₂ h (shiftedD m₂ (axialTransfer (-m₂)) q)))) := by
    simpa only [F, hP] using hi
  rw [diamond.shifted_scalar_pairing_eq_of_numerator _ _ h φ₁ φ₂ a₁ a₂ m₁ m₂ _ _ hi'
    (fun q hq _ _ => hU q hq)]
  congr 1
  simp_rw [← hP]
  change (∫ q, F q) = _
  rw [cone_axial_spatial_integral hFc hFs]
  congr 1
  refine setIntegral_congr_fun (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi) fun z hz => ?_
  have hr : 0 < z.2 := hz.2
  change z.2 ^ 2 • coneSpatialMean (fun q => f q * ((fun z => U z * P z) (q.1, ‖q.2‖))) z = _
  rw [threshold_sphere_mean_mul_radial f (fun z => U z * P z) z hr.le]
  have hp := diamond.unequal_threshold_product_axial_partial_fractions ε₁ ε₂ h hm₁ hm₂ z
  change P z = _ at hp
  rw [hp, Complex.real_smul, Plane.unequalThresholdRadialCoefficient, div_eq_mul_inv]
  ring

end UV.SectorPlane
