import UV.VerifyMassiveRunningJump
import UV.VerifyRunningPrimitive

/-! The two separately tested massive boundary sides. The axial sign is
constant in neighborhoods of the massive sheets. Its correction away
from the sheets is integrated in the original four-momentum measure. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

/-- The height is always positive and tends to zero from above. -/
abbrev poleBoundaryHeights : Filter Height :=
  (𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))

theorem pole_height_tendsto_zero :
    Tendsto (fun h : Height => (h : ℝ)) poleBoundaryHeights (𝓝 (0 : ℝ)) :=
  tendsto_comap.mono_right nhdsWithin_le_nhds

theorem Plane.pole_coefficient_off_shell_limit {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε : Evolution) {D : ℝ} (hD : D ≠ 0) :
    Tendsto (fun h : Height => diamond.poleCoefficient ε h D) poleBoundaryHeights
      (𝓝 (D : ℂ)⁻¹) := by
  let Z (t : ℝ) := (D : ℂ) + Complex.I * ((diamond.eta ε * t : ℝ) : ℂ)
  have hZ : Continuous Z := by unfold Z; fun_prop
  have h₀ : Z 0 = (D : ℂ) := by simp [Z]
  have h := (hZ.continuousAt (x := 0)).tendsto.comp pole_height_tendsto_zero
  rw [h₀] at h
  simpa only [Function.comp_apply, Plane.pole_coefficient_eq_inv, Plane.shiftedShellCoefficient, Z]
    using h.inv₀ (Complex.ofReal_ne_zero.mpr hD)

theorem Plane.pole_coefficient_off_shell_bound {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε : Evolution) (h : Height) {D : ℝ} (hD : D ≠ 0) :
    ‖diamond.poleCoefficient ε h D‖ ≤ |D|⁻¹ := by
  have hR := Complex.abs_re_le_norm (diamond.shiftedShellCoefficient ε h D)
  rw [diamond.pole_coefficient_eq_inv, norm_inv]
  exact inv_anti₀ (abs_pos.mpr hD) (by simpa [Plane.shiftedShellCoefficient] using hR)

/-- The PV tested against the running sign, on both axial sheets of
the fixed plane. The second summand is supported away from the pole. -/
def massiveSignedPV (m : ℝ) (f : MassiveMomentum → ℝ) : ℝ :=
  massiveShellPV (m ^ 2 / 4) m (massiveRunningTest m f) +
    ∫ q, (massiveRunningCorrection m q / massiveD m q) * f q

def massiveSignedPoleBoundary (η m : ℝ) (f : MassiveMomentum → ℝ) : ℂ :=
  (massiveSignedPV m f : ℂ) -
    Complex.I * (η : ℂ) * ((Real.pi * massiveSignedShellTest m f : ℝ) : ℂ)

variable {E : Type*} [NormedAddCommGroup E]

private theorem Plane.running_pole_correction_limit (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) {f : MassiveMomentum → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q : MassiveMomentum,
      (massiveRunningCorrection m q : ℂ) * (f q : ℂ) * diamond.poleCoefficient ε h (massiveD m q))
      poleBoundaryHeights (𝓝 ((∫ q, (massiveRunningCorrection m q / massiveD m q) * f q : ℝ) : ℂ)) := by
  let B := (m ^ 2 / 2)⁻¹
  have hb : 0 < m ^ 2 / 2 := by positivity
  rw [← integral_complex_ofReal]
  refine tendsto_integral_filter_of_dominated_convergence
    (l := poleBoundaryHeights) (μ := volume) (fun q => (2 * B) * ‖f q‖) ?_ ?_
    ((hf.integrable_of_hasCompactSupport hs).norm.const_mul _) ?_
  · refine Eventually.of_forall fun h => ?_
    exact (((Complex.continuous_ofReal.measurable.comp (massive_running_correction_measurable hm)).mul
      (Complex.continuous_ofReal.comp hf).measurable).mul
      ((diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)).measurable).aestronglyMeasurable
  · refine Eventually.of_forall fun h => Eventually.of_forall fun q => ?_
    by_cases hz : massiveRunningCorrection m q = 0
    · simp [hz, B]
      positivity
    have hgap := massive_running_correction_gap hm hz
    have hD : massiveD m q ≠ 0 := by
      intro he
      rw [he, abs_zero] at hgap
      exact hb.not_ge hgap
    have hP := (diamond.pole_coefficient_off_shell_bound ε h hD).trans (inv_anti₀ hb hgap)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, mul_right_comm]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (massive_running_correction_norm_le m q) hP (norm_nonneg _) (by norm_num)) (norm_nonneg _)
  · filter_upwards [massiveD_nonzero_ae m] with q hD
    have h := (diamond.pole_coefficient_off_shell_limit ε hD).const_mul
      ((massiveRunningCorrection m q : ℂ) * (f q : ℂ))
    convert h using 2
    push_cast
    ring

/-- The actual massive signed simple pole has a PV and a delta with
the difference of the two axial sheets and their coarea factors. -/
theorem Plane.massive_signed_pole_limit (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) {f : MassiveMomentum → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q : MassiveMomentum, (axialSign q.1 : ℂ) * (f q : ℂ) *
      diamond.poleCoefficient ε h (massiveD m q)) poleBoundaryHeights
      (𝓝 (massiveSignedPoleBoundary (diamond.eta ε) m f)) := by
  obtain ⟨K, hK⟩ := massive_running_test_lipschitz hm hf hs
  have hcs := massive_running_test_hasCompactSupport m hs
  have hb : 0 < m ^ 2 / 4 := by positivity
  have hmb : 2 * (m ^ 2 / 4) ≤ m ^ 2 := by linarith [sq_nonneg m]
  have h₁ := (diamond.bare_massive_pairing_limit ε hb hmb hK hcs).comp
    (tendsto_comap : Tendsto (fun h : Height => (h : ℝ)) poleBoundaryHeights (𝓝[>] (0 : ℝ)))
  rw [massive_running_test_fullShellTest hm] at h₁
  have h₂ := diamond.running_pole_correction_limit ε hm hf.continuous hs
  have hL := h₁.add h₂
  unfold massiveSignedPoleBoundary massiveSignedPV
  rw [Complex.ofReal_add, add_sub_right_comm]
  refine hL.congr fun h => ?_
  dsimp only [Function.comp_apply, Plane.bareMassivePairing]
  rw [dif_pos h.property]
  let P (q : MassiveMomentum) := diamond.poleCoefficient ε h (massiveD m q)
  have hP : Continuous P := (diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)
  have hfc := Complex.continuous_ofReal.comp hf.continuous
  have hfs := hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hi₁ : Integrable (fun q => P q * (massiveRunningTest m f q : ℂ)) :=
    (hP.mul (Complex.continuous_ofReal.comp hK.continuous)).integrable_of_hasCompactSupport
      ((hcs.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_left (f := P))
  have hi₂ : Integrable (fun q => (massiveRunningCorrection m q : ℂ) * (f q : ℂ) * P q) := by
    have hi : Integrable (fun q => (f q : ℂ) * P q) :=
      (hfc.mul hP).integrable_of_hasCompactSupport hfs.mul_right
    have hc := (Complex.continuous_ofReal.measurable.comp
      (massive_running_correction_measurable hm)).aestronglyMeasurable (μ := volume)
    simpa only [mul_assoc] using hi.bdd_mul hc
      ⟨2, fun q => by simpa only [Function.comp_apply, Complex.norm_real] using massive_running_correction_norm_le m q⟩
  rw [← integral_add hi₁ hi₂]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  simp only [massiveRunningCorrection, massiveRunningTest, Complex.ofReal_sub, Complex.ofReal_mul]
  ring

/-- Complex tests use their two real slots with the same side on both. -/
def massiveComplexSignedPoleBoundary (η m : ℝ) (f : MassiveMomentum → ℂ) : ℂ :=
  massiveSignedPoleBoundary η m (fun q => (f q).re) +
    Complex.I * massiveSignedPoleBoundary η m (fun q => (f q).im)

theorem Plane.massive_signed_pole_complex_limit (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) {f : MassiveMomentum → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q : MassiveMomentum,
      runningAxialTest f q * diamond.poleCoefficient ε h (massiveD m q)) poleBoundaryHeights
      (𝓝 (massiveComplexSignedPoleBoundary (diamond.eta ε) m f)) := by
  have hr := diamond.massive_signed_pole_limit ε hm (Complex.reCLM.lipschitz.comp hf)
    (hs.comp_left (g := Complex.re) Complex.zero_re)
  have hi := diamond.massive_signed_pole_limit ε hm (Complex.imCLM.lipschitz.comp hf)
    (hs.comp_left (g := Complex.im) Complex.zero_im)
  refine (hr.add (hi.const_mul Complex.I)).congr fun h => ?_
  let P (q : MassiveMomentum) := diamond.poleCoefficient ε h (massiveD m q)
  have hp : Continuous P := (diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)
  have hInt (p : ℂ → ℝ) (hc : Continuous p) (hz : p 0 = 0) :
      Integrable (fun q => (axialSign q.1 : ℂ) * (p (f q) : ℂ) * P q) := by
    have H := ((Complex.continuous_ofReal.comp (hc.comp hf.continuous)).mul hp).integrable_of_hasCompactSupport
      (μ := volume) ((hs.comp_left hz).comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_right
    simpa only [mul_assoc] using integrable_runningAxialSign_mul measurable_fst H
  change (∫ q, (axialSign q.1 : ℂ) * ((f q).re : ℂ) * P q) +
    Complex.I * (∫ q, (axialSign q.1 : ℂ) * ((f q).im : ℂ) * P q) = _
  rw [← integral_const_mul, ← integral_add (hInt _ Complex.continuous_re Complex.zero_re)
    ((hInt _ Complex.continuous_im Complex.zero_im).const_mul _)]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  simp only [runningAxialTest]
  calc
    _ = (axialSign q.1 : ℂ) * ((f q).re + (f q).im * Complex.I) * P q := by ring
    _ = _ := by rw [Complex.re_add_im]

end UV.SectorPlane
