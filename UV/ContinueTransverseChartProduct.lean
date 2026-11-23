import UV.ContinueTransverseChartSubtraction
import UV.MassiveRunningPole

/-! A two-normal boundary on an independent Cartesian shell chart.
Both directed inverses use the same strictly positive height. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

abbrev transverseNormalVolume : Measure (ℝ × ℝ) :=
  (volume : Measure ℝ).prod volume

def transverseNormalPV₂ (f : ℝ × ℝ → ℂ) : ℂ :=
  ∫ p, (p.1 : ℂ)⁻¹ * (p.2 : ℂ)⁻¹ * transverseNormalRemainder f p ∂transverseNormalVolume

def transverseNormalBoundary (η₁ η₂ : ℝ) (f : ℝ × ℝ → ℂ) : ℂ :=
  transverseNormalPV₂ f -
    Complex.I * (Real.pi : ℂ) * (η₂ : ℂ) * complexShellPV (fun x => f (x,0)) -
    Complex.I * (Real.pi : ℂ) * (η₁ : ℂ) * complexShellPV (fun y => f (0,y)) -
    (Real.pi : ℂ)^2 * (η₁ : ℂ) * (η₂ : ℂ) * f (0,0)

theorem transverse_normal_cutoff_pv : complexShellPV transverseNormalCutoff = 0 := by
  simp [complexShellPV, symmetricTest, transverse_normal_cutoff_even]

theorem transverse_normal_slice_compact {f : ℝ × ℝ → ℂ} (hs : HasCompactSupport f) :
    HasCompactSupport (fun x => f (x,0)) ∧ HasCompactSupport (fun y => f (0,y)) := by
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuousOn
    (continuous_id : Continuous (id : ℝ × ℝ → ℝ × ℝ)).continuousOn
  have H (p : ℝ × ℝ) (hp : f p ≠ 0) : ‖p‖ ≤ C := hC p (subset_tsupport f hp)
  constructor
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -C) (b := C))
    intro x hx
    exact abs_le.mp (by simpa [Prod.norm_def, Real.norm_eq_abs] using H (x,0) hx)
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -C) (b := C))
    intro y hy
    exact abs_le.mp (by simpa [Prod.norm_def, Real.norm_eq_abs] using H (0,y) hy)

theorem transverse_normal_coordinates_nonzero_ae :
    ∀ᵐ p ∂transverseNormalVolume, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  have H : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  exact ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).ae H).and
    ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).ae H)

/-- Common-height dominated limit for a mixed remainder, with
the two normal factors already cancelled by the test. -/
theorem transverse_normal_remainder_moving_limit (G : Height → (ℝ × ℝ) → ℂ) (g : ℝ × ℝ → ℂ)
    (K : TopologicalSpace.Compacts (ℝ × ℝ)) {C : ℝ}
    (hGc : ∀ᶠ h in poleBoundaryHeights, Continuous (G h))
    (hGs : ∀ᶠ h in poleBoundaryHeights, ∀ p ∉ K, G h p = 0)
    (hGb : ∀ᶠ h in poleBoundaryHeights, ∀ p, ‖G h p‖ ≤ C * |p.1| * |p.2|)
    (hG : ∀ p, Tendsto (fun h => G h p) poleBoundaryHeights (𝓝 (g p)))
    (P Q : Height → ℝ → ℂ)
    (hPc : ∀ h, Continuous (P h)) (hQc : ∀ h, Continuous (Q h))
    (hPb : ∀ h x, x ≠ 0 → ‖P h x‖ ≤ |x|⁻¹) (hQb : ∀ h x, x ≠ 0 → ‖Q h x‖ ≤ |x|⁻¹)
    (hP : ∀ x, x ≠ 0 → Tendsto (fun h => P h x) poleBoundaryHeights (𝓝 (x : ℂ)⁻¹))
    (hQ : ∀ x, x ≠ 0 → Tendsto (fun h => Q h x) poleBoundaryHeights (𝓝 (x : ℂ)⁻¹)) :
    Tendsto (fun h => ∫ p, P h p.1 * Q h p.2 * G h p ∂transverseNormalVolume) poleBoundaryHeights
      (𝓝 (∫ p, (p.1 : ℂ)⁻¹ * (p.2 : ℂ)⁻¹ * g p ∂transverseNormalVolume)) := by
  let M := (K : Set (ℝ × ℝ)).indicator (fun _ => C)
  have hM : Integrable M transverseNormalVolume :=
    (integrableOn_const (C := C) K.isCompact.measure_lt_top.ne).integrable_indicator K.isCompact.measurableSet
  apply tendsto_integral_filter_of_dominated_convergence M ?_ ?_ hM ?_
  · filter_upwards [hGc] with h hh
    exact ((((hPc h).comp continuous_fst).mul ((hQc h).comp continuous_snd)).mul hh).aestronglyMeasurable
  · filter_upwards [hGs,hGb] with h hs hb
    filter_upwards [transverse_normal_coordinates_nonzero_ae] with p hp
    by_cases hK : p ∈ K
    · dsimp only [M]
      rw [indicator_of_mem hK, norm_mul, norm_mul]
      calc
        _ ≤ (|p.1|⁻¹ * |p.2|⁻¹) * (C * |p.1| * |p.2|) := by
          exact mul_le_mul (mul_le_mul (hPb h _ hp.1) (hQb h _ hp.2) (norm_nonneg _) (by positivity))
            (hb p) (norm_nonneg _) (by positivity)
        _ = C := by
          field_simp [abs_ne_zero.mpr hp.1, abs_ne_zero.mpr hp.2]
    · simp [M, indicator_of_notMem hK, hs p hK]
  · filter_upwards [transverse_normal_coordinates_nonzero_ae] with p hp
    exact ((hP p.1 hp.1).mul (hQ p.2 hp.2)).mul (hG p)

theorem transverse_normal_product_split (P Q : ℝ → ℂ) (hP : Continuous P) (hQ : Continuous Q)
    {f : ℝ × ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    (∫ p, P p.1 * Q p.2 * f p ∂transverseNormalVolume) =
      (∫ p, P p.1 * Q p.2 * transverseNormalRemainder f p ∂transverseNormalVolume) +
      (∫ x, P x * transverseNormalCutoff x) * (∫ y, Q y * f (0,y)) +
      (∫ x, P x * f (x,0)) * (∫ y, Q y * transverseNormalCutoff y) -
      f (0,0) * ((∫ x, P x * transverseNormalCutoff x) *
        (∫ y, Q y * transverseNormalCutoff y)) := by
  obtain ⟨hsx,hsy⟩ := transverse_normal_slice_compact hs
  have hp : Integrable (fun x => P x * transverseNormalCutoff x) :=
    (hP.mul transverse_normal_cutoff_lipschitz.continuous).integrable_of_hasCompactSupport
      (transverse_normal_cutoff_compact.mul_left (f := P))
  have hq : Integrable (fun y => Q y * transverseNormalCutoff y) :=
    (hQ.mul transverse_normal_cutoff_lipschitz.continuous).integrable_of_hasCompactSupport
      (transverse_normal_cutoff_compact.mul_left (f := Q))
  have hx : Integrable (fun x => P x * f (x,0)) :=
    (hP.mul (hf.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
      (hsx.mul_left (f := P))
  have hy : Integrable (fun y => Q y * f (0,y)) :=
    (hQ.mul (hf.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
      (hsy.mul_left (f := Q))
  have hr : Integrable (fun p : ℝ × ℝ => P p.1 * Q p.2 * transverseNormalRemainder f p) transverseNormalVolume :=
    (((hP.comp continuous_fst).mul (hQ.comp continuous_snd)).mul
      (transverse_normal_remainder_continuous hf)).integrable_of_hasCompactSupport
        (transverse_normal_remainder_compact hs).mul_left
  rw [← integral_prod_mul, ← integral_prod_mul, ← integral_prod_mul, ← integral_const_mul]
  have hA := integral_add (hr.add (hp.mul_prod hy)) (hx.mul_prod hq)
  have hS := integral_sub ((hr.add (hp.mul_prod hy)).add (hx.mul_prod hq)) ((hp.mul_prod hq).const_mul (f (0,0)))
  simp only [Pi.add_apply] at hA hS
  rw [← integral_add hr (hp.mul_prod hy), ← hA, ← hS]
  apply integral_congr_ae
  refine Eventually.of_forall fun p => ?_
  simp only [transverseNormalRemainder]
  ring

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.transverse_normal_single_test (diamond : Plane E) (ε : Evolution)
    {g : ℝ → ℂ} {L : ℝ≥0} (hg : LipschitzWith L g) (hs : HasCompactSupport g) :
    Tendsto (fun h : Height => ∫ x, diamond.poleCoefficient ε h x * g x) poleBoundaryHeights
      (𝓝 (complexShellPV g - Complex.I * (Real.pi : ℂ) * (diamond.eta ε : ℂ) * g 0)) := by
  have H := (diamond.tested_pole_coefficient_limit ε hg hs).comp
    (tendsto_comap : Tendsto (fun h : Height => (h : ℝ)) poleBoundaryHeights (𝓝[>] (0 : ℝ)))
  have e : Complex.I * (diamond.eta ε : ℂ) * ((Real.pi : ℂ) * g 0) =
      Complex.I * (Real.pi : ℂ) * (diamond.eta ε : ℂ) * g 0 := by ring
  rw [e] at H
  exact H.congr (fun h => by simp only [Function.comp_apply, dif_pos h.property])

theorem Plane.transverse_normal_cutoff_limit (diamond : Plane E) (ε : Evolution) :
    Tendsto (fun h : Height => ∫ x, diamond.poleCoefficient ε h x * transverseNormalCutoff x)
      poleBoundaryHeights (𝓝 (-(Complex.I * (Real.pi : ℂ) * (diamond.eta ε : ℂ)))) := by
  simpa only [transverse_normal_cutoff_pv, transverse_normal_cutoff_zero, mul_one, zero_sub]
    using diamond.transverse_normal_single_test ε transverse_normal_cutoff_lipschitz transverse_normal_cutoff_compact

/-- The true two-normal product on a bounded chart at one common positive
height. The doubly subtracted PV and both shell evaluations are explicit. -/
theorem Plane.transverse_normal_product_boundary (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ p, diamond.poleCoefficient ε₁ h p.1 *
      diamond.poleCoefficient ε₂ h p.2 * f p ∂transverseNormalVolume) poleBoundaryHeights
      (𝓝 (transverseNormalBoundary (diamond.eta ε₁) (diamond.eta ε₂) f)) := by
  let R := transverseNormalRemainder f
  let K : TopologicalSpace.Compacts (ℝ × ℝ) := ⟨tsupport R, transverse_normal_remainder_compact hs⟩
  obtain ⟨C,_,hR⟩ := transverse_normal_remainder_bound hf hs
  have Hr := transverse_normal_remainder_moving_limit (fun _ => R) R K (C := C)
    (Eventually.of_forall fun _ => transverse_normal_remainder_continuous hf.continuous)
    (Eventually.of_forall fun _ p hp => image_eq_zero_of_notMem_tsupport hp)
    (Eventually.of_forall fun _ => hR) (fun _ => tendsto_const_nhds)
    (diamond.poleCoefficient ε₁) (diamond.poleCoefficient ε₂)
    (diamond.pole_coefficient_continuous ε₁) (diamond.pole_coefficient_continuous ε₂)
    (fun h _ hx => diamond.pole_coefficient_off_shell_bound ε₁ h hx)
    (fun h _ hx => diamond.pole_coefficient_off_shell_bound ε₂ h hx)
    (fun _ hx => diamond.pole_coefficient_off_shell_limit ε₁ hx)
    (fun _ hx => diamond.pole_coefficient_off_shell_limit ε₂ hx)
  obtain ⟨hsx,hsy⟩ := transverse_normal_slice_compact hs
  have hdx : ContDiff ℝ 2 (fun x => f (x,0)) := hf.comp (contDiff_id.prodMk contDiff_const)
  have hdy : ContDiff ℝ 2 (fun y => f (0,y)) := hf.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨_,hLx⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsx hdx (by norm_num)
  obtain ⟨_,hLy⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsy hdy (by norm_num)
  have Hx := diamond.transverse_normal_single_test ε₁ hLx hsx
  have Hy := diamond.transverse_normal_single_test ε₂ hLy hsy
  have Hc₁ := diamond.transverse_normal_cutoff_limit ε₁
  have Hc₂ := diamond.transverse_normal_cutoff_limit ε₂
  have H := ((Hr.add (Hc₁.mul Hy)).add (Hx.mul Hc₂)).sub ((Hc₁.mul Hc₂).const_mul (f (0,0)))
  let c (ε : Evolution) := Complex.I * (Real.pi : ℂ) * (diamond.eta ε : ℂ)
  have he : (∫ p, (p.1 : ℂ)⁻¹ * (p.2 : ℂ)⁻¹ * R p ∂transverseNormalVolume) +
      (-c ε₁) * (complexShellPV (fun y => f (0,y)) - c ε₂ * f (0,0)) +
      (complexShellPV (fun x => f (x,0)) - c ε₁ * f (0,0)) * (-c ε₂) -
      f (0,0) * ((-c ε₁) * (-c ε₂)) =
        transverseNormalBoundary (diamond.eta ε₁) (diamond.eta ε₂) f := by
    simp only [transverseNormalBoundary, transverseNormalPV₂, R, c]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [he] at H
  exact H.congr (fun h => by
    rw [transverse_normal_product_split _ _ (diamond.pole_coefficient_continuous ε₁ h)
      (diamond.pole_coefficient_continuous ε₂ h) hf.continuous hs])

end UV.SectorPlane
