import UV.ContinuationPoleBoundary
import UV.ContinuationVectorialPole
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The positive-shell coefficient on a fixed sector plane. The coarea
substitution takes place in the real aligned frequency. The finite height
in the directed quotient is retained until after testing. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Actual positive shell frequency, away from the zero-frequency channel. -/
def shellFrequency (m : ℝ) (p : Spatial) : ℝ := Real.sqrt (‖p‖ ^ 2 + m ^ 2)

theorem shell_frequency_square (m : ℝ) (p : Spatial) :
    shellFrequency m p ^ 2 = ‖p‖ ^ 2 + m ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Change variables from the positive frequency ray to the real shell
denominator. The lower endpoint is the off-shell stationary point. -/
theorem positive_ray_shell_change (κ : ℝ) (g : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), 2 * r * g (r ^ 2 - κ ^ 2)) =
      ∫ D in Ioi (-(κ ^ 2)), g D := by
  have hder (r : ℝ) (_ : r ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt (fun t : ℝ => t ^ 2 - κ ^ 2) (2 * r) (Ioi 0) r := by
    simpa using (((hasDerivAt_id r).pow 2).sub_const (κ ^ 2)).hasDerivWithinAt
  have hinj : InjOn (fun r : ℝ => r ^ 2 - κ ^ 2) (Ioi 0) := by
    apply StrictMonoOn.injOn
    intro r hr t ht hrt
    exact sub_lt_sub_right ((sq_lt_sq₀ hr.le ht.le).mpr hrt) _
  have himage : (fun r : ℝ => r ^ 2 - κ ^ 2) '' Ioi 0 = Ioi (-(κ ^ 2)) := by
    ext D
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : 0 < r := hr
      exact (show -(κ ^ 2) < r ^ 2 - κ ^ 2 by linarith [sq_pos_of_pos hr'])
    · intro hD
      have h : 0 < D + κ ^ 2 := by have : -(κ ^ 2) < D := hD; linarith
      exact ⟨Real.sqrt (D + κ ^ 2), Real.sqrt_pos.mpr h, by
        change Real.sqrt (D + κ ^ 2) ^ 2 - κ ^ 2 = D
        rw [Real.sq_sqrt h.le]; ring⟩
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr' : 0 < r := hr
  change 2 * r * g (r ^ 2 - κ ^ 2) = |2 * r| • g (r ^ 2 - κ ^ 2)
  rw [smul_eq_mul, abs_of_pos (by positivity : 0 < 2 * r)]

/-- An exact single-ray shell test. The test is supported away from the
zero-frequency endpoint, where the quadratic coarea chart degenerates. -/
private theorem positive_ray_shell_poisson_limit_supported {κ : ℝ} (hκ : 0 < κ)
    {f : ℝ → ℝ} (hf : Continuous f) (C : ℝ) (hC : ∀ r, ‖f r‖ ≤ C)
    (hsupp : ∀ r ≤ κ / 2, f r = 0) :
    Tendsto (fun h : ℝ => ∫ r in Ioi (0 : ℝ), polePoisson h (r ^ 2 - κ ^ 2) * f r)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi * (f κ / (2 * κ)))) := by
  let g (D : ℝ) : ℝ :=
    f (Real.sqrt (D + κ ^ 2)) / (2 * max (κ / 2) (Real.sqrt (D + κ ^ 2)))
  have hden (D : ℝ) : 0 < 2 * max (κ / 2) (Real.sqrt (D + κ ^ 2)) :=
    mul_pos two_pos ((half_pos hκ).trans_le (le_max_left _ _))
  have hsqrt : Continuous (fun D : ℝ => Real.sqrt (D + κ ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_id.add continuous_const)
  have hg : Continuous g :=
    (hf.comp hsqrt).div (continuous_const.mul (continuous_const.max hsqrt))
      (fun D => (hden D).ne')
  have hC₀ : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hgC (D : ℝ) : ‖g D‖ ≤ C / κ := by
    dsimp [g]
    rw [abs_div, abs_of_pos (hden D)]
    apply (div_le_div_of_nonneg_right (hC _) (hden D).le).trans
    apply div_le_div_of_nonneg_left hC₀ hκ
    linarith [le_max_left (κ / 2) (Real.sqrt (D + κ ^ 2))]
  have hg₀ : g 0 = f κ / (2 * κ) := by
    dsimp [g]
    rw [zero_add, Real.sqrt_sq hκ.le, max_eq_right (by linarith)]
  have hlim := pole_poisson_test_limit hg (C / κ) hgC
  rw [hg₀] at hlim
  apply hlim.congr'
  refine Eventually.of_forall fun h => ?_
  have hzero (D : ℝ) (hD : D ∉ Ioi (-(κ ^ 2))) : g D = 0 := by
    have hD' : D ≤ -(κ ^ 2) := le_of_not_gt hD
    have hsum : D + κ ^ 2 ≤ 0 := by linarith
    dsimp [g]
    rw [Real.sqrt_eq_zero_of_nonpos hsum, hsupp 0 (by linarith), zero_div]
  calc
    (∫ D : ℝ, polePoisson h D * g D) =
        ∫ D in Ioi (-(κ ^ 2)), polePoisson h D * g D := by
      rw [← integral_indicator measurableSet_Ioi]
      congr 1
      funext D
      by_cases hD : D ∈ Ioi (-(κ ^ 2))
      · rw [indicator_of_mem hD]
      · rw [indicator_of_notMem hD, hzero D hD, mul_zero]
    _ = ∫ r in Ioi (0 : ℝ),
          2 * r * (polePoisson h (r ^ 2 - κ ^ 2) * g (r ^ 2 - κ ^ 2)) :=
      (positive_ray_shell_change κ _).symm
    _ = ∫ r in Ioi (0 : ℝ), polePoisson h (r ^ 2 - κ ^ 2) * f r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr' : 0 < r := hr
      dsimp [g]
      rw [sub_add_cancel, Real.sqrt_sq hr'.le]
      by_cases h : r ≤ κ / 2
      · simp [hsupp r h]
      · rw [max_eq_right (le_of_not_ge h)]
        field_simp [hr'.ne']

theorem pole_poisson_nonneg {h : ℝ} (hh : 0 ≤ h) (D : ℝ) :
    0 ≤ polePoisson h D :=
  div_nonneg hh (by positivity)

theorem pole_poisson_le_inv_height {h : ℝ} (hh : 0 < h) (D : ℝ) :
    polePoisson h D ≤ h⁻¹ := by
  unfold polePoisson
  rw [div_le_iff₀ (by positivity)]
  calc
    h = h⁻¹ * h ^ 2 := by field_simp
    _ ≤ h⁻¹ * (D ^ 2 + h ^ 2) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg D)) (by positivity)

/-- The exact positive-shell limit also holds when the test reaches the
zero-frequency endpoint. That part of the test stays separated from the shell. -/
theorem positive_ray_shell_poisson_limit {κ : ℝ} (hκ : 0 < κ)
    {f : ℝ → ℝ} (hf : Continuous f) (C : ℝ) (hC : ∀ r, ‖f r‖ ≤ C)
    (hi : IntegrableOn f (Ioi (0 : ℝ))) :
    Tendsto (fun h : ℝ => ∫ r in Ioi (0 : ℝ), polePoisson h (r ^ 2 - κ ^ 2) * f r)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi * (f κ / (2 * κ)))) := by
  let χ (r : ℝ) : ℝ := min 1 (max 0 (4 * r / κ - 2))
  let f₁ (r : ℝ) : ℝ := χ r * f r
  let f₂ (r : ℝ) : ℝ := (1 - χ r) * f r
  have hχ : Continuous χ :=
    continuous_const.min (continuous_const.max
      (((continuous_const.mul continuous_id).div_const κ).sub continuous_const))
  have hχ₀ (r : ℝ) : 0 ≤ χ r := le_min zero_le_one (le_max_left _ _)
  have hχ₁ (r : ℝ) : χ r ≤ 1 := min_le_left _ _
  have hχ_near (r : ℝ) (hr : r ≤ κ / 2) : χ r = 0 := by
    have h : 4 * r / κ ≤ 2 := (div_le_iff₀ hκ).2 (by linarith)
    simp [χ, max_eq_left (sub_nonpos.mpr h)]
  have hχ_far (r : ℝ) (hr : 3 * κ / 4 ≤ r) : χ r = 1 := by
    have h : 3 ≤ 4 * r / κ := (le_div_iff₀ hκ).2 (by linarith)
    exact min_eq_left ((by linarith : 1 ≤ 4 * r / κ - 2).trans (le_max_right _ _))
  have h₁ : Continuous f₁ := hχ.mul hf
  have h₂ : Continuous f₂ := (continuous_const.sub hχ).mul hf
  have hC₁ (r : ℝ) : ‖f₁ r‖ ≤ C := by
    rw [show f₁ r = χ r * f r from rfl, norm_mul, Real.norm_of_nonneg (hχ₀ r)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχ₁ r)).trans (hC r)
  have hs₁ (r : ℝ) (hr : r ≤ κ / 2) : f₁ r = 0 := by simp [f₁, hχ_near r hr]
  have hs₂ (r : ℝ) (hr : 3 * κ / 4 ≤ r) : f₂ r = 0 := by simp [f₂, hχ_far r hr]
  have hf₁κ : f₁ κ = f κ := by simp [f₁, hχ_far κ (by linarith)]
  have hi₁ : IntegrableOn f₁ (Ioi (0 : ℝ)) :=
    hi.bdd_mul hχ.aestronglyMeasurable
      ⟨1, fun r => by simpa [Real.norm_of_nonneg (hχ₀ r)] using hχ₁ r⟩
  have hi₂ : IntegrableOn f₂ (Ioi (0 : ℝ)) :=
    hi.bdd_mul (continuous_const.sub hχ).aestronglyMeasurable
      ⟨1, fun r => by
        rw [Real.norm_of_nonneg (sub_nonneg.mpr (hχ₁ r))]
        linarith [hχ₀ r]⟩
  have hlim₁ := positive_ray_shell_poisson_limit_supported hκ h₁ C hC₁ hs₁
  rw [hf₁κ] at hlim₁
  let δ : ℝ := (κ ^ 2 - (3 * κ / 4) ^ 2) ^ 2
  have hδ : 0 < δ := sq_pos_of_pos (by
    nlinarith [sq_pos_of_pos hκ])
  have hsep {r : ℝ} (hr : 0 < r) (hrs : r < 3 * κ / 4) : δ ≤ (r ^ 2 - κ ^ 2) ^ 2 := by
    have hrsq : r ^ 2 ≤ (3 * κ / 4) ^ 2 :=
      (sq_le_sq₀ hr.le (by positivity)).mpr hrs.le
    have hpos : 0 ≤ κ ^ 2 - (3 * κ / 4) ^ 2 := by nlinarith [sq_nonneg κ]
    rw [← neg_sq (r ^ 2 - κ ^ 2), neg_sub]
    exact (sq_le_sq₀ hpos (by linarith)).mpr (by linarith)
  have hcont (h : ℝ) : Continuous (fun r : ℝ => polePoisson h (r ^ 2 - κ ^ 2)) := by
    by_cases hh : h = 0
    · subst h
      simpa [polePoisson] using (continuous_const (y := (0 : ℝ)))
    · exact continuous_const.div
        ((((continuous_id.pow 2).sub continuous_const).pow 2).add continuous_const)
        (fun r => (add_pos_of_nonneg_of_pos (sq_nonneg (r ^ 2 - κ ^ 2))
          (sq_pos_of_ne_zero hh)).ne')
  have hlim₂ : Tendsto (fun h : ℝ =>
      ∫ r in Ioi (0 : ℝ), polePoisson h (r ^ 2 - κ ^ 2) * f₂ r)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[>] (0 : ℝ)) (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun h r => polePoisson h (r ^ 2 - κ ^ 2) * f₂ r) (f := fun _ => 0)
      (fun r => δ⁻¹ * ‖f₂ r‖)
      (Eventually.of_forall fun h => ((hcont h).mul h₂).aestronglyMeasurable)
      ?_ (hi₂.norm.const_mul _) ?_
    · simpa using hh
    · have h₁n : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 :=
        nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
      filter_upwards [self_mem_nhdsWithin, h₁n] with h hh hh₁
      have hh' : 0 < h := hh
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun r hr => ?_
      have hr' : 0 < r := hr
      by_cases hrs : r < 3 * κ / 4
      · rw [norm_mul, Real.norm_of_nonneg (pole_poisson_nonneg hh'.le _)]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        unfold polePoisson
        calc
          _ ≤ 1 / ((r ^ 2 - κ ^ 2) ^ 2 + h ^ 2) :=
            div_le_div_of_nonneg_right hh₁.le (by positivity)
          _ ≤ δ⁻¹ := by
            rw [← one_div]
            exact div_le_div_of_nonneg_left zero_le_one hδ
              ((hsep hr' hrs).trans (le_add_of_nonneg_right (sq_nonneg _)))
      · simp [hs₂ r (le_of_not_gt hrs)]
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun r hr => ?_
      have hr' : 0 < r := hr
      by_cases hrs : r < 3 * κ / 4
      · have hne : (r ^ 2 - κ ^ 2) ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by
          simpa using (hδ.trans_le (hsep hr' hrs)).ne'
        have hc : ContinuousAt (fun h : ℝ => polePoisson h (r ^ 2 - κ ^ 2)) 0 :=
          continuousAt_id.div
            ((continuous_const.add (continuous_id.pow 2)).continuousAt) hne
        simpa [polePoisson] using ((hc.mul continuousAt_const).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
      · simp [hs₂ r (le_of_not_gt hrs)]
  have hsum := hlim₁.add hlim₂
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  have hpC (r : ℝ) : ‖polePoisson h (r ^ 2 - κ ^ 2)‖ ≤ h⁻¹ := by
    rw [Real.norm_of_nonneg (pole_poisson_nonneg hh'.le _)]
    exact pole_poisson_le_inv_height hh' _
  rw [← integral_add
    (hi₁.bdd_mul (hcont h).aestronglyMeasurable ⟨h⁻¹, hpC⟩)
    (hi₂.bdd_mul (hcont h).aestronglyMeasurable ⟨h⁻¹, hpC⟩)]
  congr 1
  funext r
  dsimp [f₁, f₂]
  ring

/-- The shell delta has twice the unnormalized Poisson kernel as its
physical cut density. The axial Fourier factor gives precisely (2κ)⁻¹. -/
theorem positive_ray_shell_measure_limit {κ : ℝ} (hκ : 0 < κ)
    {f : ℝ → ℝ} (hf : Continuous f) (C : ℝ) (hC : ∀ r, ‖f r‖ ≤ C)
    (hi : IntegrableOn f (Ioi (0 : ℝ))) :
    Tendsto (fun h : ℝ => ∫ r in Ioi (0 : ℝ),
      (2 * polePoisson h (r ^ 2 - κ ^ 2)) / (2 * Real.pi) * f r)
      (𝓝[>] (0 : ℝ)) (𝓝 (f κ / (2 * κ))) := by
  have hlim := (positive_ray_shell_poisson_limit hκ hf C hC hi).const_mul Real.pi⁻¹
  rw [show Real.pi⁻¹ * (Real.pi * (f κ / (2 * κ))) = f κ / (2 * κ) by
    rw [← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]] at hlim
  apply hlim.congr'
  refine Eventually.of_forall fun h => ?_
  dsimp only
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  change Real.pi⁻¹ * (polePoisson h (r ^ 2 - κ ^ 2) * f r) =
    2 * polePoisson h (r ^ 2 - κ ^ 2) / (2 * Real.pi) * f r
  ring

section Diamond

variable {E : Type*} [NormedAddCommGroup E]

/-- The physical signed-carrier sheet contains the original spatial covector. -/
def Plane.physicalShellPoint (diamond : Plane E) (m : ℝ) (p : Spatial) : ℝ × Spatial :=
  (sectorSign diamond.s * shellFrequency m p, p)

theorem Plane.physical_shell_point_continuous (diamond : Plane E) (m : ℝ) :
    Continuous (diamond.physicalShellPoint m) :=
  (continuous_const.mul (Real.continuous_sqrt.comp
    ((continuous_norm.pow 2).add continuous_const))).prodMk continuous_id

theorem Plane.physical_shell_normalization (diamond : Plane E) (m : ℝ) (p : Spatial)
    (hp : 0 < shellFrequency m p) :
    let q := diamond.physicalShellPoint m p
    shellSquare q.1 q.2 - m ^ 2 = 0 ∧
      sectorSign diamond.s * q.1 = shellFrequency m p ∧
      |2 * q.1| = 2 * shellFrequency m p := by
  dsimp [Plane.physicalShellPoint, shellSquare]
  rw [mul_pow, sectorSign_sq, one_mul, shell_frequency_square,
    abs_mul, abs_mul, sectorSign_abs, abs_of_pos hp, one_mul,
    abs_of_pos (by norm_num : 0 < (2 : ℝ))]
  refine ⟨by ring, ?_, rfl⟩
  rw [← mul_assoc, ← pow_two, sectorSign_sq, one_mul]

theorem Plane.routed_shell_invariants (diamond : Plane E) (ε : Evolution) (m : ℝ)
    (p : Spatial) (hp : 0 < shellFrequency m p) :
    let k := cutArrow ε (diamond.physicalShellPoint m p)
    shellSquare k.1 k.2 - m ^ 2 = 0 ∧ diamond.eta ε * k.1 = shellFrequency m p ∧
      axialSign k.1 = diamond.eta ε := by
  rcases diamond with ⟨s, b_s, Ghat⟩
  cases s <;> cases ε <;>
    simp [Plane.physicalShellPoint, cutArrow, Plane.eta, shellSquare, shell_frequency_square,
      axialSign, sectorSign, evolutionSign, hp, hp.not_gt]

theorem Plane.routed_shell_running_unit [NormedSpace ℝ E] (diamond : Plane E)
    (ε : Evolution) (m : ℝ) (p : Spatial) (hp : 0 < shellFrequency m p)
    (hk : (cutArrow ε (diamond.physicalShellPoint m p)).1 ≠ 0) :
    (diamond.runningUnit _ hk : E) = diamond.eta ε • (diamond.poleUnit : E) := by
  simp only [Plane.runningUnit, (diamond.routed_shell_invariants ε m p hp).2.2]

/-- The instance of the scalar completeness measure on the signed sheet,
with the physical spatial Lebesgue normalization. The pole height and
the virtual damping profile are independent data. -/
def Plane.positiveShellMeasure (diamond : Plane E) (m : ℝ) :
    Measure (ℝ × Spatial) :=
  Measure.map (diamond.physicalShellPoint m)
    (volume.withDensity (fun p =>
      ENNReal.ofReal (((2 * Real.pi) ^ 3 * (2 * shellFrequency m p))⁻¹)))

theorem Plane.positive_shell_measure_integral (diamond : Plane E) (m : ℝ)
    (f : ℝ × Spatial → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂diamond.positiveShellMeasure m =
      ∫⁻ p, ENNReal.ofReal (((2 * Real.pi) ^ 3 * (2 * shellFrequency m p))⁻¹) *
        f (diamond.physicalShellPoint m p) := by
  have hκ : Continuous (shellFrequency m) :=
    Real.continuous_sqrt.comp ((continuous_norm.pow 2).add continuous_const)
  have hweight : Measurable (fun p : Spatial =>
      ENNReal.ofReal (((2 * Real.pi) ^ 3 * (2 * shellFrequency m p))⁻¹)) :=
    ((measurable_const.mul (measurable_const.mul hκ.measurable)).inv).ennreal_ofReal
  rw [Plane.positiveShellMeasure,
    lintegral_map hf (diamond.physical_shell_point_continuous m).measurable]
  exact lintegral_withDensity_eq_lintegral_mul _ hweight
    (hf.comp (diamond.physical_shell_point_continuous m).measurable)

theorem cut_arrow_continuous (ε : Evolution) : Continuous (cutArrow ε) :=
  (continuous_const.mul continuous_fst).prodMk (continuous_const.smul continuous_snd)

theorem Plane.routed_positive_shell_measure_integral (diamond : Plane E) (ε : Evolution)
    (m : ℝ) (f : ℝ × Spatial → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ k, f k ∂Measure.map (cutArrow ε) (diamond.positiveShellMeasure m) =
      ∫⁻ p, ENNReal.ofReal (((2 * Real.pi) ^ 3 * (2 * shellFrequency m p))⁻¹) *
        f (cutArrow ε (diamond.physicalShellPoint m p)) := by
  have hε := (cut_arrow_continuous ε).measurable
  rw [lintegral_map hf hε]
  exact diamond.positive_shell_measure_integral m (fun q => f (cutArrow ε q)) (hf.comp hε)

end Diamond

end UV.SectorPlane
