import UV.ContinueTwoBandFourier
import UV.ContinueRepairResultSlab

/-! Position-space spatial hopping on the finite rectangular torus.
The winding sum uses the normalized heat density on the cover, with a
distinct straight Wilson segment for each lift of the endpoint. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace UV.SectorPlane

abbrev TwoBandPoint := ℝ × Spatial

/-- Half-open position representatives of a rectangular torus. The three
arguments in this module are the spatial periods. -/
def twoBandTorusCell (L₁ L₂ L₃ : ℝ) : Set Spatial :=
  {x | x 0 ∈ Ico 0 L₁ ∧ x 1 ∈ Ico 0 L₂ ∧ x 2 ∈ Ico 0 L₃}

theorem twoBand_torus_cell_measurable (L₁ L₂ L₃ : ℝ) :
    MeasurableSet (twoBandTorusCell L₁ L₂ L₃) := by
  have h (i : Fin 3) (L : ℝ) : MeasurableSet {x : Spatial | x i ∈ Ico 0 L} :=
    measurableSet_Ico.preimage ((EuclideanSpace.projₗ i (𝕜 := ℝ)).continuous_of_finiteDimensional.measurable)
  exact (h 0 L₁).inter ((h 1 L₂).inter (h 2 L₃))

theorem twoBand_torus_cell_norm {L₁ L₂ L₃ : ℝ} {x : Spatial} (hx : x ∈ twoBandTorusCell L₁ L₂ L₃) :
    ‖x‖ ≤ L₁+L₂+L₃ := by
  obtain ⟨hx₁,hx₂,hx₃⟩ := hx
  have hxSq := EuclideanSpace.norm_sq_eq x
  rw [Fin.sum_univ_three] at hxSq
  simp only [Real.norm_eq_abs,sq_abs] at hxSq
  have h₁ := sq_le_sq' (by linarith [hx₁.1,hx₁.2] : -L₁ ≤ x 0) hx₁.2.le
  have h₂ := sq_le_sq' (by linarith [hx₂.1,hx₂.2] : -L₂ ≤ x 1) hx₂.2.le
  have h₃ := sq_le_sq' (by linarith [hx₃.1,hx₃.2] : -L₃ ≤ x 2) hx₃.2.le
  have hL₁ := hx₁.1.trans_lt hx₁.2
  have hL₂ := hx₂.1.trans_lt hx₂.2
  have hL₃ := hx₃.1.trans_lt hx₃.2
  nlinarith only [hxSq,h₁,h₂,h₃,mul_nonneg hL₁.le hL₂.le,mul_nonneg hL₁.le hL₃.le,
    mul_nonneg hL₂.le hL₃.le,norm_nonneg x,add_pos (add_pos hL₁ hL₂) hL₃]

/-- Integration on one symmetric slab and one spatial fundamental cell.
Boundary representatives have zero Lebesgue measure. -/
def twoBandSlabMeasure (T L₁ L₂ L₃ : ℝ) : Measure TwoBandPoint :=
  volume.restrict (Icc (-T) T ×ˢ twoBandTorusCell L₁ L₂ L₃)

instance (T L₁ L₂ L₃ : ℝ) : IsFiniteMeasure (twoBandSlabMeasure T L₁ L₂ L₃) := by
  apply isFiniteMeasure_restrict.mpr
  have h : Icc (-T) T ×ˢ twoBandTorusCell L₁ L₂ L₃ ⊆
      Icc (-T) T ×ˢ Metric.closedBall (0 : Spatial) (L₁+L₂+L₃) := by
    intro x hx
    exact ⟨hx.1, by simpa using twoBand_torus_cell_norm hx.2⟩
  exact ne_top_of_le_ne_top (isCompact_Icc.prod (isCompact_closedBall _ _)).measure_lt_top.ne (measure_mono h)

theorem twoBand_slab_cell_ae (T L₁ L₂ L₃ : ℝ) :
    ∀ᵐ x ∂twoBandSlabMeasure T L₁ L₂ L₃, x.2 ∈ twoBandTorusCell L₁ L₂ L₃ :=
  (ae_restrict_mem (measurableSet_Icc.prod (twoBand_torus_cell_measurable L₁ L₂ L₃))).mono (fun _ h => h.2)

def twoBandSpatialWilson (A : TwoBandPoint → Spatial →L[ℝ] ℝ) (q t : ℝ) (x z : Spatial) : ℂ :=
  Complex.exp (Complex.I * (q:ℂ) * (∫ s in (0:ℝ)..1, A (t,x+s • z) z : ℝ))

theorem twoBand_spatial_wilson_unit (A : TwoBandPoint → Spatial →L[ℝ] ℝ) (q t : ℝ) (x z : Spatial) :
    ‖twoBandSpatialWilson A q t x z‖ = 1 := by
  simp [twoBandSpatialWilson,Complex.norm_exp,Complex.mul_re]

theorem twoBand_spatial_wilson_continuous {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    (q : ℝ) : Continuous (fun p : ℝ × Spatial × Spatial => twoBandSpatialWilson A q p.1 p.2.1 p.2.2) := by
  have h : Continuous (fun p : ℝ × Spatial × Spatial => ∫ s in (0:ℝ)..1,
      A (p.1,p.2.1 + s • p.2.2) p.2.2) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    dsimp [Function.uncurry]
    fun_prop
  unfold twoBandSpatialWilson
  fun_prop

def twoBandWindingHop (A : TwoBandPoint → Spatial →L[ℝ] ℝ)
    (q g σ L₁ L₂ L₃ t : ℝ) (x y : Spatial) (n : ℤ × ℤ × ℤ) : ℂ :=
  let z := y-x+repairTorusMomentum L₁ L₂ L₃ n
  (g * twoBandDisplacementDensity σ z : ℂ) * twoBandSpatialWilson A q t x z

def twoBandPeriodizedHop (A : TwoBandPoint → Spatial →L[ℝ] ℝ)
    (q g σ L₁ L₂ L₃ t : ℝ) (x y : Spatial) : ℂ :=
  ∑' n, twoBandWindingHop A q g σ L₁ L₂ L₃ t x y n

theorem twoBand_winding_hop_measurable {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    (q g σ L₁ L₂ L₃ : ℝ) (n : ℤ × ℤ × ℤ) :
    Measurable (fun p : ℝ × Spatial × Spatial => twoBandWindingHop A q g σ L₁ L₂ L₃ p.1 p.2.1 p.2.2 n) := by
  apply Continuous.measurable
  unfold twoBandWindingHop twoBandDisplacementDensity
  have h := (twoBand_spatial_wilson_continuous hA q).comp
    (show Continuous (fun p : ℝ × Spatial × Spatial =>
      (p.1,p.2.1,p.2.2-p.2.1+repairTorusMomentum L₁ L₂ L₃ n)) by fun_prop)
  exact Continuous.mul (by fun_prop) h

theorem twoBand_winding_gaussian_bound (A : TwoBandPoint → Spatial →L[ℝ] ℝ)
    (q g : ℝ) {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) (R : ℝ) :
    ∃ F : (ℤ × ℤ × ℤ) → ℝ, Summable F ∧ ∀ t x y,
      ‖y-x‖ ≤ R →
        ∀ n, ‖twoBandWindingHop A q g σ L₁ L₂ L₃ t x y n‖ ≤ F n := by
  let a := (4*σ^2)⁻¹
  let c := ((4*Real.pi*σ^2) ^ (3/2:ℝ))⁻¹
  let K := |g| * c * Real.exp (a*R^2)
  have ha : 0 < a := by unfold a; positivity
  have hc : 0 ≤ c := by unfold c; positivity
  refine ⟨fun n => K*FurtherOptical.attenuation (a/2) (repairTorusMomentum L₁ L₂ L₃ n),
    (repair_gaussian_torus_summable (by positivity) h₁ h₂ h₃).mul_left _,?_⟩
  intro t x y hR n
  let w := y-x
  let l := repairTorusMomentum L₁ L₂ L₃ n
  change ‖w‖ ≤ R at hR
  have hl : ‖l‖ ≤ ‖w+l‖+‖w‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le (w+l) w
  have hlSq : ‖l‖^2 ≤ (‖w+l‖+‖w‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hl _
  have hExp : Real.exp (-(a*‖w+l‖^2)) ≤ Real.exp (a*R^2)*Real.exp (-(a/2)*‖l‖^2) := by
    rw [← Real.exp_add,Real.exp_le_exp]
    have h := pow_le_pow_left₀ (norm_nonneg w) hR 2
    nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr hlSq),
      mul_nonneg ha.le (sq_nonneg (‖w+l‖-‖w‖)),
      mul_nonneg ha.le (sub_nonneg.mpr h)]
  unfold twoBandWindingHop
  rw [norm_mul,twoBand_spatial_wilson_unit,mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_real,Real.norm_of_nonneg (by unfold twoBandDisplacementDensity; positivity)]
  change |g| * (c*Real.exp (-(a*‖w+l‖^2))) ≤ K * FurtherOptical.attenuation (a/2) l
  calc
    _ ≤ |g| * c * (Real.exp (a*R^2)*Real.exp (-(a/2)*‖l‖^2)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hExp (mul_nonneg (abs_nonneg _) hc)
    _ = _ := by unfold K FurtherOptical.attenuation; ring

theorem twoBand_periodized_hop_bounded (A : TwoBandPoint → Spatial →L[ℝ] ℝ)
    (q g : ℝ) {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x y, x ∈ twoBandTorusCell L₁ L₂ L₃ → y ∈ twoBandTorusCell L₁ L₂ L₃ →
      Summable (fun n => ‖twoBandWindingHop A q g σ L₁ L₂ L₃ t x y n‖) ∧
      ‖twoBandPeriodizedHop A q g σ L₁ L₂ L₃ t x y‖ ≤ C := by
  obtain ⟨F,hF,hB⟩ := twoBand_winding_gaussian_bound A q g hσ h₁ h₂ h₃ (2*(L₁+L₂+L₃))
  refine ⟨max 0 (∑' n,F n),le_max_left _ _,?_⟩
  intro t x y hx hy
  have hb := hB t x y ((norm_sub_le y x).trans (by linarith [twoBand_torus_cell_norm hx,twoBand_torus_cell_norm hy]))
  have hs := hF.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact ⟨hs,(norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hb hF).trans (le_max_right _ _))⟩

theorem twoBand_periodized_hop_measurable {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    (q g : ℝ) {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) :
    Measurable (fun p : ℝ × Spatial × Spatial => twoBandPeriodizedHop A q g σ L₁ L₂ L₃ p.1 p.2.1 p.2.2) := by
  apply measurable_of_tendsto_metrizable' (atTop : Filter (Finset (ℤ × ℤ × ℤ)))
    (fun S => Finset.measurable_sum S (fun n _ => twoBand_winding_hop_measurable hA q g σ L₁ L₂ L₃ n))
  apply tendsto_pi_nhds.mpr
  intro p
  obtain ⟨F,hF,hB⟩ := twoBand_winding_gaussian_bound A q g hσ h₁ h₂ h₃ ‖p.2.2-p.2.1‖
  exact (hF.of_norm_bounded (hB p.1 p.2.1 p.2.2 le_rfl)).hasSum

end UV.SectorPlane
