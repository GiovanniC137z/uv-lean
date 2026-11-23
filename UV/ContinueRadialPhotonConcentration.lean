import UV.ContinueRadialPhotonMoments
import UV.ContinueTemporalPolarization

/-! The midpoint-minus-endpoint harmonic readout, the normalized
squared-energy fluctuation, and concentration at unit speed on a
fixed carrier. The bounds apply uniformly to volume-dependent laws. -/

noncomputable section

namespace UV.RadialPhoton

open MeasureTheory Filter Set Real
open scoped Topology

def depthDifference (r k : ℝ) : ℝ := exp (-r*k/2)-exp (-r*k)

def depthDelta (R k : ℝ) : ℝ := min 1 (R^2*k^2/4)

theorem depth_difference_bounds {r R k : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (hk : 0 ≤ k) :
    0 ≤ depthDifference r k ∧ depthDifference r k ≤ min 1 (R*k/2) ∧
      (depthDifference r k)^2 ≤ depthDelta R k := by
  let t := r*k/2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht' : t ≤ R*k/2 := by dsimp [t]; gcongr
  have he0 : 0 ≤ exp (-t) := (exp_pos _).le
  have he1 : exp (-t) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have he : depthDifference r k = exp (-t)*(1-exp (-t)) := by
    unfold depthDifference
    rw [mul_sub,mul_one,← exp_add]
    congr 2 <;> dsimp [t] <;> ring
  have d0 : 0 ≤ depthDifference r k := he ▸ mul_nonneg he0 (sub_nonneg.mpr he1)
  have d1 : depthDifference r k ≤ 1-exp (-t) := he ▸ mul_le_of_le_one_left (sub_nonneg.mpr he1) he1
  have du : depthDifference r k ≤ 1 := d1.trans (by linarith only [he0])
  have dr : depthDifference r k ≤ R*k/2 := d1.trans ((by linarith only [add_one_le_exp (-t)] :
    1-exp (-t) ≤ t).trans ht')
  refine ⟨d0,le_min du dr,le_min ?_ ?_⟩
  · simpa only [one_pow] using pow_le_pow_left₀ d0 du 2
  · exact (pow_le_pow_left₀ d0 dr 2).trans_eq (by ring)

def speedFluctuation (Y : ℝ) : ℝ := (Y-1)^2/(Y+1)

private theorem speed_fluctuation_tail {Y ε : ℝ} (hY : 0 ≤ Y) (hε : 0 < ε)
    (h : ε ≤ |Y-1|) : ε^2/(2+ε) ≤ speedFluctuation Y := by
  have hden : 0 < 2+ε := by positivity
  have hden' : 0 < Y+1 := by positivity
  unfold speedFluctuation
  apply (div_le_div_iff₀ hden hden').mpr
  rcases le_or_gt 1 Y with h' | h'
  · rw [abs_of_nonneg (sub_nonneg.mpr h')] at h
    have hf : 0 ≤ (Y-1-ε)*(ε*(Y-1)+2*(Y-1+ε)) :=
      mul_nonneg (sub_nonneg.mpr h) (by
        have hΔ := sub_nonneg.mpr h'
        positivity)
    linarith only [show (Y-1)^2*(2+ε) - ε^2*(Y+1) = (Y-1-ε)*(ε*(Y-1)+2*(Y-1+ε)) by ring,hf]
  · have hs := pow_le_pow_left₀ hε.le h 2
    rw [sq_abs] at hs
    exact (mul_le_mul_of_nonneg_right hs hden'.le).trans
      (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _))

theorem radial_photon_unit_speed (ρ : Measure ℝ) {e R k : ℝ} (hk : 0 < k)
    (hs : ∀ᵐ s ∂ρ, 0 ≤ s) (hi : ∀ x > 0, Integrable (fun s : ℝ => (x+s)⁻¹) ρ)
    (hG : PhotonSandwich ρ (k^2) ((1+e^2*depthDelta R k)*k^2)) {ε : ℝ} (hε : 0 < ε) :
    ρ univ = 1 ∧ ρ.real {s | ε ≤ |s/k^2-1|} ≤ (2+ε)*e^2*depthDelta R k/ε^2 := by
  let a := k^2
  let d := e^2*depthDelta R k
  have ha : 0 < a := sq_pos_of_pos hk
  have hd : 0 ≤ d := mul_nonneg (sq_nonneg e) (le_min zero_le_one (by positivity))
  have hab : a ≤ (1+d)*a := by nlinarith only [mul_nonneg hd ha.le]
  obtain ⟨hρ,hI,hE⟩ := photon_sandwich_moments ρ ha.le hab hs hi hG
  letI : IsProbabilityMeasure ρ := ⟨hρ⟩
  let Y := fun s : ℝ => s/a
  let V := fun s => speedFluctuation (Y s)
  have hYi : Integrable Y ρ := hI.div_const a
  have hEi : (∫ s, Y s ∂ρ) ≤ 1+d := by
    unfold Y
    rw [integral_div]
    exact (div_le_iff₀ ha).mpr hE.2
  have hR : ∫ s, a*(a+s)⁻¹ ∂ρ ≤ 1/2 := by
    rw [integral_const_mul]
    have h := mul_le_mul_of_nonneg_left (hG a ha).2 ha.le
    change a*photonTransform ρ a ≤ _
    exact h.trans_eq (by field_simp; ring)
  have he : V =ᵐ[ρ] fun s => Y s - 3 + 4*(a*(a+s)⁻¹) := by
    filter_upwards [hs] with s hs'
    have hp := (add_pos_of_pos_of_nonneg ha hs').ne'
    have hv : 0 < s/a+1 := add_pos_of_nonneg_of_pos (div_nonneg hs' ha.le) zero_lt_one
    dsimp [V,Y,speedFluctuation]
    field_simp
    ring
  have hJ := (hi a ha).const_mul a
  have hV0 := (hYi.sub (integrable_const (μ := ρ) 3)).add (hJ.const_mul 4)
  have hVi : Integrable V ρ := hV0.congr he.symm
  have hEV : (∫ s, V s ∂ρ) ≤ d := by
    have hYsub : Integrable (fun s => Y s-3) ρ := hYi.sub (integrable_const _)
    rw [integral_congr_ae he,integral_add hYsub (hJ.const_mul 4),
      integral_sub hYi (integrable_const _),integral_const_mul,integral_const]
    simp only [measureReal_univ_eq_one,one_smul]
    linarith only [hEi,hR]
  have hnn : 0 ≤ᵐ[ρ] V := hs.mono fun s hs' => div_nonneg (sq_nonneg _)
    (add_nonneg (div_nonneg hs' ha.le) zero_le_one)
  have hmark := mul_meas_ge_le_integral_of_nonneg hnn hVi (ε^2/(2+ε))
  have hsub : ρ.real {s | ε ≤ |s/a-1|} ≤ ρ.real {s | ε^2/(2+ε) ≤ V s} := by
    apply ENNReal.toReal_mono (measure_ne_top ρ _)
    apply measure_mono_ae
    filter_upwards [hs] with s hs' htail
    exact speed_fluctuation_tail (div_nonneg hs' ha.le) hε htail
  have hsmall := (mul_le_mul_of_nonneg_left hsub (div_nonneg (sq_nonneg _) (by positivity))).trans
    (hmark.trans hEV)
  refine ⟨hρ,?_⟩
  change ρ.real {s | ε ≤ |s/a-1|} ≤ (2+ε)*e^2*depthDelta R k/ε^2
  rw [div_mul_eq_mul_div,div_le_iff₀ (show 0 < 2+ε by positivity)] at hsmall
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  dsimp [d] at hsmall
  linarith only [show (2+ε)*e^2*depthDelta R k = (e^2*depthDelta R k)*(2+ε) by ring,
    mul_comm (ρ.real {s | ε ≤ |s/a-1|}) (ε^2),hsmall]

/-- The volume can vary with the momentum and with the law. -/
theorem radial_photon_concentration_limit {e R ε : ℝ} (hε : 0 < ε) (ρ : ℕ → Measure ℝ)
    (k : ℕ → ℝ) (hk : ∀ n, 0 < k n) (hlim : Tendsto k atTop (𝓝 0))
    (hs : ∀ n, ∀ᵐ s ∂ρ n, 0 ≤ s)
    (hi : ∀ n x, 0 < x → Integrable (fun s : ℝ => (x+s)⁻¹) (ρ n))
    (hG : ∀ n, PhotonSandwich (ρ n) (k n^2) ((1+e^2*depthDelta R (k n))*k n^2)) :
    Tendsto (fun n => (ρ n).real {s | ε ≤ |s/k n^2-1|}) atTop (𝓝 0) := by
  let C := (2+ε)*e^2/ε^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hub (n : ℕ) := (radial_photon_unit_speed (ρ n) (hk n) (hs n) (hi n) (hG n) hε).2
  have hzero : Tendsto (fun n => C*(R^2*(k n)^2/4)) atTop (𝓝 0) := by
    simpa using (((hlim.pow 2).const_mul (R^2)).div_const 4).const_mul C
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => (hub n).trans ?_) hzero
  change (2+ε)*e^2*depthDelta R (k n)/ε^2 ≤ C*_
  rw [show (2+ε)*e^2*depthDelta R (k n)/ε^2 = C*depthDelta R (k n) by unfold C; ring]
  exact mul_le_mul_of_nonneg_left (min_le_right _ _) hC

end UV.RadialPhoton
