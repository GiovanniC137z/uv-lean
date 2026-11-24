import UV.ContinueOrderedCurrentPath
import UV.ContinueThinCurrentSmearing
import UV.ContinueWilsonPolygonCurrent
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Temporal and horizontal marks on the ordered two-band Euclidean path.
A step first follows the directed carrier interval at fixed spatial position,
then the straight hop at its endpoint time. Durations may have either sign. -/

noncomputable section

open MeasureTheory Finset UV.SectorPlane
open scoped RealInnerProductSpace

namespace UV.SectorPlane.OrderedTwoBandPath

def duration (P : OrderedTwoBandPath) (j : ℕ) := P.time (j+1) - P.time j

def step (P : OrderedTwoBandPath) (j : ℕ) := P.position (j+1) - P.position j

def length (P : OrderedTwoBandPath) : ℝ := ∑ j ∈ range P.hops, (|P.duration j| + ‖P.step j‖)

theorem length_nonneg (P : OrderedTwoBandPath) : 0 ≤ P.length :=
  sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (norm_nonneg _)

private theorem time_integrand_norm (ω t : ℝ) : ‖Complex.exp (Complex.I*(ω:ℂ)*(t:ℂ))‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re]

/-- The signed temporal pulse uses the full carrier interval, including at zero frequency. -/
def pulse (P : OrderedTwoBandPath) (j : ℕ) (ω : ℝ) : ℂ :=
  ∫ t in P.time j..P.time (j+1), Complex.exp (Complex.I*(ω:ℂ)*(t:ℂ))

theorem pulse_length (P : OrderedTwoBandPath) (j : ℕ) (ω : ℝ) :
    ‖P.pulse j ω‖ ≤ |P.duration j| := by
  simpa [pulse,duration] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := P.time j) (b := P.time (j+1)) (f := fun t => Complex.exp (Complex.I*(ω:ℂ)*(t:ℂ)))
    (C := 1) (fun t _ => (time_integrand_norm ω t).le)

theorem pulse_frequency (P : OrderedTwoBandPath) (j : ℕ) {ω : ℝ} (hω : ω ≠ 0) :
    ‖P.pulse j ω‖ ≤ min |P.duration j| (2/|ω|) := by
  refine le_min (P.pulse_length j ω) ?_
  unfold pulse
  rw [integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hω)),norm_div]
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  exact (norm_sub_le _ _).trans_eq (by norm_num [time_integrand_norm])

theorem pulses_sum_zero (P : OrderedTwoBandPath) (ω : ℝ) :
    ∑ j ∈ range P.hops, P.pulse j ω = 0 := by
  have hc : Continuous (fun t : ℝ => Complex.exp (Complex.I*(ω:ℂ)*(t:ℂ))) := by fun_prop
  unfold pulse
  rw [intervalIntegral.sum_integral_adjacent_intervals (fun j _ => hc.intervalIntegrable _ _),P.time_closed]
  simp

def spatialWave (p x : Spatial) : ℂ := Complex.exp (Complex.I*(⟪p,x⟫:ℂ))

/-- The Fourier mark obtained by integrating on every vertical segment. -/
def density (P : OrderedTwoBandPath) (ω : ℝ) (p : Spatial) : ℂ :=
  ∑ j ∈ range P.hops, spatialWave p (P.position j)*P.pulse j ω

theorem density_anchor (P : OrderedTwoBandPath) (ω : ℝ) (p x₀ : Spatial) :
    P.density ω p = ∑ j ∈ range P.hops, (spatialWave p (P.position j)-spatialWave p x₀)*P.pulse j ω := by
  simp only [density,sub_mul,sum_sub_distrib,←mul_sum,P.pulses_sum_zero,mul_zero,sub_zero]

theorem carrier_inner (ω t : ℝ) (p x : Spatial) :
    ⟪thinSpatialPoint ω p,thinSpatialPoint t x⟫ = ω*t+⟪p,x⟫ := by
  simp only [thinSpatialPoint,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,PiLp.toLp_apply,
    Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  ring

private theorem spatial_wave_norm (p x : Spatial) : ‖spatialWave p x‖ = 1 := by
  simp [spatialWave,Complex.norm_exp,Complex.mul_re]

theorem spatial_wave_difference (p x y : Spatial) :
    ‖spatialWave p x-spatialWave p y‖ ≤ min 2 (‖p‖*‖x-y‖) := by
  refine le_min ((norm_sub_le _ _).trans_eq (by norm_num [spatial_wave_norm])) ?_
  have hadd : spatialWave p x = spatialWave p y*spatialWave p (x-y) := by
    simp only [spatialWave,←Complex.exp_add,inner_sub_right,Complex.ofReal_sub]
    congr 1
    ring
  rw [hadd,←mul_sub_one,norm_mul,spatial_wave_norm,one_mul]
  have hnorm (q : Spatial) : ‖thinSpatialPoint 0 q‖ = ‖q‖ := by
    have h := thinSpatialPoint_norm_sq 0 q
    nlinarith [norm_nonneg q,norm_nonneg (thinSpatialPoint 0 q)]
  have h := wilson_plane_wave_soft (thinSpatialPoint 0 p) (thinSpatialPoint 0 (x-y))
  simpa only [thinPlaneWave,carrier_inner,zero_mul,zero_add,hnorm,spatialWave] using h

theorem step_within_length (P : OrderedTwoBandPath) {j : ℕ} (hj : j < P.hops) :
    |P.duration j| + ‖P.step j‖ ≤ P.length :=
  single_le_sum (f := fun i => |P.duration i|+‖P.step i‖)
    (fun _ _ => add_nonneg (abs_nonneg _) (norm_nonneg _)) (mem_range.mpr hj)

theorem space_within_length (P : OrderedTwoBandPath) {j : ℕ} (hj : j ≤ P.hops) :
    ‖P.position j-P.position 0‖ ≤ P.length := by
  rw [←dist_eq_norm,dist_comm]
  apply (dist_le_range_sum_dist _ _).trans
  calc
    _ ≤ ∑ i ∈ range j, (|P.duration i|+‖P.step i‖) := by
      apply sum_le_sum
      intro i _
      rw [dist_comm, dist_eq_norm]
      exact le_add_of_nonneg_left (abs_nonneg _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono hj)
      (fun i _ _ => add_nonneg (abs_nonneg _) (norm_nonneg _))

/-- The anchored density has both spatial softness and temporal decay, uniformly
over signed durations, including folded and zero-length segments. -/
theorem density_bound (P : OrderedTwoBandPath) (ω : ℝ) (p : Spatial) :
    ‖P.density ω p‖ ≤ 8*P.hops*(1+P.length)^2*min 1 ‖p‖/(1+|ω|) := by
  let L := P.length
  have hL : 0 ≤ L := P.length_nonneg
  have hpos : 0 < 1+|ω| := by positivity
  have hp0 : 0 ≤ min 1 ‖p‖ := le_min zero_le_one (norm_nonneg _)
  have hterm (j : ℕ) (hj : j ∈ range P.hops) :
      ‖(spatialWave p (P.position j)-spatialWave p (P.position 0))*P.pulse j ω‖ ≤
        8*(1+L)^2*min 1 ‖p‖/(1+|ω|) := by
    have hx := P.space_within_length (mem_range.mp hj).le
    have hu : |P.duration j| ≤ L := (le_add_of_nonneg_right (norm_nonneg _)).trans
      (P.step_within_length (mem_range.mp hj))
    have hdiff := spatial_wave_difference p (P.position j) (P.position 0)
    have hspace : ‖spatialWave p (P.position j)-spatialWave p (P.position 0)‖ ≤ 2*(1+L)*min 1 ‖p‖ := by
      rcases le_total ‖p‖ 1 with hh|hh
      · rw [min_eq_right hh]
        apply (hdiff.trans (min_le_right _ _)).trans
        calc
          _ ≤ ‖p‖*L := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
          _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg p) hL,norm_nonneg p]
      · rw [min_eq_left hh,mul_one]
        exact (hdiff.trans (min_le_left _ _)).trans (by linarith)
    have htime : ‖P.pulse j ω‖*(1+|ω|) ≤ 4*(1+L) := by
      rcases le_total |ω| 1 with hh|hh
      · have h := mul_le_mul ((P.pulse_length j ω).trans hu) (show 1+|ω| ≤ 2 by linarith) hpos.le hL
        linarith
      · have hω : 0 < |ω| := by linarith
        have hdecay := (P.pulse_frequency j (abs_pos.mp hω)).trans (min_le_right _ _)
        have hprod := (le_div_iff₀ hω).mp hdecay
        have hsmall : ‖P.pulse j ω‖ ≤ 2 := (le_mul_of_one_le_right (norm_nonneg _) hh).trans hprod
        nlinarith
    rw [le_div_iff₀ hpos,norm_mul,mul_assoc]
    exact (mul_le_mul hspace htime (by positivity) (by positivity)).trans_eq (by ring)
  rw [P.density_anchor ω p (P.position 0)]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum hterm).trans_eq
  simp only [sum_const,card_range,nsmul_eq_mul,L]
  ring

end UV.SectorPlane.OrderedTwoBandPath
