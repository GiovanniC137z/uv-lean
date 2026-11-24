import UV.ContinueOrderedCurrent

/-! Horizontal marks, the exact Ward contraction with the temporal density,
and the soft estimate for a real unit spatial polarization. -/

noncomputable section

open MeasureTheory Finset UV.SectorPlane Set
open scoped RealInnerProductSpace

namespace UV.SectorPlane.OrderedTwoBandPath

private theorem chart_inner_wave (ω t : ℝ) (p x : Spatial) :
    thinPlaneWave (thinSpatialPoint ω p) (thinSpatialPoint t x) =
      Complex.exp (Complex.I*(ω:ℂ)*(t:ℂ))*spatialWave p x := by
  simp only [thinPlaneWave,carrier_inner,spatialWave,←Complex.exp_add,Complex.ofReal_add,Complex.ofReal_mul]
  congr 1
  ring

private theorem chart_add (s t : ℝ) (x y : Spatial) :
    thinSpatialPoint s x + thinSpatialPoint t y = thinSpatialPoint (s+t) (x+y) := by
  ext i
  cases i using Fin.cases <;> simp [thinSpatialPoint]

private theorem chart_sub (s t : ℝ) (x y : Spatial) :
    thinSpatialPoint s x - thinSpatialPoint t y = thinSpatialPoint (s-t) (x-y) := by
  ext i
  cases i using Fin.cases <;> simp [thinSpatialPoint]

private theorem chart_smul (r t : ℝ) (y : Spatial) :
    r • thinSpatialPoint t y = thinSpatialPoint (r*t) (r • y) := by
  ext i
  cases i using Fin.cases <;> simp [thinSpatialPoint,smul_eq_mul]

/-- The average of the spacetime wave on the actual horizontal hop, at its fixed time. -/
def hopWave (P : OrderedTwoBandPath) (j : ℕ) (ω : ℝ) (p : Spatial) : ℂ :=
  wilsonEdgeWave (thinSpatialPoint ω p) (thinSpatialPoint (P.time (j+1)) (P.position j))
    (thinSpatialPoint 0 (P.step j))

/-- Spatial current contracted with a real spatial test vector. -/
def spatialCurrent (P : OrderedTwoBandPath) (ω : ℝ) (p v : Spatial) : ℂ :=
  ∑ j ∈ range P.hops, (⟪v,P.step j⟫:ℂ)*P.hopWave j ω p

private theorem pulse_contraction (P : OrderedTwoBandPath) (j : ℕ) (ω : ℝ) :
    Complex.I*(ω:ℂ)*P.pulse j ω =
      Complex.exp (Complex.I*(ω:ℂ)*(P.time (j+1):ℂ))-Complex.exp (Complex.I*(ω:ℂ)*(P.time j:ℂ)) := by
  let c := Complex.I*(ω:ℂ)
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => Complex.exp (c*(u:ℂ))) (c*Complex.exp (c*(t:ℂ))) t := by
    simpa only [mul_one,mul_comm] using (((hasDerivAt_id (t:ℂ)).const_mul c).cexp).comp_ofReal
  have hi : Continuous (fun t : ℝ => c * Complex.exp (c*(t:ℂ))) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hi.intervalIntegrable (μ := volume) (P.time j) (P.time (j+1)))
  rw [intervalIntegral.integral_const_mul] at h
  exact h

/-- Summing endpoint differences on each vertical and horizontal leg cancels around
the entire path. The spatial argument in the contraction is the momentum itself. -/
theorem ward (P : OrderedTwoBandPath) (ω : ℝ) (p : Spatial) :
    (ω:ℂ)*P.density ω p + P.spatialCurrent ω p p = 0 := by
  let W := fun j => thinPlaneWave (thinSpatialPoint ω p) (thinSpatialPoint (P.time j) (P.position j))
  have he (j : ℕ) :
      Complex.I*((ω:ℂ)*(spatialWave p (P.position j)*P.pulse j ω)) +
        Complex.I*((⟪p,P.step j⟫:ℂ)*P.hopWave j ω p) = W (j+1)-W j := by
    have ht := P.pulse_contraction j ω
    have hx := wilson_edge_contraction (thinSpatialPoint ω p) (thinSpatialPoint (P.time (j+1)) (P.position j))
      (thinSpatialPoint 0 (P.step j))
    rw [carrier_inner,mul_zero,zero_add,chart_add,add_zero,
      show P.position j + P.step j = P.position (j+1) by simp [step],
      chart_inner_wave,chart_inner_wave] at hx
    rw [show Complex.I*((ω:ℂ)*(spatialWave p (P.position j)*P.pulse j ω)) =
        spatialWave p (P.position j)*(Complex.I*(ω:ℂ)*P.pulse j ω) by ring,ht,
      ←mul_assoc,hopWave,hx]
    simp only [W,chart_inner_wave]
    ring
  suffices h : Complex.I*((ω:ℂ)*P.density ω p + P.spatialCurrent ω p p) = 0 from
    (mul_eq_zero.mp h).resolve_left Complex.I_ne_zero
  simp only [mul_add,density,spatialCurrent,mul_sum,←sum_add_distrib]
  rw [sum_congr rfl (fun j _ => he j),sum_range_sub]
  simp [W,P.time_closed,P.space_closed]

theorem readout_ward (P : OrderedTwoBandPath) (a ω : ℝ) (p : Spatial) :
    let w : ℂ := Real.exp (-a*‖p‖)
    (ω:ℂ)*(w*P.density ω p)+w*P.spatialCurrent ω p p = 0 := by
  intro w
  rw [mul_left_comm,←mul_add,P.ward,mul_zero]

private theorem wave_difference (q x y : ThinCurrentPlane) :
    ‖thinPlaneWave q x-thinPlaneWave q y‖ ≤ ‖q‖*‖x-y‖ := by
  have h : thinPlaneWave q x = thinPlaneWave q y * thinPlaneWave q (x-y) := by
    simp only [thinPlaneWave,←Complex.exp_add,inner_sub_right,Complex.ofReal_sub]
    congr 1
    ring
  rw [h,←mul_sub_one,norm_mul,show ‖thinPlaneWave q y‖ = 1 by simp [thinPlaneWave,Complex.norm_exp,Complex.mul_re],one_mul]
  exact wilson_plane_wave_soft q (x-y)

private theorem time_within_length (P : OrderedTwoBandPath) {j : ℕ} (hj : j ≤ P.hops) :
    |P.time j-P.time 0| ≤ P.length := by
  rw [←Real.dist_eq,dist_comm]
  apply (dist_le_range_sum_dist _ _).trans
  calc
    _ ≤ ∑ i ∈ range j, (|P.duration i|+‖P.step i‖) := by
      apply sum_le_sum
      intro i _
      rw [dist_comm,Real.dist_eq]
      exact le_add_of_nonneg_right (norm_nonneg _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono hj)
      (fun i _ _ => add_nonneg (abs_nonneg _) (norm_nonneg _))

private theorem chart_norm (t : ℝ) (x : Spatial) : ‖thinSpatialPoint t x‖ ≤ |t|+‖x‖ := by
  nlinarith [thinSpatialPoint_norm_sq t x,sq_abs t,norm_nonneg x,abs_nonneg t,
    norm_nonneg (thinSpatialPoint t x),mul_nonneg (abs_nonneg t) (norm_nonneg x)]

private theorem hop_difference (P : OrderedTwoBandPath) {j : ℕ} (hj : j < P.hops) (ω : ℝ) (p : Spatial) :
    ‖P.hopWave j ω p - thinPlaneWave (thinSpatialPoint ω p) (thinSpatialPoint (P.time 0) (P.position 0))‖ ≤
      ‖thinSpatialPoint ω p‖*(3*P.length) := by
  let q := thinSpatialPoint ω p
  let base := thinSpatialPoint (P.time 0) (P.position 0)
  let start := thinSpatialPoint (P.time (j+1)) (P.position j)
  let d := thinSpatialPoint 0 (P.step j)
  let F := fun s : ℝ => thinPlaneWave q (start+s • d)
  have hc : Continuous F := by unfold F thinPlaneWave; fun_prop
  have hx (s : ℝ) (hs : s ∈ Set.uIoc (0:ℝ) 1) : ‖start+s • d-base‖ ≤ 3*P.length := by
    have h : s ∈ Set.Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
    simp only [start,d,base,chart_smul,mul_zero,chart_add,add_zero,chart_sub]
    apply (chart_norm _ _).trans
    have ht := P.time_within_length (j := j+1) hj
    have hp := P.space_within_length hj.le
    have hd : ‖P.step j‖ ≤ P.length := (le_add_of_nonneg_left (abs_nonneg _)).trans (P.step_within_length hj)
    rw [show P.position j+s • P.step j-P.position 0 = (P.position j-P.position 0)+s • P.step j by abel]
    have hd' : ‖s • P.step j‖ ≤ ‖P.step j‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg h.1.le]
      exact mul_le_of_le_one_left (norm_nonneg _) h.2
    linarith [norm_add_le (P.position j-P.position 0) (s • P.step j)]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun s => F s-thinPlaneWave q base) (C := ‖q‖*(3*P.length)) (fun s hs =>
      (wave_difference q _ _).trans (mul_le_mul_of_nonneg_left (hx s hs) (norm_nonneg q)))
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)] at he
  simpa [F,hopWave,wilsonEdgeWave,q,base,start,d] using he

/-- The soft transverse bound holds for every actual unit spatial polarization,
hence in particular for those orthogonal to the specified spatial momentum. -/
theorem polarized_bound (P : OrderedTwoBandPath) (ω : ℝ) (p : Spatial) (e : UnitVector Spatial) :
    ‖P.spatialCurrent ω p e.val‖ ≤ 3*(1+P.length)^2*min 1 (Real.sqrt (ω^2+‖p‖^2)) := by
  let q := thinSpatialPoint ω p
  let w := thinPlaneWave q (thinSpatialPoint (P.time 0) (P.position 0))
  have hL := P.length_nonneg
  have hQ : Real.sqrt (ω^2+‖p‖^2) = ‖q‖ := by rw [←thinSpatialPoint_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  rw [hQ]
  have hcoeff (j : ℕ) : ‖(⟪e.val,P.step j⟫:ℂ)‖ ≤ ‖P.step j‖ := by
    simpa [e.property] using abs_real_inner_le_norm e.val (P.step j)
  have hsum : (∑ j ∈ range P.hops, ‖P.step j‖) ≤ P.length :=
    sum_le_sum (fun _ _ => le_add_of_nonneg_left (abs_nonneg _))
  by_cases hsoft : ‖q‖ ≤ 1
  · rw [min_eq_right hsoft]
    have hclose : (∑ j ∈ range P.hops, ⟪e.val,P.step j⟫) = 0 := by
      simp only [step,inner_sub_right]
      rw [sum_range_sub (fun j => ⟪e.val,P.position j⟫),P.space_closed,sub_self]
    have hcancel : (∑ j ∈ range P.hops, (⟪e.val,P.step j⟫:ℂ)*w) = 0 := by
      rw [←sum_mul,←Complex.ofReal_sum,hclose,Complex.ofReal_zero,zero_mul]
    have hex : P.spatialCurrent ω p e.val = ∑ j ∈ range P.hops,
        (⟪e.val,P.step j⟫:ℂ)*(P.hopWave j ω p-w) := by simp [spatialCurrent,mul_sub,sum_sub_distrib,hcancel]
    rw [hex]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ range P.hops, ‖P.step j‖*(‖q‖*(3*P.length)) := by
        apply sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul (hcoeff j) (P.hop_difference (mem_range.mp hj) ω p) (norm_nonneg _) (norm_nonneg _)
      _ = (∑ j ∈ range P.hops, ‖P.step j‖)*(‖q‖*(3*P.length)) := (sum_mul ..).symm
      _ ≤ P.length*(‖q‖*(3*P.length)) := mul_le_mul_of_nonneg_right hsum (by positivity)
      _ ≤ _ := by nlinarith [norm_nonneg q,mul_nonneg hL (norm_nonneg q)]
  · rw [min_eq_left (le_of_not_ge hsoft),mul_one]
    apply (norm_sum_le _ _).trans
    apply LE.le.trans _ (hsum.trans (by nlinarith [sq_nonneg P.length]))
    apply sum_le_sum
    intro j _
    rw [norm_mul]
    have hw : ‖P.hopWave j ω p‖ ≤ 1 := by
      apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (fun s _ => ?_)).trans (by norm_num)
      simp [thinPlaneWave,Complex.norm_exp,Complex.mul_re]
    exact (mul_le_of_le_one_right (norm_nonneg _) hw).trans (hcoeff j)

end UV.SectorPlane.OrderedTwoBandPath
