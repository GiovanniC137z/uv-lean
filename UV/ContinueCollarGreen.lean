import UV.ContinueCollarEigenmode
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Explicit zero-energy Green solution of the singular collar. The
left barrier is recessive at zero and the independent right solution
vanishes at one. Their Wronskian fixes the delta normalization. -/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace UV.CollarEigenmode

def barrierD (c r : ℝ) := (2*r+3*c/r^2)*exp (-c/r^3)
def rightSolution (c r : ℝ) := barrier (-c) r-exp (2*c)*barrier c r
def rightGradient (c r : ℝ) := barrierD (-c) r-exp (2*c)*barrierD c r

theorem right_hasDerivAt (c : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (rightSolution c) (rightGradient c r) r :=
  (barrier_gradient (-c) hr).sub ((barrier_gradient c hr).const_mul _)

theorem right_laplacian (c : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (rightGradient c) (potential (3*c) r*rightSolution c r) r := by
  convert (barrier_laplacian (-c) hr).sub ((barrier_laplacian c hr).const_mul (exp (2*c))) using 1
  simp only [rightSolution,potential]; ring

theorem right_dirichlet (c : ℝ) : rightSolution c 1 = 0 := by
  simp only [rightSolution,barrier,one_pow,one_mul,div_one,neg_neg,←exp_add]
  ring_nf

theorem collar_wronskian (c : ℝ) {r : ℝ} (hr : 0 < r) :
    barrierD c r*rightSolution c r-barrier c r*rightGradient c r = 6*c := by
  have hx : exp (-c/r^3)*exp (c/r^3) = 1 := by rw [←exp_add,neg_div,neg_add_cancel,exp_zero]
  unfold rightSolution rightGradient
  rw [show barrierD c r*(barrier (-c) r-exp (2*c)*barrier c r)-barrier c r*(barrierD (-c) r-exp (2*c)*barrierD c r) =
      barrierD c r*barrier (-c) r - barrier c r*barrierD (-c) r by ring]
  simp only [barrierD,barrier,neg_neg]
  field_simp
  rw [neg_div] at hx
  linear_combination (6*c)*hx

def green (c r s : ℝ) := barrier c (min r s)*rightSolution c (max r s)/(6*c)

theorem green_symm (c r s : ℝ) : green c r s = green c s r := by rw [green,green,min_comm r s,max_comm r s]

theorem green_bounds {c r s : ℝ} (hc : 0 < c) (hr : r ∈ Ioc 0 1) (hs : s ∈ Ioc 0 1) :
    0 ≤ green c r s ∧ green c r s ≤ (6*c)⁻¹ := by
  let l := min r s
  let u := max r s
  have hₗ : 0 < l := lt_min hr.1 hs.1
  have hu : 0 < u := hr.1.trans_le (le_max_left ..)
  have hu₁ : u ≤ 1 := max_le hr.2 hs.2
  have hlu : l ≤ u := (min_le_left ..).trans (le_max_left r s)
  have hsmall := pow_le_pow_left₀ hu.le hu₁ 3
  have hcs : c ≤ c/u^3 := (le_div_iff₀ (pow_pos hu 3)).mpr
    (mul_le_of_le_one_right hc.le (by simpa only [one_pow] using hsmall))
  have hR : 0 ≤ rightSolution c u := by
    unfold rightSolution barrier
    simp only [neg_neg]
    have h := exp_le_exp.mpr (show 2*c + (-c/u^3) ≤ c/u^3 by rw [neg_div]; linarith)
    rw [exp_add] at h
    nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg u)]
  have hup := div_le_div_of_nonneg_left hc.le (pow_pos hₗ 3) (pow_le_pow_left₀ hₗ.le hlu 3)
  have he : exp (-c/l^3)*exp (c/u^3) ≤ 1 := by rw [←exp_add,neg_div]; exact exp_le_one_iff.mpr (by linarith)
  have hL : 0 ≤ barrier c l := (barrier_pos hₗ).le
  have hprod : barrier c l*rightSolution c u ≤ 1 := by
    have hR' : rightSolution c u ≤ barrier (-c) u := sub_le_self _ (mul_nonneg (exp_pos _).le (barrier_pos hu).le)
    apply (mul_le_mul_of_nonneg_left hR' hL).trans
    unfold barrier
    rw [neg_neg]
    calc _ = (l^2*u^2)*(exp (-c/l^3)*exp (c/u^3)) := by ring
         _ ≤ 1 := mul_le_one₀ (mul_le_one₀ (by simpa using pow_le_pow_left₀ hₗ.le (hlu.trans hu₁) 2) (sq_nonneg u) (by simpa using pow_le_pow_left₀ hu.le hu₁ 2))
           (mul_nonneg (exp_pos _).le (exp_pos _).le) he
  exact ⟨div_nonneg (mul_nonneg hL hR) (by positivity),by
    change (barrier c l*rightSolution c u)/(6*c) ≤ (6*c)⁻¹
    rw [←one_div]; exact div_le_div_of_nonneg_right hprod (by positivity)⟩

theorem green_measurable (c : ℝ) : Measurable (fun x : ℝ × ℝ => green c x.1 x.2) := by
  unfold green barrier rightSolution barrier
  fun_prop

theorem green_square_integrable {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun z : ℝ × ℝ => green c z.1 z.2^2) (Ioc 0 1 ×ˢ Ioc 0 1) := by
  let Q := (Ioc (0:ℝ) 1) ×ˢ (Ioc (0:ℝ) 1)
  have hQ : (volume : Measure (ℝ × ℝ)) Q ≠ ⊤ := by
    rw [Measure.volume_eq_prod,Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne
  apply (integrableOn_const (C := ((6*c)⁻¹)^2) hQ).mono' ((green_measurable c).pow_const 2).aestronglyMeasurable
  apply (ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)).mono fun z hz => ?_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  obtain ⟨hn,hb⟩ := green_bounds hc hz.1 hz.2
  exact pow_le_pow_left₀ hn hb 2

def greenApplied (c : ℝ) (f : ℝ → ℝ) (r : ℝ) :=
  (rightSolution c r*(∫ s in (0:ℝ)..r,barrier c s*f s)+barrier c r*(∫ s in r..(1:ℝ),rightSolution c s*f s))/(6*c)

def greenGradient (c : ℝ) (f : ℝ → ℝ) (r : ℝ) :=
  (rightGradient c r*(∫ s in (0:ℝ)..r,barrier c s*f s)+barrierD c r*(∫ s in r..(1:ℝ),rightSolution c s*f s))/(6*c)

/-- On every smooth test force, the Green solution solves the actual
inhomogeneous radial equation. Only continuity on the closed interval
is needed; all upper-primitive integrations begin strictly above zero. -/
theorem green_solves {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) (hf : Continuous f) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    HasDerivAt (greenApplied c f) (greenGradient c f r) r ∧
    HasDerivAt (greenGradient c f) (potential (3*c) r*greenApplied c f r-f r) r := by
  let U := fun x => ∫ s in (0:ℝ)..x,barrier c s*f s
  let V := fun x => ∫ s in x..(1:ℝ),rightSolution c s*f s
  have hmL : ContinuousOn (fun s => barrier c s*f s) (Ioi 0) := fun s hs => ((barrier_gradient c hs).continuousAt.mul hf.continuousAt).continuousWithinAt
  have hmR : ContinuousOn (fun s => rightSolution c s*f s) (Ioi 0) := fun s hs => ((right_hasDerivAt c hs).continuousAt.mul hf.continuousAt).continuousWithinAt
  have hU : HasDerivAt U (barrier c r*f r) r := by
    apply intervalIntegral.integral_hasDerivAt_right
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hr.1.le]; exact (barrier_continuous hc).mul hf.continuousOn
    · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hmL r hr.1
    · exact (barrier_gradient c hr.1).continuousAt.mul hf.continuousAt
  have hV : HasDerivAt V (-(rightSolution c r*f r)) r := by
    apply intervalIntegral.integral_hasDerivAt_left
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hr.2.le]; exact hmR.mono fun _ ht => hr.1.trans_le ht.1
    · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hmR r hr.1
    · exact (right_hasDerivAt c hr.1).continuousAt.mul hf.continuousAt
  constructor
  · convert (((right_hasDerivAt c hr.1).mul hU).add ((barrier_gradient c hr.1).mul hV)).div_const (6*c) using 1
    change (_+_)/(6*c) = (_+_)/(6*c)
    dsimp only [U,V,barrierD]; ring
  · convert (((right_laplacian c hr.1).mul hU).add ((barrier_laplacian c hr.1).mul hV)).div_const (6*c) using 1
    change potential _ _*((rightSolution _ _*U r+barrier _ _*V r)/(6*c))-f r = _
    change _ = ((potential _ _*rightSolution _ _*U r+rightGradient _ _*(barrier _ _*f r))+
      (potential _ _*barrier _ _*V r+barrierD _ _*(-(rightSolution _ _*f r))))/(6*c)
    field_simp
    linear_combination (f r)*(collar_wronskian c hr.1)

theorem green_dirichlet_values (c s : ℝ) (hs : s ∈ Icc 0 1) : green c 0 s = 0 ∧ green c 1 s = 0 := by
  simp [green,min_eq_left hs.1,max_eq_right hs.1,min_eq_right hs.2,max_eq_left hs.2,right_dirichlet,barrier]

theorem greenApplied_eq_integral {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) (hf : Continuous f) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    greenApplied c f r = ∫ s in (0:ℝ)..1,green c r s*f s := by
  let L := fun s => rightSolution c r/(6*c)*(barrier c s*f s)
  let R := fun s => barrier c r/(6*c)*(rightSolution c s*f s)
  have h₁ (s) (hs : s ∈ uIcc 0 r) : green c r s*f s = L s := by
    rw [uIcc_of_le hr.1.le] at hs
    unfold green L; rw [min_eq_right hs.2,max_eq_left hs.2]; ring
  have h₂ (s) (hs : s ∈ uIcc r 1) : green c r s*f s = R s := by
    rw [uIcc_of_le hr.2.le] at hs
    unfold green R; rw [min_eq_left hs.1,max_eq_right hs.1]; ring
  have hL : IntervalIntegrable (fun s => green c r s*f s) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.congr (f := L) _ h₁
    rw [uIcc_of_le hr.1.le]; exact continuousOn_const.mul ((barrier_continuous hc).mul hf.continuousOn)
  have hR : IntervalIntegrable (fun s => green c r s*f s) volume r 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.congr (f := R) _ h₂
    rw [uIcc_of_le hr.2.le]
    have hm : ContinuousOn (rightSolution c) (Icc r 1) := fun s hs => (right_hasDerivAt c (hr.1.trans_le hs.1)).continuousAt.continuousWithinAt
    exact continuousOn_const.mul (hm.mul hf.continuousOn)
  rw [←intervalIntegral.integral_add_adjacent_intervals hL hR,intervalIntegral.integral_congr h₁,intervalIntegral.integral_congr h₂]
  dsimp only [L,R,greenApplied]
  simp only [intervalIntegral.integral_const_mul]; ring

theorem dirichlet_homogeneous_unique {c : ℝ} (hc : 0 < c) {u g : ℝ → ℝ}
    (hU : ContinuousOn u (Icc 0 1)) (hz : u 0 = 0) (h₁ : u 1 = 0)
    (hu : ∀ x ∈ Ioo 0 1,HasDerivAt u (g x) x)
    (hg : ∀ x ∈ Ioo 0 1,HasDerivAt g (potential (3*c) x*u x) x) :
    ∀ r ∈ Icc (0:ℝ) 1,u r = 0 := by
  have h := dirichlet_mode_bound (j := 3*c) (E := 0) hc zero_lt_one le_rfl hU hz hu
    (fun x hx => by simpa only [sub_zero] using hg x hx) (by simp)
  intro r hr
  have hn := h r hr
  simpa only [h₁,abs_zero,zero_div,zero_mul,abs_nonpos_iff] using hn

end UV.CollarEigenmode
