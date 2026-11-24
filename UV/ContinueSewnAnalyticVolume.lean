import UV.ContinueSewnAnalyticDirection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod

/-! Local sublevel volume on the full chart. Averaging over a real translation
in the selected unit direction implements slicing without rotating coordinates. -/

noncomputable section
open Real Set Filter MeasureTheory Metric
open scoped ENNReal Topology
namespace UV.SewnFlags

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem derivative_slice_smooth {f : ℝ → ℝ} {t : ℝ}
    (ha : AnalyticAt ℝ f t) (j : ℕ) : DifferentiableAt ℝ (iteratedDeriv j f) t := by
  have hj : AnalyticAt ℝ (iteratedDeriv j f) t := by
    induction j with
    | zero => simpa using ha
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  exact hj.differentiableAt

private theorem directional_ball_volume {U : Set E} {f : E → ℝ}
    (hU : IsOpen U) (ha : AnalyticOnNhd ℝ f U) (x : E)
    (v : {w : E // ‖w‖ = 1}) {m : ℕ} (hm : 0 < m) {c ρ : ℝ}
    (hc : 0 < c) (hρ : 0 < ρ) (hball : ball x (3*ρ) ⊆ U)
    (hder : ∀ z ∈ ball x (3*ρ), c ≤ |iteratedFDeriv ℝ m f z (fun _ => v.val)|)
    {r : ℝ} (hr : 0 < r) :
    volume {z ∈ ball x ρ | |f z| < r} * ENNReal.ofReal (2*ρ) ≤
      ENNReal.ofReal ((2^m:ℝ)*8*(r/c)^(1/(m:ℝ))) * volume (ball x (2*ρ)) := by
  let I := Ioo (-ρ) ρ
  let A := {z ∈ ball x ρ | |f z| < r}
  let B := ball x (2*ρ)
  have hI : MeasurableSet I := measurableSet_Ioo
  have hB : MeasurableSet B := measurableSet_ball
  have hA : MeasurableSet A := by
    have hc' : ContinuousOn f (ball x ρ) := fun z hz =>
      (ha z (hball (ball_subset_ball (by linarith) hz))).continuousAt.continuousWithinAt
    exact (hc'.abs.isOpen_inter_preimage isOpen_ball (isOpen_Iio (a := r))).measurableSet
  let D := (fun p : E × ℝ => p.1+p.2 • v.val) ⁻¹' A
  have hD : MeasurableSet D := hA.preimage (by fun_prop)
  let μ := (volume : Measure E).restrict B
  let τ := (volume : Measure ℝ).restrict I
  have hIt (t : ℝ) (ht : t ∈ I) : ‖t • v.val‖ < ρ := by
    rw [norm_smul, v.property, mul_one, Real.norm_eq_abs]; exact abs_lt.mpr ht
  have hinside (y : E) (hy : y ∈ B) (t : ℝ) (ht : t ∈ I) : y+t • v.val ∈ ball x (3*ρ) := by
    have ht' := hIt t ht
    rw [mem_ball, dist_eq_norm] at hy ⊢
    calc
      _ = ‖(y-x)+t • v.val‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ < _ := by linarith
  have hfirst (t : ℝ) (ht : t ∈ I) : μ ((fun y => (y,t)) ⁻¹' D) = volume A := by
    change volume.restrict B ((fun y : E => y+t • v.val) ⁻¹' A) = _
    rw [Measure.restrict_apply (hA.preimage (by fun_prop)), inter_eq_left.mpr ?_,
      measure_preimage_add_right]
    intro y hy
    have hd : dist (y+t • v.val) x < ρ := hy.1
    have hn : dist y (y+t • v.val) < ρ := by simpa [dist_eq_norm] using hIt t ht
    change dist y x < 2*ρ
    linarith [dist_triangle y (y+t • v.val) x]
  have hvolI : volume I = ENNReal.ofReal (2*ρ) := by
    rw [Real.volume_Ioo]; congr 1; ring
  have he : μ.prod τ D = volume A * ENNReal.ofReal (2*ρ) := by
    rw [Measure.prod_apply_symm hD]
    calc
      _ = ∫⁻ _ : ℝ, volume A ∂τ :=
        lintegral_congr_ae ((ae_restrict_mem hI).mono (fun t ht => hfirst t ht))
      _ = _ := by simp [τ, hvolI]
  rw [← he, Measure.prod_apply hD]
  let C := ENNReal.ofReal ((2^m:ℝ)*8*(r/c)^(1/(m:ℝ)))
  calc
    _ ≤ ∫⁻ _ : E, C ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with y hy
      have ha' (t : ℝ) (ht : t ∈ I) : AnalyticAt ℝ (fun s : ℝ => f (y+s • v.val)) t :=
        by
          have hline : AnalyticAt ℝ (fun s : ℝ => y+s • v.val) t := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
          exact (ha _ (hball (hinside y hy t ht))).comp (f := fun s : ℝ => y+s • v.val) hline
      have hs := finite_type_slice_volume m hm (fun s : ℝ => f (y+s • v.val))
        (fun j t ht => derivative_slice_smooth (ha' t ht) j) hc (fun t ht => by
          rw [analytic_affine_line_derivative hU ha _ _ _ (hball (hinside y hy t ht))]
          exact hder _ (hinside y hy t ht)) hr
      apply le_trans _ hs
      rw [Measure.restrict_apply (hD.preimage measurable_prodMk_left)]
      exact measure_mono fun t ht => ⟨ht.2,ht.1.2⟩
    _ = _ := by simp [μ,C,B]

/-- Every occupied analytic chart point has a neighborhood whose sublevel
volume has a positive power bound on all radii up to one. -/
theorem analytic_local_power_volume {U : Set E} {f : E → ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (ha : AnalyticOnNhd ℝ f U)
    (hnon : ¬ EqOn f 0 U) {x : E} (hx : x ∈ U) :
    ∃ (B : Set E) (C : ℝ≥0∞) (b : ℝ), B ∈ 𝓝 x ∧ C < ⊤ ∧ 0 < b ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 → volume {z ∈ B | |f z| < r} ≤ C * ENNReal.ofReal (r^b) := by
  by_cases hz : f x = 0
  · obtain ⟨m,v,c,hm,hc,hD⟩ := analytic_unit_direction_at_zero ha hconn hx hnon hz
    obtain ⟨ε,hε,hεB⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) hD)
    let ρ := ε/3
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have he : 3*ρ = ε := by dsimp [ρ]; ring
    let b := 1/(m:ℝ)
    have hb : 0 < b := by dsimp [b]; positivity
    let T := ENNReal.ofReal (2*ρ)
    have hT : T ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    let k := (2^m:ℝ)*8/(c^b)
    have hk : 0 ≤ k := by dsimp [k]; positivity
    refine ⟨ball x ρ, (ENNReal.ofReal k * volume (ball x (2*ρ))) / T, b,
      ball_mem_nhds _ hρ, ENNReal.div_lt_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne) hT, hb,?_⟩
    intro r hr _
    have h := directional_ball_volume hU ha x v hm hc hρ
      (by rw [he]; exact fun _ h => (hεB h).1)
      (by rw [he]; exact fun _ h => (hεB h).2) hr
    have hfac : (2^m:ℝ)*8*(r/c)^(1/(m:ℝ)) = k*r^b := by
      rw [Real.div_rpow hr.le hc.le]; dsimp [k,b]; ring
    rw [hfac, ENNReal.ofReal_mul hk] at h
    calc
      _ ≤ (ENNReal.ofReal k * ENNReal.ofReal (r^b) * volume (ball x (2*ρ))) / T :=
        (ENNReal.le_div_iff_mul_le (Or.inl hT) (Or.inl ENNReal.ofReal_ne_top)).mpr h
      _ = _ := by simp only [ENNReal.div_eq_inv_mul]; ac_rfl
  · let c := |f x|/2
    have hc : 0 < c := half_pos (abs_pos.mpr hz)
    have hreg := ((ha x hx).continuousAt.abs.tendsto.eventually_const_lt (half_lt_self (abs_pos.mpr hz)))
    obtain ⟨ρ,hρ,hB⟩ := Metric.mem_nhds_iff.mp hreg
    let M := volume (ball x ρ)
    refine ⟨ball x ρ, M / ENNReal.ofReal c, 1, ball_mem_nhds _ hρ,
      ENNReal.div_lt_top measure_ball_lt_top.ne (ENNReal.ofReal_ne_zero_iff.mpr hc), zero_lt_one, ?_⟩
    intro r hr _
    rw [Real.rpow_one]
    by_cases h : c ≤ r
    · calc
        _ ≤ M := measure_mono fun _ hx => hx.1
        _ = M / ENNReal.ofReal c * ENNReal.ofReal c :=
          (ENNReal.div_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top).symm
        _ ≤ _ := mul_le_mul_left' (ENNReal.ofReal_le_ofReal h) _
    · have he : {z ∈ ball x ρ | |f z| < r} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr; intro z hz'
        exact h ((le_of_lt (hB hz'.1)).trans hz'.2.le)
      rw [he, measure_empty]; exact zero_le _

end UV.SewnFlags
