import UV.RectifiableContourPrimitive
import UV.BernsteinContourHomotopy
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Uniform approximation of Lipschitz contour representatives. The
derivatives need not converge pointwise: integration by parts first gives
weak derivative convergence on smooth tests, then uniform test
approximation extends it to continuous readouts. -/

noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology NNReal Interval unitInterval

namespace UV

theorem continuousOn_Icc_nnnorm_bound {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    ∃ B : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖₊ ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  exact ⟨⟨B,hB0⟩, fun t ht => by exact_mod_cast hB t ht⟩

theorem lipschitzOn_complex_mul_of_bounds {f g : ℝ → ℂ} {s : Set ℝ}
    {Kf Kg Bf Bg : ℝ≥0} (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s)
    (hBf : ∀ t ∈ s, ‖f t‖₊ ≤ Bf) (hBg : ∀ t ∈ s, ‖g t‖₊ ≤ Bg) :
    LipschitzOnWith (Bf*Kg+Kf*Bg) (fun t => f t*g t) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hfx : ‖f x‖ ≤ Bf := by exact_mod_cast hBf x hx
  have hgy : ‖g y‖ ≤ Bg := by exact_mod_cast hBg y hy
  rw [dist_eq_norm]
  have hsplit : f x*g x-f y*g y = f x*(g x-g y)+(f x-f y)*g y := by ring
  rw [hsplit]
  calc
    _ ≤ ‖f x‖*‖g x-g y‖+‖f x-f y‖*‖g y‖ := by
      simpa only [norm_mul] using norm_add_le (f x*(g x-g y)) ((f x-f y)*g y)
    _ ≤ (Bf : ℝ)*((Kg : ℝ)*dist x y)+((Kf : ℝ)*dist x y)*(Bg : ℝ) := by
      gcongr
      · simpa only [dist_eq_norm] using hg.dist_le_mul x hx y hy
      · simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

/-- Integration by parts for a genuinely Lipschitz complex curve and a C1
test. The product's Lipschitz property and its a.e. derivative are derived. -/
theorem lipschitz_c1_integration_by_parts {f P : ℝ → ℂ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hP : ContDiffOn ℝ 1 P (Icc (0 : ℝ) 1)) :
    (∫ t in (0 : ℝ)..1, derivWithin f (Icc (0 : ℝ) 1) t*P t) =
      f 1*P 1-f 0*P 0-∫ t in (0 : ℝ)..1, f t*derivWithin P (Icc (0 : ℝ) 1) t := by
  obtain ⟨Bf, hBf⟩ := continuousOn_Icc_nnnorm_bound hf.continuous.continuousOn
  obtain ⟨BP, hBP⟩ := continuousOn_Icc_nnnorm_bound hP.continuousOn
  obtain ⟨BD, hBD⟩ := continuousOn_Icc_nnnorm_bound
    (hP.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl)
  have hPLip : LipschitzOnWith BD P (Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (hP.differentiableOn (by norm_num) t ht).hasDerivWithinAt) hBD
  have hProd := lipschitzOn_complex_mul_of_bounds hf.lipschitzOnWith hPLip hBf hBP
  obtain ⟨_, hFTC⟩ := lipschitzOn_derivWithin_properties zero_le_one hProd
  have hAE : derivWithin (fun t => f t*P t) (Icc (0 : ℝ) 1)
      =ᵐ[volume.restrict (Ι (0 : ℝ) 1)]
        (fun t => derivWithin f (Icc (0 : ℝ) 1) t*P t+
          f t*derivWithin P (Icc (0 : ℝ) 1) t) := by
    rw [uIoc_of_le zero_le_one]
    filter_upwards [ae_restrict_of_ae hf.ae_differentiableAt_real,
      ae_restrict_mem measurableSet_Ioc] with t hft ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hfd := hft.hasDerivAt.hasDerivWithinAt (s := Icc (0 : ℝ) 1)
    have hPd := (hP.differentiableOn (by norm_num) t ht').hasDerivWithinAt
    change derivWithin (f*P) (Icc (0 : ℝ) 1) t = _
    rw [(hfd.mul hPd).derivWithin (uniqueDiffOn_Icc zero_lt_one t ht'),
      hfd.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht')]
  have hI₁ := ((lipschitzOn_derivWithin_properties zero_le_one hf.lipschitzOnWith).1).mul_continuousOn
    (by simpa only [uIcc_of_le zero_le_one] using hP.continuousOn)
  have hI₂ : IntervalIntegrable
      (fun t => f t*derivWithin P (Icc (0 : ℝ) 1) t) volume 0 1 :=
    (hf.continuous.continuousOn.mul
      (hP.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl)).intervalIntegrable_of_Icc zero_le_one
  have hsum : (∫ t in (0 : ℝ)..1, derivWithin f (Icc (0 : ℝ) 1) t*P t)+
      (∫ t in (0 : ℝ)..1, f t*derivWithin P (Icc (0 : ℝ) 1) t) = f 1*P 1-f 0*P 0 := by
    rw [← intervalIntegral.integral_add hI₁ hI₂, ← intervalIntegral.integral_congr_ae_restrict hAE]
    exact hFTC
  exact eq_sub_of_add_eq hsum

/-- Uniformly small curves with a common Lipschitz bound have derivatives
converging weakly on every smooth test. No pointwise convergence of the
derivatives is required. -/
theorem lipschitz_uniform_zero_c1_test {F : ℕ → ℝ → ℂ} {K : ℝ≥0}
    (hLip : ∀ n, LipschitzWith K (F n))
    (hU : TendstoUniformlyOn F (fun _ => (0 : ℂ)) atTop (Icc (0 : ℝ) 1))
    {P : ℝ → ℂ} (hP : ContDiffOn ℝ 1 P (Icc (0 : ℝ) 1)) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..1, derivWithin (F n) (Icc (0 : ℝ) 1) t*P t)
      atTop (𝓝 (0 : ℂ)) := by
  have hbound : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ‖F n t‖ ≤ 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) 1 zero_lt_one] with n hn
    intro t ht
    simpa only [dist_zero_left] using (hn t ht).le
  have hPD := hP.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  have hI (n : ℕ) : IntervalIntegrable
      (fun t : ℝ => F n t*derivWithin P (Icc (0 : ℝ) 1) t) volume 0 1 :=
    ((hLip n).continuous.continuousOn.mul hPD).intervalIntegrable_of_Icc zero_le_one
  have hterm : Tendsto
      (fun n => ∫ t in (0 : ℝ)..1, F n t*derivWithin P (Icc (0 : ℝ) 1) t)
      atTop (𝓝 (0 : ℂ)) := by
    have hdct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (l := atTop) (a := (0 : ℝ)) (b := 1) (μ := volume) (f := fun _ => (0 : ℂ))
      (F := fun n t => F n t*derivWithin P (Icc (0 : ℝ) 1) t)
      (fun t => ‖derivWithin P (Icc (0 : ℝ) 1) t‖)
      (Eventually.of_forall (fun n => (hI n).def'.aestronglyMeasurable))
      (by
        filter_upwards [hbound] with n hn
        exact Eventually.of_forall (fun t ht => by
          have ht' : t ∈ Icc (0 : ℝ) 1 := by
            have htI : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
            exact ⟨htI.1.le, htI.2⟩
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (hn t ht') (norm_nonneg _)).trans_eq (one_mul _)))
      (hPD.norm.intervalIntegrable_of_Icc zero_le_one)
      (Eventually.of_forall (fun t ht => by
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          have htI : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
          exact ⟨htI.1.le, htI.2⟩
        simpa only [zero_mul] using (hU.tendsto_at ht').mul_const
          (derivWithin P (Icc (0 : ℝ) 1) t)))
    simpa only [intervalIntegral.integral_zero] using hdct
  have hboundary : Tendsto (fun n => F n 1*P 1-F n 0*P 0) atTop (𝓝 (0 : ℂ)) := by
    simpa only [zero_mul, sub_zero] using
      ((hU.tendsto_at (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)).mul_const (P 1)).sub
        ((hU.tendsto_at (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)).mul_const (P 0))
  have htotal := hboundary.sub hterm
  have hEq : (fun n => ∫ t in (0 : ℝ)..1, derivWithin (F n) (Icc (0 : ℝ) 1) t*P t) =
      (fun n => F n 1*P 1-F n 0*P 0-∫ t in (0 : ℝ)..1, F n t*derivWithin P (Icc (0 : ℝ) 1) t) :=
    funext (fun n => lipschitz_c1_integration_by_parts (hLip n) hP)
  rw [hEq]
  simpa only [sub_zero] using htotal

theorem intervalIntegral_derivWithin_mul_eq {f P : ℝ → ℂ} :
    (∫ t in (0 : ℝ)..1, derivWithin f (Icc (0 : ℝ) 1) t*P t) =
      ∫ t in (0 : ℝ)..1, deriv f t*P t := by
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

theorem lipschitz_uniform_zero_c1_test_deriv {F : ℕ → ℝ → ℂ} {K : ℝ≥0}
    (hLip : ∀ n, LipschitzWith K (F n))
    (hU : TendstoUniformlyOn F (fun _ => (0 : ℂ)) atTop (Icc (0 : ℝ) 1))
    {P : ℝ → ℂ} (hP : ContDiffOn ℝ 1 P (Icc (0 : ℝ) 1)) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..1, deriv (F n) t*P t) atTop (𝓝 (0 : ℂ)) := by
  simpa only [intervalIntegral_derivWithin_mul_eq] using lipschitz_uniform_zero_c1_test hLip hU hP

/-- The uniform operator bound needed to pass from smooth to continuous
tests, with the original Lipschitz constant and unit parameter interval. -/
theorem lipschitz_derivative_test_difference_bound {f φ P : ℝ → ℂ} {K : ℝ≥0} {δ : ℝ}
    (hf : LipschitzWith K f)
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) (hP : ContinuousOn P (Icc (0 : ℝ) 1))
    (hδ : ∀ t ∈ Icc (0 : ℝ) 1, ‖φ t-P t‖ ≤ δ) :
    ‖(∫ t in (0 : ℝ)..1, deriv f t*φ t)-(∫ t in (0 : ℝ)..1, deriv f t*P t)‖ ≤ (K : ℝ)*δ := by
  have hIφ := (lipschitz_deriv_intervalIntegrable hf 0 1).mul_continuousOn
    (by simpa only [uIcc_of_le zero_le_one] using hφ)
  have hIP := (lipschitz_deriv_intervalIntegrable hf 0 1).mul_continuousOn
    (by simpa only [uIcc_of_le zero_le_one] using hP)
  rw [← intervalIntegral.integral_sub hIφ hIP]
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1, ‖deriv f t*φ t-deriv f t*P t‖ ≤ (K : ℝ)*δ := by
    intro t ht
    have htI : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨htI.1.le, htI.2⟩
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (norm_deriv_le_of_lipschitz hf) (hδ t ht') (norm_nonneg _) K.coe_nonneg
  simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- Uniform smooth-test density and the derived operator bound promote
actual weak derivative convergence to every continuous test. -/
theorem lipschitz_uniform_zero_test_of_smooth_approx {F : ℕ → ℝ → ℂ} {K : ℝ≥0}
    (hLip : ∀ n, LipschitzWith K (F n))
    (hU : TendstoUniformlyOn F (fun _ => (0 : ℂ)) atTop (Icc (0 : ℝ) 1))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ P : ℝ → ℂ,
      ContDiffOn ℝ 1 P (Icc (0 : ℝ) 1) ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖φ t-P t‖ ≤ δ) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..1, deriv (F n) t*φ t) atTop (𝓝 (0 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(2*((K : ℝ)+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hmul : 2*((K : ℝ)+1)*δ = ε := by dsimp only [δ]; field_simp
  have hsmall : (K : ℝ)*δ < ε/2 := by nlinarith [K.coe_nonneg]
  obtain ⟨P, hP, hclose⟩ := happrox δ hδ
  have hweak := lipschitz_uniform_zero_c1_test_deriv hLip hU hP
  have hε2 : 0 < ε/2 := by linarith
  filter_upwards [(Metric.tendsto_nhds.mp hweak) (ε/2) hε2] with n hn
  have hn' : ‖∫ t in (0 : ℝ)..1, deriv (F n) t*P t‖ < ε/2 := by simpa only [dist_zero_right] using hn
  rw [dist_zero_right]
  calc
    _ ≤ ‖(∫ t in (0 : ℝ)..1, deriv (F n) t*φ t)-(∫ t in (0 : ℝ)..1, deriv (F n) t*P t)‖+
        ‖∫ t in (0 : ℝ)..1, deriv (F n) t*P t‖ := norm_le_norm_sub_add _ _
    _ ≤ (K : ℝ)*δ+‖∫ t in (0 : ℝ)..1, deriv (F n) t*P t‖ :=
      add_le_add_right (lipschitz_derivative_test_difference_bound (hLip n) hφ hP.continuousOn hclose) _
    _ < ε := by linarith

/-- Actual Bernstein polynomials supply smooth-test density. Thus the weak
convergence conclusion has only uniform convergence, a common Lipschitz
bound, and continuity of the original test as hypotheses. -/
theorem lipschitz_uniform_zero_continuous_test {F : ℕ → ℝ → ℂ} {K : ℝ≥0}
    (hLip : ∀ n, LipschitzWith K (F n))
    (hU : TendstoUniformlyOn F (fun _ => (0 : ℂ)) atTop (Icc (0 : ℝ) 1))
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..1, deriv (F n) t*φ t) atTop (𝓝 (0 : ℂ)) := by
  apply lipschitz_uniform_zero_test_of_smooth_approx hLip hU hφ
  intro δ hδ
  let g : C(I, ℂ) := ⟨fun t => φ t, continuousOn_iff_continuous_restrict.mp hφ⟩
  obtain ⟨n, hn⟩ := (bernsteinCurveExtension_uniform_error φ g (fun _ => rfl) hδ).exists
  refine ⟨bernsteinCurveExtension n φ,
    ((bernsteinCurveExtension_smooth n φ).of_le (by norm_num)).contDiffOn, fun t ht => ?_⟩
  simpa only [norm_sub_rev] using (hn t ht).le

/-- Actual weak derivative convergence to a nonzero limiting curve. -/
theorem lipschitz_uniform_derivative_test {F : ℕ → ℝ → ℂ} {g φ : ℝ → ℂ} {K : ℝ≥0}
    (hLip : ∀ n, LipschitzWith K (F n)) (hgLip : LipschitzWith K g)
    (hU : TendstoUniformlyOn F g atTop (Icc (0 : ℝ) 1))
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..1, deriv (F n) t*φ t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, deriv g t*φ t)) := by
  have hδLip (n : ℕ) : LipschitzWith (K+K) (fun t => F n t-g t) := (hLip n).sub hgLip
  have hδU : TendstoUniformlyOn (fun n t => F n t-g t) (fun _ => (0 : ℂ)) atTop
      (Icc (0 : ℝ) 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) ε hε] with n hn
    intro t ht
    simpa only [dist_zero_left, dist_eq_norm, norm_sub_rev, sub_zero] using hn t ht
  have hweak := lipschitz_uniform_zero_continuous_test hδLip hδU hφ
  have hI (n : ℕ) : (∫ t in (0 : ℝ)..1, deriv (fun t => F n t-g t) t*φ t) =
      (∫ t in (0 : ℝ)..1, deriv (F n) t*φ t)-(∫ t in (0 : ℝ)..1, deriv g t*φ t) := by
    have hiF := (lipschitz_deriv_intervalIntegrable (hLip n) 0 1).mul_continuousOn
      (by simpa only [uIcc_of_le zero_le_one] using hφ)
    have hig := (lipschitz_deriv_intervalIntegrable hgLip 0 1).mul_continuousOn
      (by simpa only [uIcc_of_le zero_le_one] using hφ)
    rw [← intervalIntegral.integral_sub hiF hig]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(hLip n).ae_differentiableAt_real, hgLip.ae_differentiableAt_real] with t htF htg
    intro _
    change deriv (F n-g) t*φ t = _
    rw [deriv_sub htF htg, sub_mul]
  have hsub : Tendsto (fun n => (∫ t in (0 : ℝ)..1, deriv (F n) t*φ t)-
      (∫ t in (0 : ℝ)..1, deriv g t*φ t)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [hI] using hweak
  exact tendsto_sub_nhds_zero_iff.mp hsub

/-- Weak convergence also permits a uniformly convergent varying test.
This is the analytic heart of contour convergence under a common
Lipschitz bound. -/
theorem lipschitz_derivative_pairing_uniform_limit
    {F Ψ : ℕ → ℝ → ℂ} {g φ : ℝ → ℂ} {K : ℝ≥0}
    (hLip : ∀ n, LipschitzWith K (F n)) (hgLip : LipschitzWith K g)
    (hU : TendstoUniformlyOn F g atTop (Icc (0 : ℝ) 1))
    (hΨ : ∀ᶠ n in atTop, ContinuousOn (Ψ n) (Icc (0 : ℝ) 1))
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hTest : TendstoUniformlyOn Ψ φ atTop (Icc (0 : ℝ) 1)) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..1, deriv (F n) t*Ψ n t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, deriv g t*φ t)) := by
  have hbound : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ‖Ψ n t-φ t‖ ≤ 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hTest) 1 zero_lt_one] with n hn
    intro t ht
    simpa only [dist_eq_norm, norm_sub_rev] using (hn t ht).le
  have hvar : Tendsto (fun n => ∫ t in (0 : ℝ)..1, deriv (F n) t*(Ψ n t-φ t))
      atTop (𝓝 (0 : ℂ)) := by
    have hdct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (l := atTop) (a := (0 : ℝ)) (b := 1) (μ := volume) (f := fun _ => (0 : ℂ))
      (F := fun n t => deriv (F n) t*(Ψ n t-φ t)) (fun _ => (K : ℝ))
      (by
        filter_upwards [hΨ] with n hn
        exact ((lipschitz_deriv_intervalIntegrable (hLip n) 0 1).mul_continuousOn
          (by simpa only [uIcc_of_le zero_le_one] using hn.sub hφ)).def'.aestronglyMeasurable)
      (by
        filter_upwards [hbound] with n hn
        exact Eventually.of_forall (fun t ht => by
          have htI : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
          rw [norm_mul]
          exact (mul_le_mul (norm_deriv_le_of_lipschitz (hLip n))
            (hn t ⟨htI.1.le, htI.2⟩) (norm_nonneg _) K.coe_nonneg).trans_eq (mul_one _)))
      intervalIntegrable_const
      (Eventually.of_forall (fun t ht => by
        have htI : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
        have hp : Tendsto (fun n => Ψ n t-φ t) atTop (𝓝 (0 : ℂ)) := by
          simpa only [sub_self] using (hTest.tendsto_at ⟨htI.1.le, htI.2⟩).sub_const (φ t)
        apply squeeze_zero_norm (fun n => ?_)
          (by simpa only [norm_zero, mul_zero] using hp.norm.const_mul (K : ℝ))
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_deriv_le_of_lipschitz (hLip n)) (norm_nonneg _)))
    simpa only [intervalIntegral.integral_zero] using hdct
  have hfixed := lipschitz_uniform_derivative_test hLip hgLip hU hφ
  have htotal := hvar.add hfixed
  have hEq : (fun n => (∫ t in (0 : ℝ)..1, deriv (F n) t*(Ψ n t-φ t))+
      (∫ t in (0 : ℝ)..1, deriv (F n) t*φ t)) =ᶠ[atTop]
      (fun n => ∫ t in (0 : ℝ)..1, deriv (F n) t*Ψ n t) := by
    filter_upwards [hΨ] with n hn
    have hiFixed := (lipschitz_deriv_intervalIntegrable (hLip n) 0 1).mul_continuousOn
      (by simpa only [uIcc_of_le zero_le_one] using hφ)
    have hiVar := (lipschitz_deriv_intervalIntegrable (hLip n) 0 1).mul_continuousOn
      (by simpa only [uIcc_of_le zero_le_one] using hn.sub hφ)
    rw [← intervalIntegral.integral_add hiVar hiFixed]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    ring
  simpa only [zero_add] using htotal.congr' hEq

theorem parametrizedContourIntegral_eq_ordinaryDerivative_scalar {a b : ℂ}
    (γ : Path a b) (f : ℂ → ℂ) :
    parametrizedContourIntegral f γ = ∫ t in (0 : ℝ)..1, deriv γ.extend t*f (γ.extend t) := by
  rw [parametrizedContourIntegral, curveIntegral_eq_intervalIntegral_deriv]
  rfl

/-- Uniform convergence of actual Lipschitz representatives preserves the
actual scalar contour integral. Compact-domain continuity supplies the
varying readout's uniform convergence internally. -/
theorem lipschitzContourIntegral_uniform_limit_scalar {a : ℂ} {K : ℝ≥0}
    (γn : ℕ → Path a a) (γ : Path a a)
    (hnLip : ∀ n, LipschitzWith K (γn n).extend) (hLip : LipschitzWith K γ.extend)
    (hU : TendstoUniformlyOn (fun n t => (γn n).extend t) γ.extend atTop (Icc (0 : ℝ) 1))
    {S : Set ℂ} (hS : IsCompact S)
    (hnMap : ∀ᶠ n in atTop, MapsTo (γn n).extend (Icc (0 : ℝ) 1) S)
    (hMap : MapsTo γ.extend (Icc (0 : ℝ) 1) S)
    {f : ℂ → ℂ} (hf : ContinuousOn f S) :
    Tendsto (fun n => parametrizedContourIntegral f (γn n)) atTop
      (𝓝 (parametrizedContourIntegral f γ)) := by
  have htest : TendstoUniformlyOn (fun n t => f ((γn n).extend t))
      (fun t => f (γ.extend t)) atTop (Icc (0 : ℝ) 1) :=
    UniformContinuousOn.comp_tendstoUniformlyOn_eventually hnMap hMap
      (hS.uniformContinuousOn_of_continuous hf) hU
  have htestc : ∀ᶠ n in atTop, ContinuousOn (fun t => f ((γn n).extend t)) (Icc (0 : ℝ) 1) :=
    hnMap.mono (fun n hn => hf.comp (hnLip n).continuous.continuousOn hn)
  have ht := lipschitz_derivative_pairing_uniform_limit hnLip hLip hU htestc
    (hf.comp hLip.continuous.continuousOn hMap) htest
  simpa only [parametrizedContourIntegral_eq_ordinaryDerivative_scalar] using ht

theorem parametrizedContourIntegral_clm
    {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    {a b : ℂ} (γ : Path a b) (L : Z →L[ℂ] W) {f : ℂ → Z}
    (hf : parametrizedContourIntegrable f γ) :
    parametrizedContourIntegral (fun z => L (f z)) γ = L (parametrizedContourIntegral f γ) := by
  simp_rw [parametrizedContourIntegral_eq]
  have he : (fun t : ℝ => derivWithin γ.extend (Icc (0 : ℝ) 1) t • L (f (γ.extend t))) =
      (fun t => L (derivWithin γ.extend (Icc (0 : ℝ) 1) t • f (γ.extend t))) := by
    funext t
    rw [L.map_smul]
  rw [he]
  exact L.intervalIntegral_comp_comm ((parametrizedContourIntegrable_iff f γ).mp hf)

/-- The uniform contour-limit theorem for arbitrary finite complex
dimensional readouts, including matrices in their operator norm. Actual
integrals commute with the coordinate maps, and the continuous inverse
coordinate map reconstructs the full norm-topology limit. -/
theorem lipschitzContourIntegral_uniform_limit
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    [FiniteDimensional ℂ Z] {a : ℂ} {K : ℝ≥0}
    (γn : ℕ → Path a a) (γ : Path a a)
    (hnLip : ∀ n, LipschitzWith K (γn n).extend) (hLip : LipschitzWith K γ.extend)
    (hU : TendstoUniformlyOn (fun n t => (γn n).extend t) γ.extend atTop (Icc (0 : ℝ) 1))
    {S : Set ℂ} (hS : IsCompact S)
    (hnMap : ∀ᶠ n in atTop, MapsTo (γn n).extend (Icc (0 : ℝ) 1) S)
    (hMap : MapsTo γ.extend (Icc (0 : ℝ) 1) S)
    {f : ℂ → Z} (hf : ContinuousOn f S) :
    Tendsto (fun n => parametrizedContourIntegral f (γn n)) atTop
      (𝓝 (parametrizedContourIntegral f γ)) := by
  let ι := Module.Basis.ofVectorSpaceIndex ℂ Z
  let e : Z ≃L[ℂ] (ι → ℂ) := (Module.Basis.ofVectorSpace ℂ Z).equivFun.toContinuousLinearEquiv
  have hin : ∀ᶠ n in atTop, parametrizedContourIntegrable f (γn n) :=
    hnMap.mono (fun n hn => parametrizedContour_lipschitz_integrable (γn n) (hnLip n)
      (hf.comp (hnLip n).continuous.continuousOn hn))
  have hig : parametrizedContourIntegrable f γ := parametrizedContour_lipschitz_integrable γ hLip
    (hf.comp hLip.continuous.continuousOn hMap)
  have hcoord : Tendsto (fun n => e (parametrizedContourIntegral f (γn n))) atTop
      (𝓝 (e (parametrizedContourIntegral f γ))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    let L : Z →L[ℂ] ℂ := (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
    have hs := lipschitzContourIntegral_uniform_limit_scalar γn γ hnLip hLip hU hS hnMap hMap
      (L.continuous.comp_continuousOn hf)
    change Tendsto (fun n => parametrizedContourIntegral (fun z => L (f z)) (γn n)) atTop
      (𝓝 (parametrizedContourIntegral (fun z => L (f z)) γ)) at hs
    rw [parametrizedContourIntegral_clm γ L hig] at hs
    have heq : (fun n => parametrizedContourIntegral (fun z => L (f z)) (γn n)) =ᶠ[atTop]
        (fun n => L (parametrizedContourIntegral f (γn n))) :=
      hin.mono (fun n hn => parametrizedContourIntegral_clm (γn n) L hn)
    exact hs.congr' heq
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
    (e.symm.continuous.tendsto (e (parametrizedContourIntegral f γ))).comp hcoord

end UV
