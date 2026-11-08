import UV.DiskZeroCount
import UV.ParameterCircle

/-! A unique simple root is constructed by the actual first logarithmic
derivative contour moment. No pre-existing root branch is supplied. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology

namespace UV

/-- The actual contour moment is itself the unique simple interior zero
whenever the independently defined disk divisor has count one. -/
theorem diskRootMoment_properties {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hr : 0 < r)
    (hb : ∀ z ∈ sphere c r, f z ≠ 0) (hcount : diskZeroCount f c r = 1) :
    diskRootMoment f c r ∈ ball c r ∧
      f (diskRootMoment f c r) = 0 ∧
      deriv f (diskRootMoment f c r) ≠ 0 ∧
      ∀ z ∈ ball c r, f z = 0 → z = diskRootMoment f c r := by
  obtain ⟨z,hz,hzero,hderiv,honly⟩ := disk_zeroCount_one_unique_simple hf hr hb hcount
  rw [diskRootMoment_eq_of_count_one hf hr hb hcount hz hzero]
  exact ⟨hz,hzero,hderiv,honly⟩

def diskRootFamily (F : ℂ → ℂ → ℂ) (c : ℂ) (r : ℝ) : ℂ → ℂ :=
  fun l => diskRootMoment (F l) c r

theorem diskRootFamily_properties {F : ℂ → ℂ → ℂ} {Ω : Set ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hF : ∀ l ∈ Ω, AnalyticOnNhd ℂ (F l) (closedBall c r))
    (hb : ∀ l ∈ Ω, ∀ z ∈ sphere c r, F l z ≠ 0)
    (hcount : ∀ l ∈ Ω, diskZeroCount (F l) c r = 1) :
    ∀ l ∈ Ω, diskRootFamily F c r l ∈ ball c r ∧
      F l (diskRootFamily F c r l) = 0 ∧
      deriv (F l) (diskRootFamily F c r l) ≠ 0 ∧
      ∀ z ∈ ball c r, F l z = 0 → z = diskRootFamily F c r l :=
  fun l hl => diskRootMoment_properties (hF l hl) hr (hb l hl) (hcount l hl)

theorem diskRootFamily_initial {F : ℂ → ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hF : AnalyticOnNhd ℂ (F 0) (closedBall c r))
    (hb : ∀ z ∈ sphere c r, F 0 z ≠ 0) (hcount : diskZeroCount (F 0) c r = 1)
    (hzero : F 0 c = 0) : diskRootFamily F c r 0 = c :=
  diskRootMoment_eq_of_count_one hF hr hb hcount (mem_ball_self hr) hzero

theorem diskRootFamily_norm_bound {F : ℂ → ℂ → ℂ} {Ω : Set ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hF : ∀ l ∈ Ω, AnalyticOnNhd ℂ (F l) (closedBall c r))
    (hb : ∀ l ∈ Ω, ∀ z ∈ sphere c r, F l z ≠ 0)
    (hcount : ∀ l ∈ Ω, diskZeroCount (F l) c r = 1) :
    ∀ l ∈ Ω, ‖diskRootFamily F c r l-c‖ < r := by
  intro l hl
  exact (diskRootFamily_properties hr hF hb hcount l hl).1

/-- Boundary parameter holomorphy makes the actual first contour moment
holomorphic. No root or holomorphic branch is an input. -/
theorem diskRootFamily_analyticOnNhd {F : ℂ → ℂ → ℂ} {Ω : Set ℂ} {c : ℂ} {r : ℝ}
    (hΩ : IsOpen Ω) (hr : 0 ≤ r)
    (hb : ∀ l ∈ Ω, ∀ z ∈ sphere c r, F l z ≠ 0)
    (hc : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (Ω ×ˢ sphere c r))
    (hd : ContinuousOn (fun p : ℂ × ℂ => deriv (F p.1) p.2) (Ω ×ˢ sphere c r))
    (hparam : ∀ z ∈ sphere c r, DifferentiableOn ℂ (fun l => F l z) Ω)
    (hparamDeriv : ∀ z ∈ sphere c r,
      DifferentiableOn ℂ (fun l => deriv (F l) z) Ω) :
    AnalyticOnNhd ℂ (diskRootFamily F c r) Ω := by
  have hlog : ContinuousOn (fun p : ℂ × ℂ => logDeriv (F p.1) p.2)
      (Ω ×ˢ sphere c r) :=
    hd.div hc (fun p hp => hb p.1 hp.1 p.2 hp.2)
  have hweighted : ContinuousOn (fun p : ℂ × ℂ => p.2 * logDeriv (F p.1) p.2)
      (Ω ×ˢ sphere c r) := continuous_snd.continuousOn.mul hlog
  have hhol : ∀ z ∈ sphere c r,
      DifferentiableOn ℂ (fun l => z * logDeriv (F l) z) Ω := by
    intro z hz
    exact ((hparamDeriv z hz).div (hparam z hz) (fun l hl => hb l hl z hz)).const_mul z
  have hi := parameterCircle_analyticOnNhd
    (F := fun l z => z * logDeriv (F l) z) (c := c) hΩ hr hweighted hhol
  exact analyticOnNhd_const.mul hi

/-- Count certificates construct a genuine simple root family; boundary
holomorphy proves that very family's holomorphy and its uniform disk bound. -/
theorem disk_unique_root_holomorphic_family
    {F : ℂ → ℂ → ℂ} {Ω : Set ℂ} {c : ℂ} {r : ℝ}
    (hΩ : IsOpen Ω) (hr : 0 < r)
    (hF : ∀ l ∈ Ω, AnalyticOnNhd ℂ (F l) (closedBall c r))
    (hb : ∀ l ∈ Ω, ∀ z ∈ sphere c r, F l z ≠ 0)
    (hcount : ∀ l ∈ Ω, diskZeroCount (F l) c r = 1)
    (hc : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (Ω ×ˢ sphere c r))
    (hd : ContinuousOn (fun p : ℂ × ℂ => deriv (F p.1) p.2) (Ω ×ˢ sphere c r))
    (hparam : ∀ z ∈ sphere c r, DifferentiableOn ℂ (fun l => F l z) Ω)
    (hparamDeriv : ∀ z ∈ sphere c r,
      DifferentiableOn ℂ (fun l => deriv (F l) z) Ω) :
    AnalyticOnNhd ℂ (diskRootFamily F c r) Ω ∧
      ∀ l ∈ Ω, diskRootFamily F c r l ∈ ball c r ∧
        F l (diskRootFamily F c r l) = 0 ∧
        deriv (F l) (diskRootFamily F c r l) ≠ 0 ∧
        ∀ z ∈ ball c r, F l z = 0 → z = diskRootFamily F c r l :=
  ⟨diskRootFamily_analyticOnNhd hΩ hr.le hb hc hd hparam hparamDeriv,
    diskRootFamily_properties hr hF hb hcount⟩

end UV
