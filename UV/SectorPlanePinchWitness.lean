import UV.SectorPlaneStablePinch
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Smooth test witnesses for the opposite-side pinch. The spatial
center is any specified unit direction on the fixed plane. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped ContDiff Topology

/-- A compact smooth nonnegative test has strictly positive mass on the
full shell. It also works for zero mass without dividing a test by zero at
the cone tip. -/
theorem positive_shell_test_exists (m : ℝ) (u : UnitVector Spatial) :
    ∃ f : MassiveMomentum → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ q, 0 ≤ f q) ∧ 0 < fullShellTest m f := by
  let p₀ := (u : Spatial)
  let frequency := shellFrequency m
  let t₀ := frequency p₀
  let b : ContDiffBump t₀ := ⟨1,2,by norm_num,by norm_num⟩
  let d : ContDiffBump p₀ := ⟨1,2,by norm_num,by norm_num⟩
  let f (q : MassiveMomentum) := 2*q.1^2 * (b q.1 * d q.2)
  have hfrequency : Continuous frequency := by unfold frequency shellFrequency; fun_prop
  have hpos (p : Spatial) : 0 ≤ frequency p := Real.sqrt_nonneg _
  have h₀ : 0 < t₀ := by
    change 0 < Real.sqrt (‖(u:Spatial)‖^2 + m^2)
    rw [u.property]; positivity
  have hfc : ContDiff ℝ ∞ f :=
    (contDiff_const.mul (contDiff_fst.pow 2)).mul ((b.contDiff.comp contDiff_fst).mul (d.contDiff.comp contDiff_snd))
  have hfs : HasCompactSupport f := by
    apply HasCompactSupport.intro (b.hasCompactSupport.prod d.hasCompactSupport)
    intro q hq
    by_cases ht : q.1 ∈ tsupport (b : ℝ → ℝ)
    · have hp : q.2 ∉ tsupport (d : Spatial → ℝ) := fun hp => hq ⟨ht,hp⟩
      simp [f,image_eq_zero_of_notMem_tsupport hp]
    · simp [f,image_eq_zero_of_notMem_tsupport ht]
  have he (t : ℝ) (p : Spatial) (ht : t^2 = (frequency p)^2) :
      f (t,p) / (2*frequency p) = frequency p * (b t * d p) := by
    dsimp only [f]
    rw [ht]
    by_cases hz : frequency p = 0
    · simp [hz]
    · field_simp
  let G (p : Spatial) := frequency p * (b (frequency p) * d p)
  have hGc : Continuous G := hfrequency.mul ((b.continuous.comp hfrequency).mul d.continuous)
  have hGs : HasCompactSupport G := by
    apply HasCompactSupport.intro d.hasCompactSupport
    intro p hp
    simp [G,image_eq_zero_of_notMem_tsupport hp]
  have hv : G p₀ ≠ 0 := by
    have hb : b t₀ = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    have hd : d p₀ = 1 := d.one_of_mem_closedBall (Metric.mem_closedBall_self d.rIn_pos.le)
    change t₀ * (b t₀*d p₀) ≠ 0
    simpa [hb,hd] using h₀.ne'
  have hG := integral_pos_of_integrable_nonneg_nonzero (μ := volume) hGc (hGc.integrable_of_hasCompactSupport hGs)
    (fun p => mul_nonneg (hpos p) (mul_nonneg b.nonneg d.nonneg)) hv
  refine ⟨f,hfc,hfs,fun q => mul_nonneg (by positivity) (mul_nonneg b.nonneg d.nonneg),?_⟩
  unfold fullShellTest
  change 0 < (∫ p, f (frequency p,p)/(2*frequency p)) + ∫ p, f (-frequency p,p)/(2*frequency p)
  simp_rw [he _ _ rfl, he _ _ (neg_sq _)]
  exact add_pos_of_pos_of_nonneg hG (integral_nonneg (fun p => mul_nonneg (hpos p) (mul_nonneg b.nonneg d.nonneg)))

/-- The co-routed stable-half product with opposite pole sides has no
distributional boundary on all smooth compact tests for any two depths. -/
theorem Plane.stable_pinch_smooth_witness {E : Type*} [NormedAddCommGroup E] (diamond : Plane E)
    (ε₁ ε₂ : Evolution) (hη : diamond.eta ε₂ = -diamond.eta ε₁) (u : UnitVector Spatial)
    {a₁ a₂ m : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (hm : 0 ≤ m) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    ∃ f : MassiveMomentum → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ q, 0 ≤ f q) ∧
      ¬∃ z, Tendsto (fun h => diamond.twoLinePairing ε₁ ε₂ h φ φ a₁ a₂ m m (fun q => (f q : ℂ))) poleBoundaryHeights (𝓝 z) := by
  intro φ
  obtain ⟨f,hf,hs,hpos,hw⟩ := positive_shell_test_exists m u
  refine ⟨f,hf,hs,hpos,diamond.stable_half_pinch_no_boundary ε₁ ε₂ hη h₁ h₂ hm
    (Complex.continuous_ofReal.comp hf.continuous) (hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero) ?_⟩
  have hzero : fullShellTest m (fun _ => 0) = 0 := by simp [fullShellTest]
  simpa [complexShellTest,hzero] using hw.ne'

end UV.SectorPlane
