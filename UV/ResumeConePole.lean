import UV.ResumeConeMajorant
import UV.NextSameSideShell

/-! Both real axial sheets in the unweighted shell delta. The sum is
the delta in the analytic coefficient. Its normalization differs from
a selected positive physical completeness measure. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology

/-- The unweighted shell distribution on real four-momentum tests. -/
def fullShellTest (m : ℝ) (f : ℝ × Spatial → ℝ) : ℝ :=
  (∫ p : Spatial, f (shellFrequency m p, p) / (2 * shellFrequency m p)) +
    ∫ p : Spatial, f (-shellFrequency m p, p) / (2 * shellFrequency m p)

theorem real_axial_nonzero_ae :
    ∀ᵐ q : ℝ × Spatial ∂((volume : Measure ℝ).prod (volume : Measure Spatial)), q.1 ≠ 0 := by
  have h : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by rw [ae_iff]; simp
  exact (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := (volume : Measure Spatial))).ae h

theorem pole_poisson_full_shell_limit (m : ℝ) {f : ℝ × Spatial → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : ℝ => ∫ q : ℝ × Spatial, polePoisson h (shellSquare q.1 q.2 - m ^ 2) * f q)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi * fullShellTest m f)) := by
  let C := (2 * Real.pi) ^ 4 / 2
  have hp := selected_shell_test_limit (σ := (1 : ℝ)) (m := m) (Or.inl rfl) hf hs
  have hn := selected_shell_test_limit (σ := (-1 : ℝ)) (m := m) (Or.inr rfl) hf hs
  have H := (hp.add hn).const_mul C
  simp only [one_mul, neg_one_mul] at H
  have hscale (σ : ℝ) :
      C * (∫ p : Spatial, f (σ * shellFrequency m p, p) *
        (((2 * Real.pi) ^ 3 * (2 * shellFrequency m p))⁻¹)) =
      Real.pi * ∫ p : Spatial, f (σ * shellFrequency m p, p) / (2 * shellFrequency m p) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    refine Eventually.of_forall fun p => ?_
    dsimp [C]
    rw [mul_inv, div_eq_mul_inv]
    ring_nf
    field_simp [Real.pi_ne_zero]
  rw [mul_add] at H
  have hp' := hscale 1
  have hn' := hscale (-1)
  simp only [one_mul, neg_one_mul] at hp' hn'
  rw [hp', hn', ← mul_add] at H
  unfold fullShellTest
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  let G (q : ℝ × Spatial) := polePoisson h (shellSquare q.1 q.2 - m ^ 2) * f q
  let S := {q : ℝ × Spatial | 0 < q.1}
  let T := {q : ℝ × Spatial | q.1 < 0}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_fst
  have hT : MeasurableSet T := measurableSet_lt measurable_fst measurable_const
  have hcont : Continuous (fun q : ℝ × Spatial => shellSquare q.1 q.2 - m ^ 2) := by
    unfold shellSquare
    fun_prop
  have hpc : Continuous (polePoisson h) :=
    continuous_iff_continuousAt.mpr fun x => (polePoisson_hasDerivAt hh' x).continuousAt
  have hi : Integrable G :=
    ((hpc.comp hcont).mul hf).integrable_of_hasCompactSupport (hs.mul_left (f := _))
  have hscaleS :
      C * selectedShellTest 1 h m f = ∫ q in S, G q := by
    unfold selectedShellTest
    simp only [one_mul]
    change C * (∫ q in S, shellMollifierDensity h m q * f q) = _
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hS
    intro q _
    unfold C G shellMollifierDensity
    field_simp [Real.pi_ne_zero]
  have hscaleT :
      C * selectedShellTest (-1) h m f = ∫ q in T, G q := by
    unfold selectedShellTest
    simp only [neg_one_mul, neg_pos]
    change C * (∫ q in T, shellMollifierDensity h m q * f q) = _
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hT
    intro q _
    unfold C G shellMollifierDensity
    field_simp [Real.pi_ne_zero]
  change C * (selectedShellTest 1 h m f + selectedShellTest (-1) h m f) = ∫ q, G q
  rw [mul_add, hscaleS, hscaleT, ← integral_indicator hS, ← integral_indicator hT,
    ← integral_add (hi.indicator hS) (hi.indicator hT)]
  apply integral_congr_ae
  filter_upwards [real_axial_nonzero_ae] with q hq
  rcases lt_or_gt_of_ne hq with hq | hq
  · simp [S, T, hq, hq.not_gt]
  · simp [S, T, hq, hq.not_gt]

end UV.SectorPlane
