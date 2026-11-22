import UV.ExtendTransverseChart

/-! The derivative of the tested finite-height canonical covariance
and its boundary response on the full regular product chart. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology NNReal

variable {E R : Type*} [NormedAddCommGroup E] [NormedRing R] [NormedAlgebra ℝ R]
  [CompleteSpace R]

/-- The derivative is taken on the fixed compact chart before the
height limit. The normal velocity is inside the transverse integral,
including when it depends on transverse momentum. -/
theorem Plane.transverse_canonical_boundary_response (diamond : Plane E) (ε : Evolution)
    (ν : Measure Spatial) [IsFiniteMeasure ν]
    {j : ℝ → UnitVector R} {dj : R}
    (hj : HasDerivAt (fun t => (j t : R)) dj 0) (hjSq : ∀ t, (j t : R) ^ 2 = -1)
    {f : ℝ × Spatial → ℝ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    {L : ℝ≥0} (hf : ∀ p, LipschitzWith L (fun x => f (x, p)))
    {D D' : ℝ → ℝ × Spatial → ℝ} (ht : ∀ t, Continuous (D t)) (h0 : ∀ x, D 0 x = x.1)
    {b : ℝ} (hb : 0 < b)
    (hD : ∀ t ∈ Metric.ball (0 : ℝ) b, ∀ x, HasDerivAt (fun u => D u x) (D' t x) t)
    (hD' : Continuous (D' 0)) {B : ℝ}
    (hB : ∀ t ∈ Metric.ball (0 : ℝ) b, ∀ x, ‖D' t x‖ ≤ B)
    {v : ℝ × Spatial → ℝ} (hvc : Continuous v) {C : ℝ} (hC : ∀ x, ‖v x‖ ≤ C)
    (hv : ∀ x p, HasDerivAt (fun y => D' 0 (y, p) * f (y, p)) (v (x, p)) x)
    {K : ℝ≥0} (hvL : ∀ p, LipschitzWith K (fun x => v (x, p))) :
    let ψ (x : ℝ × Spatial) := D' 0 x * f x
    ∃ response : ℝ → R,
      (∀ h : Height, HasDerivAt
        (fun t : ℝ => ∫ x, f x • diamond.transportedCanonicalCovariance ε h (D t x) (j t)
          ∂(volume.prod ν)) (response (h : ℝ)) 0) ∧
      Tendsto response (𝓝[>] (0 : ℝ))
        (𝓝 (((-(Real.pi * (∫ p, v (0, p) ∂ν))) • (1 : R) -
          (diamond.eta ε * ∫ x, shellFinitePartTest (transverseTest ν ψ) x) • (j 0 : R)) +
          (diamond.eta ε * ∫ x in Ioi (0 : ℝ), symmetricTest (transverseTest ν f) x) • dj)) := by
  let ψ (x : ℝ × Spatial) := D' 0 x * f x
  obtain ⟨A, hA⟩ := hfc.bounded_above_of_compact_support hfs
  obtain ⟨r, _, hr⟩ := exists_normal_support_bound hfs
  have hfLip := transverse_test_lipschitz ν hfc hA hf
  have hfSupport := transverse_test_support ν hr
  have hψc : Continuous ψ := hD'.mul hfc
  have hψA (x : ℝ × Spatial) : ‖ψ x‖ ≤ B * A := by
    have hx := hB 0 (Metric.mem_ball_self hb) x
    rw [show ψ x = D' 0 x * f x from rfl, norm_mul]
    exact mul_le_mul hx (hA x) (norm_nonneg _) ((norm_nonneg _).trans hx)
  have hψr (x : ℝ) (p : Spatial) (hx : r < |x|) : ψ (x, p) = 0 := by
    simp [ψ, hr x p hx]
  have hψSupport := transverse_test_support ν hψr
  have hvLip := transverse_test_lipschitz ν hvc hC hvL
  have hψder : ∀ x, HasDerivAt (transverseTest ν ψ) (transverseTest ν v x) x :=
    transverse_test_hasDerivAt ν hψc hvc hψA hC hv
  refine ⟨fun h : ℝ =>
    (((∫ x, sameSideImag h x * transverseTest ν ψ x) • (1 : R) -
      (diamond.eta ε * ∫ x, sameSideReal h x * transverseTest ν ψ x) • (j 0 : R)) +
      (diamond.eta ε * ∫ x, polePV h x * transverseTest ν f x) • dj), ?_, ?_⟩
  · intro h
    have hder := diamond.tested_canonical_covariance_measure_hasDerivAt ε h
      (volume.prod ν) hj hjSq hfc hfs ht hb hD hD' hB
    have hPos : 0 < (h : ℝ) := h.property
    have hPV : Continuous (polePV (h : ℝ)) :=
      continuous_iff_continuousAt.mpr fun x => (polePV_hasDerivAt hPos x).continuousAt
    have hRe : Continuous (sameSideReal (h : ℝ)) :=
      Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
    have hIm : Continuous (sameSideImag (h : ℝ)) :=
      Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
    have hrw {k : ℝ → ℝ} (hk : Continuous k) :
        (∫ x : ℝ × Spatial, k (D 0 x) * ψ x ∂(volume.prod ν)) =
          ∫ x, k x * transverseTest ν ψ x := by
      simpa only [smul_eq_mul, h0] using chart_integral_smul ν hψc hψA hψr hk
    have hpw :
        (∫ x : ℝ × Spatial, polePV (h : ℝ) (D 0 x) * f x ∂(volume.prod ν)) =
          ∫ x, polePV (h : ℝ) x * transverseTest ν f x := by
      simpa only [smul_eq_mul, h0] using chart_integral_smul ν hfc hA hr hPV
    dsimp only at hder
    rw [hrw hIm, hrw hRe, hpw] at hder
    exact hder
  · exact diamond.canonical_boundary_response_limit ε (j 0) dj hfLip hfSupport
      hψder hψSupport hvLip

end UV.SectorPlane
