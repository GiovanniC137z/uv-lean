import UV.DiskZeroCount
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Connected.TotallyDisconnected

/-! The actual disk zero count is constant along a continuous boundary
homotopy. The contour formula and its continuity are proved, rather than
supplied as homotopy data. -/

noncomputable section
open Set Filter Metric MeasureTheory Complex
open scoped Topology

namespace UV

/-- Joint boundary continuity gives continuity of the actual circle integral
in a real homotopy parameter, including both closed-interval endpoints. -/
theorem disk_circleIntegral_homotopy_continuous
    {F : ℝ → ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hF : ContinuousOn (fun p : ℝ × ℂ => F p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ sphere c r)) :
    ContinuousOn (fun t : ℝ => ∮ z in C(c,r), F t z) (Icc (0 : ℝ) 1) := by
  let S := Icc (0 : ℝ) 1
  have hmap : Continuous (fun p : S × ℝ => ((p.1 : ℝ), circleMap c r p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_circleMap c r).comp continuous_snd)
  have hcomp : Continuous (fun p : S × ℝ => F p.1 (circleMap c r p.2)) :=
    hF.comp_continuous hmap (fun p => ⟨p.1.property, circleMap_mem_sphere c hr p.2⟩)
  have hderiv : Continuous (fun p : S × ℝ => deriv (circleMap c r) p.2) := by
    simp_rw [deriv_circleMap]
    exact ((continuous_circleMap 0 r).comp continuous_snd).mul continuous_const
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume)
    (f := fun t : S => fun θ : ℝ => deriv (circleMap c r) θ * F t (circleMap c r θ))
    (hderiv.mul hcomp) 0 (2 * Real.pi)
  apply continuousOn_iff_continuous_restrict.mpr
  simpa only [circleIntegral, smul_eq_mul] using hi

/-- The real homotopy hypotheses concern the actual function and derivative
on the boundary. Analyticity and the argument principle then force the
integer zero count to stay constant. -/
theorem disk_zeroCount_homotopy
    {F : ℝ → ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticOnNhd ℂ (F t) (closedBall c r))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere c r, F t z ≠ 0)
    (hc : ContinuousOn (fun p : ℝ × ℂ => F p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ sphere c r))
    (hd : ContinuousOn (fun p : ℝ × ℂ => deriv (F p.1) p.2)
      (Icc (0 : ℝ) 1 ×ˢ sphere c r)) :
    ∀ t ∈ Icc (0 : ℝ) 1, diskZeroCount (F t) c r = diskZeroCount (F 0) c r := by
  have hlog : ContinuousOn (fun p : ℝ × ℂ => logDeriv (F p.1) p.2)
      (Icc (0 : ℝ) 1 ×ˢ sphere c r) := by
    exact hd.div hc (fun p hp => hb p.1 hp.1 p.2 hp.2)
  have hcircle := disk_circleIntegral_homotopy_continuous
    (F := fun t z => logDeriv (F t) z) (c := c) hr.le hlog
  have hcast : ContinuousOn (fun t : ℝ => (diskZeroCount (F t) c r : ℂ))
      (Icc (0 : ℝ) 1) := by
    have hn : ContinuousOn (fun t : ℝ => (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(c,r), logDeriv (F t) z)) (Icc (0 : ℝ) 1) :=
      continuousOn_const.mul hcircle
    apply hn.congr
    intro t ht
    exact (disk_argument_principle (hF t ht) hr (hb t ht)).symm
  have hcount : Continuous (fun t : Icc (0 : ℝ) 1 => diskZeroCount (F t) c r) := by
    apply Complex.isometry_intCast.isEmbedding.isInducing.continuous_iff.mpr
    exact hcast.restrict
  have hcountOn : ContinuousOn (fun t : ℝ => diskZeroCount (F t) c r)
      (Icc (0 : ℝ) 1) := continuousOn_iff_continuous_restrict.mpr hcount
  intro t ht
  exact isPreconnected_Icc.constant hcountOn ht (by norm_num)

end UV
