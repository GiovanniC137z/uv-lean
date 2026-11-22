import UV.ExtendStablePole
import Mathlib.Analysis.Complex.RealDeriv

/-! Compact regular timelike charts of the stable-half coefficient.
The first derivative in the invariant real coordinate has the same
one-sided limit as the derivative of the exact timelike phase. -/

noncomputable section

namespace UV.SectorPlane

open Filter Set
open scoped Topology

def timelikeStable (a η : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((Complex.I * ((η * a : ℝ) : ℂ)) * principalSqrt z)

def timelikeShift (η h w : ℝ) : ℂ :=
  (w : ℂ) + Complex.I * ((η * h : ℝ) : ℂ)

private theorem timelike_uniform_chart {F : ℂ → ℂ}
    (hF : ContinuousOn F {z : ℂ | 0 < z.re}) (η : ℝ) {b c : ℝ} (hb : 0 < b) :
    TendstoUniformlyOn (fun h w => F (timelikeShift η h w))
      (fun w => F (w : ℂ)) (𝓝[>] (0 : ℝ)) (Icc b c) := by
  have hs : ContinuousOn (fun x : ℝ × ℝ => F (timelikeShift η x.1 x.2))
      (Icc (0 : ℝ) 1 ×ˢ Icc b c) := by
    apply hF.comp
    · unfold timelikeShift
      fun_prop
    · intro x hx
      change 0 < (timelikeShift η x.1 x.2).re
      simpa [timelikeShift] using hb.trans_le hx.2.1
  have h := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_Icc (a := b) (b := c))).uniformContinuousOn_of_continuous hs
  have ht := UniformContinuousOn.tendstoUniformlyOn
    (F := fun h w => F (timelikeShift η h w)) h
    (left_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1))
  have hm : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc (0 : ℝ) 1] 0 := by
    refine le_inf nhdsWithin_le_nhds (le_principal_iff.mpr ?_)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)]
      with x hx hx'
    exact ⟨(show 0 < x from hx).le, (show x < 1 from hx').le⟩
  intro u hu
  exact hm (by simpa [timelikeShift] using ht u hu)

theorem timelike_stable_hasDerivAt (a η h : ℝ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun x : ℝ => timelikeStable a η (timelikeShift η h x))
      (deriv (timelikeStable a η) (timelikeShift η h w)) w := by
  let c : ℂ := Complex.I * ((η * h : ℝ) : ℂ)
  have hz : 0 < ((w : ℂ) + c).re := by simpa [c] using hw
  have han : AnalyticAt ℂ (timelikeStable a η) ((w : ℂ) + c) :=
    stable_half_analyticOn_timed a η _ hz
  have hc := (han.differentiableAt.hasDerivAt).comp (w : ℂ)
    ((hasDerivAt_id (w : ℂ)).add_const c)
  simpa [c, timelikeShift, Function.comp_def] using hc.comp_ofReal

variable {E : Type*} [NormedAddCommGroup E]

/-- On each compact positive shell interval the actual kernel and its
invariant first derivative converge uniformly as the height vanishes. -/
theorem Plane.stable_half_timed_uniform_C1 (diamond : Plane E) (ε : Evolution) (a : ℝ)
    {b c : ℝ} (hb : 0 < b) :
    let G (w : ℝ) := Complex.exp
      (((diamond.eta ε * a * Real.sqrt w : ℝ) : ℂ) * Complex.I)
    TendstoUniformlyOn (fun h w => diamond.stableHalfCoefficient ε a w h)
      G (𝓝[>] (0 : ℝ)) (Icc b c) ∧
    TendstoUniformlyOn (fun h => deriv (fun w => diamond.stableHalfCoefficient ε a w h))
      (deriv G) (𝓝[>] (0 : ℝ)) (Icc b c) := by
  let η := diamond.eta ε
  let F := timelikeStable a η
  let G (w : ℝ) := Complex.exp (((η * a * Real.sqrt w : ℝ) : ℂ) * Complex.I)
  have hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.re} := stable_half_analyticOn_timed a η
  have hU := timelike_uniform_chart hF.continuousOn η (c := c) hb
  have hU' := timelike_uniform_chart hF.deriv.continuousOn η (c := c) hb
  have he (w : ℝ) (hw : 0 < w) : F (w : ℂ) = G w := by
    dsimp [F, G, timelikeStable]
    rw [principalSqrt_ofReal hw.le]
    push_cast
    congr 1
    ring
  have hg {w : ℝ} (hw : 0 < w) : deriv G w = deriv F (w : ℂ) := by
    have hd := timelike_stable_hasDerivAt a η 0 hw
    have hs (x : ℝ) : timelikeShift η 0 x = (x : ℂ) := by simp [timelikeShift]
    simp only [hs] at hd
    have hh : G =ᶠ[𝓝 w] (fun x => F (x : ℂ)) := by
      filter_upwards [Ioi_mem_nhds hw] with x hx
      exact (he x hx).symm
    exact (hd.congr_of_eventuallyEq hh).deriv
  have hpos (h : ℝ) (hh : 0 < h) :
      (fun w => diamond.stableHalfCoefficient ε a w h) =
        (fun w => F (timelikeShift η h w)) := by
    funext w
    exact diamond.stable_half_analytic_form ε ⟨h, hh⟩ a w
  constructor
  · refine (hU.congr_right (fun w hw => he w (hb.trans_le hw.1))).congr ?_
    filter_upwards [self_mem_nhdsWithin] with h hh w _
    exact congrFun (hpos h hh).symm w
  · have hd (h w : ℝ) (hh : 0 < h) (hw : 0 < w) :
        deriv (fun x => diamond.stableHalfCoefficient ε a x h) w =
          deriv F (timelikeShift η h w) := by
      rw [hpos h hh]
      exact (timelike_stable_hasDerivAt a η h hw).deriv
    refine (hU'.congr_right (fun w hw => (hg (hb.trans_le hw.1)).symm)).congr ?_
    filter_upwards [self_mem_nhdsWithin] with h hh w hw
    exact (hd h w hh (hb.trans_le hw.1)).symm

end UV.SectorPlane
