import UV.ContinueSewnAnalyticSlice
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Analytic nonidentity gives a uniformly nonzero finite directional
derivative near each zero. All chosen directions have norm one. -/

noncomputable section
open Real Set Filter
open scoped Topology
namespace UV.SewnFlags

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero analytic germ cannot have every diagonal Taylor derivative zero. -/
private theorem exists_diagonal_derivative {U : Set E} {f : E → ℝ} {x : E}
    (ha : AnalyticOnNhd ℝ f U) (hU : IsPreconnected U) (hx : x ∈ U)
    (hnon : ¬ EqOn f 0 U) :
    ∃ (m : ℕ) (v : E), iteratedFDeriv ℝ m f x (fun _ => v) ≠ 0 := by
  by_contra! h
  apply hnon (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hx ?_)
  obtain ⟨p,R,hp⟩ := ha x hx
  filter_upwards [EMetric.ball_mem_nhds x hp.r_pos] with y hy
  have hy' : y-x ∈ EMetric.ball 0 R := by simpa [EMetric.mem_ball, edist_eq_enorm_sub] using hy
  have hs := hp.hasSum_iteratedFDeriv hy'
  simpa [h, add_sub_cancel] using hs.tsum_eq.symm

/-- The unit direction and derivative order can depend on the chart point;
the lower bound then holds on a whole neighborhood of that point. -/
theorem analytic_unit_direction_at_zero {U : Set E} {f : E → ℝ} {x : E}
    (ha : AnalyticOnNhd ℝ f U) (hU : IsPreconnected U) (hx : x ∈ U)
    (hnon : ¬ EqOn f 0 U) (hz : f x = 0) :
    ∃ (m : ℕ) (v : {w : E // ‖w‖ = 1}) (c : ℝ), 0 < m ∧ 0 < c ∧
      ∀ᶠ y in 𝓝 x, c ≤ |iteratedFDeriv ℝ m f y (fun _ => v.val)| := by
  obtain ⟨m,w,hw⟩ := exists_diagonal_derivative ha hU hx hnon
  have hm : 0 < m := by
    by_contra! h; have := Nat.eq_zero_of_le_zero h; subst m
    simp [iteratedFDeriv_zero_apply, hz] at hw
  have hw₀ : w ≠ 0 := by
    intro he
    exact hw ((iteratedFDeriv ℝ m f x).map_coord_zero ⟨0,hm⟩ he)
  let v := ‖w‖⁻¹ • w
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw₀)]
  have hvnz : iteratedFDeriv ℝ m f x (fun _ => v) ≠ 0 := by
    have he := (iteratedFDeriv ℝ m f x).map_smul_univ (fun _ => ‖w‖⁻¹) (fun _ => w)
    simp [v, he, smul_eq_mul, hw, hw₀]
  let D (y : E) := iteratedFDeriv ℝ m f y (fun _ => v)
  have hD : ContinuousAt D x := by
    have hF : ContinuousAt (iteratedFDeriv ℝ m f) x :=
      (((ha x hx).contDiffAt : ContDiffAt ℝ (m : ℕ) f x).iteratedFDeriv_right (m := 0) (by simp)).continuousAt
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => E) ℝ (fun _ => v)).continuous.continuousAt.comp hF)
  have hpos : 0 < |D x| := abs_pos.mpr hvnz
  refine ⟨m,⟨v,hv⟩,|D x|/2,hm,half_pos hpos,?_⟩
  exact (hD.abs.tendsto.eventually_const_lt (half_lt_self hpos)).mono fun _ h => h.le

/-- The chart's directional derivative is the ordinary derivative on its real
affine line. The finite difference argument is applied to this same restriction. -/
theorem analytic_affine_line_derivative {U : Set E} {f : E → ℝ}
    (hU : IsOpen U) (ha : AnalyticOnNhd ℝ f U) (y v : E) (t : ℝ) (ht : y+t • v ∈ U) (m : ℕ) :
    iteratedDeriv m (fun s : ℝ => f (y+s • v)) t =
      iteratedFDeriv ℝ m f (y+t • v) (fun _ => v) := by
  let g : ℝ →L[ℝ] E := (1 : ℝ →L[ℝ] ℝ).smulRight v
  let W := (fun z : E => y+z) ⁻¹' U
  have hW : IsOpen W := hU.preimage (continuous_const.add continuous_id)
  have hgw : IsOpen (g ⁻¹' W) := hW.preimage g.continuous
  have hgt : g t ∈ W := ht
  have hF : ContDiffOn ℝ (m : ℕ) (fun z => f (y+z)) W := by
    intro z hz
    exact (((ha _ hz).comp ((analyticAt_const.add analyticAt_id))).contDiffAt).contDiffWithinAt
  have he := g.iteratedFDerivWithin_comp_right hF hW.uniqueDiffOn hgw.uniqueDiffOn hgt (i := m) le_rfl
  rw [iteratedFDerivWithin_of_isOpen _ hW hgt, iteratedFDerivWithin_of_isOpen _ hgw hgt,
    iteratedFDeriv_comp_add_left] at he
  rw [iteratedDeriv_eq_iteratedFDeriv]
  simpa [g, Function.comp_def] using congrArg (fun D => D (fun _ => (1:ℝ))) he

end UV.SewnFlags
