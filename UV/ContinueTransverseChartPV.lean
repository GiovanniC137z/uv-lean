import UV.ContinueTransverseChartProduct

/-! Identifies the doubly subtracted coefficient with the actual tensor
principal-value regularization, independently of either chosen pole side. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

private theorem transverse_chart_pv_test {g : ℝ → ℂ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hs : HasCompactSupport g) :
    Tendsto (fun h : Height => ∫ x, (polePV (h : ℝ) x : ℂ) * g x) poleBoundaryHeights (𝓝 (complexShellPV g)) := by
  simpa only [Function.comp_apply, Complex.real_smul] using
    (complex_shell_pv_limit hg hs).comp (tendsto_comap :
      Tendsto (fun h : Height => (h : ℝ)) poleBoundaryHeights (𝓝[>] (0 : ℝ)))

/-- The term called PV×PV is itself the limit of the two actual
conjugate Poisson kernels at their shared height. -/
theorem Plane.transverse_normal_pv_tensor_boundary {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε : Evolution) {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ p, (polePV (h : ℝ) p.1 : ℂ) *
      (polePV (h : ℝ) p.2 : ℂ) * f p ∂transverseNormalVolume) poleBoundaryHeights
      (𝓝 (transverseNormalPV₂ f)) := by
  let P (h : Height) (x : ℝ) := (polePV (h : ℝ) x : ℂ)
  have hPc (h : Height) : Continuous (P h) :=
    Complex.continuous_ofReal.comp (continuous_iff_continuousAt.mpr fun D =>
      (polePV_hasDerivAt h.property D).continuousAt)
  have he (h : Height) (x : ℝ) : (diamond.poleCoefficient ε h x).re = polePV (h : ℝ) x := by
    rw [diamond.pole_coefficient_split]
    simp
  have hPb (h : Height) (x : ℝ) (hx : x ≠ 0) : ‖P h x‖ ≤ |x|⁻¹ := by
    dsimp only [P]
    rw [Complex.norm_real, Real.norm_eq_abs, ← he]
    exact (Complex.abs_re_le_norm _).trans (diamond.pole_coefficient_off_shell_bound ε h hx)
  have hPl (x : ℝ) (hx : x ≠ 0) :
      Tendsto (fun h => P h x) poleBoundaryHeights (𝓝 (x : ℂ)⁻¹) := by
    have H := (Complex.continuous_ofReal.comp Complex.continuous_re).continuousAt.tendsto.comp
      (diamond.pole_coefficient_off_shell_limit ε hx)
    change Tendsto (fun h : Height => ((diamond.poleCoefficient ε h x).re : ℂ)) _
      (𝓝 ((((x : ℂ)⁻¹).re : ℂ))) at H
    simpa only [he, ← Complex.ofReal_inv, Complex.ofReal_re, P] using H
  let R := transverseNormalRemainder f
  let K : TopologicalSpace.Compacts (ℝ × ℝ) := ⟨tsupport R, transverse_normal_remainder_compact hs⟩
  obtain ⟨C,_,hR⟩ := transverse_normal_remainder_bound hf hs
  have Hr := transverse_normal_remainder_moving_limit (fun _ => R) R K (C := C)
    (Eventually.of_forall fun _ => transverse_normal_remainder_continuous hf.continuous)
    (Eventually.of_forall fun _ p hp => image_eq_zero_of_notMem_tsupport hp)
    (Eventually.of_forall fun _ => hR) (fun _ => tendsto_const_nhds)
    P P hPc hPc hPb hPb hPl hPl
  obtain ⟨hsx,hsy⟩ := transverse_normal_slice_compact hs
  have hx : ContDiff ℝ 2 (fun x => f (x,0)) := hf.comp (contDiff_id.prodMk contDiff_const)
  have hy : ContDiff ℝ 2 (fun y => f (0,y)) := hf.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨_,hLx⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsx hx (by norm_num)
  obtain ⟨_,hLy⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsy hy (by norm_num)
  have Hx := transverse_chart_pv_test hLx hsx
  have Hy := transverse_chart_pv_test hLy hsy
  have Hc := transverse_chart_pv_test transverse_normal_cutoff_lipschitz transverse_normal_cutoff_compact
  rw [transverse_normal_cutoff_pv] at Hc
  have H := ((Hr.add (Hc.mul Hy)).add (Hx.mul Hc)).sub ((Hc.mul Hc).const_mul (f (0,0)))
  simp only [zero_mul, mul_zero, add_zero, sub_zero] at H
  refine H.congr fun h => ?_
  exact (transverse_normal_product_split (P h) (P h) (hPc h) (hPc h) hf.continuous hs).symm

end UV.SectorPlane
