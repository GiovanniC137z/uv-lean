import UV.ContinueRadialPhotonSlab

/-! A positive static contribution to the stationary covariance is tested
by long constant carrier-time probes. -/

noncomputable section

namespace UV.RadialPhoton

open MeasureTheory Set Real

/-- A nonnegative static atom gives weight S times the square of the
zero-frequency readout. The free upper form bound excludes any such atom. -/
theorem radial_photon_no_static_atom {k S : ℝ} (hk : 0 < k) (hS : 0 ≤ S)
    (G : (ℝ → ℝ) → ℝ)
    (hupper : ∀ j, MemLp j 2 volume → G j ≤ timeProbeCovariance (fun _ => k^2) j)
    (hstatic : ∀ j : ℝ → ℝ, Integrable j → MemLp j 2 volume → S*(∫ t, j t)^2 ≤ G j) :
    S = 0 := by
  by_contra h
  have hpos := hS.lt_of_ne (Ne.symm h)
  let T := 2/(k^2*S)
  have hT : 0 < T := by dsimp [T]; positivity
  let I := Icc (0:ℝ) T
  let j : ℝ → ℝ := I.indicator (fun _ => 1)
  have hfin : volume I ≠ ⊤ := by simp [I,Real.volume_Icc]
  have hj : MemLp j 2 volume := memLp_indicator_const 2 measurableSet_Icc _ (Or.inr hfin)
  have h1 : MemLp j 1 volume := memLp_indicator_const 1 measurableSet_Icc _ (Or.inr hfin)
  have hi : (∫ t, j t) = T := by
    simpa only [j,I,Real.volume_real_Icc_of_le hT.le,sub_zero] using
      (integral_indicator_one (μ := (volume : Measure ℝ)) (s := I) measurableSet_Icc)
  have hs : (fun t => (j t)^2) = j := by
    funext t
    by_cases ht : t ∈ I <;> simp [j,ht]
  have hb := (hstatic j (memLp_one_iff_integrable.mp h1) hj).trans
    ((hupper j hj).trans (free_time_probe_covariance_le (sq_pos_of_pos hk) hj))
  rw [hs,hi,le_div_iff₀ (sq_pos_of_pos hk)] at hb
  have he : S*T^2*k^2 = 2*T := by dsimp [T]; field_simp
  linarith only [hb,he,hT]

end UV.RadialPhoton
