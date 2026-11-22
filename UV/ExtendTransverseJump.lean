import UV.ExtendTransverseChart

/-! The regular-shell numerator jump with transverse integration and
uniform C¹ multiplier errors. Both character sides are extracted from
the same plane's vectorial inverse. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

/-- Compact regular-chart data after multiplication by the test and the
fixed coarea density. The positive-height numerator is base + error. -/
structure ShellChartNumerator where
  radius : ℝ
  radius_pos : 0 < radius
  base : ℝ × Spatial → ℂ
  base_continuous : Continuous base
  baseBound : ℝ
  base_norm : ∀ x, ‖base x‖ ≤ baseBound
  baseLip : ℝ≥0
  base_lipschitz : ∀ p, LipschitzWith baseLip (fun D => base (D, p))
  base_support : ∀ D p, radius < |D| → base (D, p) = 0
  error : ℝ → ℝ × Spatial → ℂ
  errorDeriv : ℝ → ℝ × Spatial → ℂ
  error_continuous : ∀ h > 0, Continuous (error h)
  errorDeriv_continuous : ∀ h > 0, Continuous (errorDeriv h)
  error_hasDerivAt : ∀ h > 0, ∀ D p,
    HasDerivAt (fun x => error h (x, p)) (errorDeriv h (D, p)) D
  errorBound : ℝ → ℝ
  errorDerivBound : ℝ → ℝ≥0
  error_norm : ∀ h > 0, ∀ x, ‖error h x‖ ≤ errorBound h
  errorDeriv_norm : ∀ h > 0, ∀ x, ‖errorDeriv h x‖ ≤ (errorDerivBound h : ℝ)
  error_support : ∀ h > 0, ∀ D p, radius < |D| → error h (D, p) = 0
  error_bound_zero : Tendsto errorBound (𝓝[>] (0 : ℝ)) (𝓝 0)
  errorDeriv_bound_zero : Tendsto (fun h => (errorDerivBound h : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0)

variable {E : Type*} [NormedAddCommGroup E]

def Plane.transversePoleTest (diamond : Plane E) (ε : Evolution)
    (ν : Measure Spatial) (n : ShellChartNumerator) (h : ℝ) : ℂ :=
  if hh : 0 < h then
    ∫ x : ℝ × Spatial, diamond.poleCoefficient ε ⟨h, hh⟩ x.1 *
      (n.base x + n.error h x) ∂(volume.prod ν)
  else 0

theorem Plane.transverse_pole_test_limit (diamond : Plane E) (ε : Evolution)
    (ν : Measure Spatial) [IsFiniteMeasure ν] (n : ShellChartNumerator) :
    Tendsto (diamond.transversePoleTest ε ν n) (𝓝[>] (0 : ℝ))
      (𝓝 (complexShellPV (transverseTest ν n.base) -
        Complex.I * (diamond.eta ε : ℂ) * ((Real.pi : ℂ) * transverseTest ν n.base 0))) := by
  let m : ℝ≥0 := ⟨ν.real univ, measureReal_nonneg⟩
  have hLip := transverse_test_lipschitz ν n.base_continuous n.base_norm n.base_lipschitz
  have hCs : Tendsto (fun h => (m : ℝ) * n.errorBound h) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using n.error_bound_zero.const_mul (m : ℝ)
  have hLs : Tendsto (fun h => ((m * n.errorDerivBound h : ℝ≥0) : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using n.errorDeriv_bound_zero.const_mul (m : ℝ)
  have hh := diamond.tested_pole_varying_numerator_limit ε hLip
    (transverse_test_support ν n.base_support) (e := fun h => transverseTest ν (n.error h))
    (e' := fun h => transverseTest ν (n.errorDeriv h))
    (L := fun h => m * n.errorDerivBound h) (C := fun h => (m : ℝ) * n.errorBound h)
    n.radius_pos
    (fun h hh D => transverse_test_hasDerivAt ν (n.error_continuous h hh)
      (n.errorDeriv_continuous h hh) (n.error_norm h hh) (n.errorDeriv_norm h hh)
      (n.error_hasDerivAt h hh) D)
    (fun h hh D => transverse_test_norm_le ν (fun p => n.errorDeriv_norm h hh (D, p)))
    (fun h hh D => transverse_test_norm_le ν (fun p => n.error_norm h hh (D, p)))
    (fun h hh D hd => by simp only [transverseTest, n.error_support h hh D _ hd, integral_zero])
    hLs hCs
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : 0 < h := hh
  have hf : Continuous (fun x => n.base x + n.error h x) :=
    n.base_continuous.add (n.error_continuous h hp)
  have hb (x : ℝ × Spatial) : ‖n.base x + n.error h x‖ ≤ n.baseBound + n.errorBound h :=
    (norm_add_le _ _).trans (add_le_add (n.base_norm x) (n.error_norm h hp x))
  have hs (D : ℝ) (p : Spatial) (hd : n.radius < |D|) :
      n.base (D, p) + n.error h (D, p) = 0 := by
    rw [n.base_support D p hd, n.error_support h hp D p hd, add_zero]
  simp only [Plane.transversePoleTest, dif_pos hp]
  rw [chart_integral_mul ν hf hb hs (diamond.pole_coefficient_continuous ε ⟨h, hp⟩)]
  apply integral_congr_ae
  refine Eventually.of_forall fun D => ?_
  have hbi : Integrable (fun p => n.base (D, p)) ν :=
    Integrable.of_bound
      ((n.base_continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      n.baseBound (Eventually.of_forall fun p => n.base_norm (D, p))
  have hei : Integrable (fun p => n.error h (D, p)) ν :=
    Integrable.of_bound
      (((n.error_continuous h hp).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (n.errorBound h) (Eventually.of_forall fun p => n.error_norm h hp (D, p))
  dsimp only [transverseTest]
  rw [integral_add hbi hei]

/-- Full compact chart jump, with the chart Jacobian already in its
tested numerator. The two signs select the auxiliary boundary sides. -/
theorem Plane.transverse_pole_jump (diamond : Plane E) (εPos εNeg : Evolution)
    (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    (ν : Measure Spatial) [IsFiniteMeasure ν] (pos neg : ShellChartNumerator) :
    Tendsto (fun h => diamond.transversePoleTest εPos ν pos h -
      diamond.transversePoleTest εNeg ν neg h) (𝓝[>] (0 : ℝ))
      (𝓝 (complexShellPV (fun D => transverseTest ν pos.base D - transverseTest ν neg.base D) -
        Complex.I * (Real.pi : ℂ) * (∫ p, (pos.base (0, p) + neg.base (0, p)) ∂ν))) := by
  have hp := transverse_test_lipschitz ν pos.base_continuous pos.base_norm pos.base_lipschitz
  have hn := transverse_test_lipschitz ν neg.base_continuous neg.base_norm neg.base_lipschitz
  have hiP := hp.continuous.integrable_of_hasCompactSupport (μ := volume)
    (transverse_test_support ν pos.base_support)
  have hiN := hn.continuous.integrable_of_hasCompactSupport (μ := volume)
    (transverse_test_support ν neg.base_support)
  have hp₀ : Integrable (fun p => pos.base (0, p)) ν :=
    Integrable.of_bound (pos.base_continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable pos.baseBound
      (Eventually.of_forall fun p => pos.base_norm (0, p))
  have hn₀ : Integrable (fun p => neg.base (0, p)) ν :=
    Integrable.of_bound (neg.base_continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable neg.baseBound
      (Eventually.of_forall fun p => neg.base_norm (0, p))
  rw [complex_shell_pv_sub hp hn hiP hiN, integral_add hp₀ hn₀]
  have h := (diamond.transverse_pole_test_limit εPos ν pos).sub
    (diamond.transverse_pole_test_limit εNeg ν neg)
  rw [hPos, hNeg] at h
  convert h using 2
  dsimp only [transverseTest]
  push_cast
  ring

/-- A common boundary numerator gives the exact weighted delta jump
over the entire compact transverse chart. -/
theorem Plane.transverse_common_numerator_pole_jump (diamond : Plane E) (εPos εNeg : Evolution)
    (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    (ν : Measure Spatial) [IsFiniteMeasure ν] (pos neg : ShellChartNumerator)
    (hbase : pos.base = neg.base) :
    Tendsto (fun h => diamond.transversePoleTest εPos ν pos h -
      diamond.transversePoleTest εNeg ν neg h) (𝓝[>] (0 : ℝ))
      (𝓝 (-(2 * (Real.pi : ℂ) * Complex.I * (∫ p, pos.base (0, p) ∂ν)))) := by
  have h := diamond.transverse_pole_jump εPos εNeg hPos hNeg ν pos neg
  rw [← hbase] at h
  have hz : (complexShellPV fun D => transverseTest ν pos.base D - transverseTest ν pos.base D) = 0 := by
    simp [complexShellPV, symmetricTest]
  rw [hz, zero_sub] at h
  have hi : Integrable (fun p => pos.base (0, p)) ν :=
    Integrable.of_bound (pos.base_continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable pos.baseBound
      (Eventually.of_forall fun p => pos.base_norm (0, p))
  rw [integral_add hi hi] at h
  convert h using 2
  ring

theorem Plane.transverse_directed_pole_jump (diamond : Plane E) (εPos εNeg : Evolution)
    (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    (ν : Measure Spatial) [IsFiniteMeasure ν] (pos neg : ShellChartNumerator) :
    Tendsto (fun h => directed (diamond.transversePoleTest εPos ν pos h -
      diamond.transversePoleTest εNeg ν neg h)) (𝓝[>] (0 : ℝ))
      (𝓝 (directed (complexShellPV
        (fun D => transverseTest ν pos.base D - transverseTest ν neg.base D) -
        Complex.I * (Real.pi : ℂ) * (∫ p, (pos.base (0, p) + neg.base (0, p)) ∂ν)))) :=
  directed_shell_readout_continuous.continuousAt.tendsto.comp
    (diamond.transverse_pole_jump εPos εNeg hPos hNeg ν pos neg)

end UV.SectorPlane
