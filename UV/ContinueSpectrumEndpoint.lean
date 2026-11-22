import UV.ContinueSpectrumForms

/-! The positive gap makes the common spectral representation valid also
at zero Euclidean spectral argument. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology ENNReal

namespace UV.RevisionSpectrum

theorem continue_boundary_measure_gap {β b M₂ : ℝ}
    (hβ : 0<β) (hb : b<M₂) :
    ∀ᵐ s ∂resumeBulkBoundaryMeasure β b M₂,b<s := by
  unfold resumeBulkBoundaryMeasure
  rw [ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure
      ((ae_dirac_iff measurableSet_Ioi).mpr (bulkPole_unique hβ hb).1) _
  · apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hb.trans hs

private theorem continue_stieltjes_norm_bound {b y s A : ℝ}
    (hb : 0<b) (hy : 0≤y) (hs : b<s) :
    ‖A/(y+s)‖≤(1+1/b)*‖A/(1+s)‖ := by
  have hs₀ : 0<s := hb.trans hs
  have hbs : 1≤s/b := (le_div_iff₀ hb).mpr (by simpa using hs.le)
  have hbase : 1+s≤(1+1/b)*(y+s) := by
    have hdiv : s/b=s*(1/b) := by simp only [div_eq_mul_inv,one_mul]
    have hy' : 0≤(1+1/b)*y := by positivity
    nlinarith
  simp only [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0<y+s),
    abs_of_pos (by positivity : 0<1+s)]
  rw [← mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (abs_nonneg A) (sub_nonneg.mpr hbase)]

theorem continue_layer_pair_measure_nonnegative {β b M₂ x r r' : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0≤x) (hr : 0≤r) (hr' : 0≤r') :
    Integrable (fun s : ℝ =>
      continueLayerMultiplier β b M₂ r s*continueLayerMultiplier β b M₂ r' s/(x+s))
      (resumeBulkBoundaryMeasure β b M₂) ∧
    (∫ s : ℝ,
      continueLayerMultiplier β b M₂ r s*continueLayerMultiplier β b M₂ r' s/(x+s)
      ∂resumeBulkBoundaryMeasure β b M₂) = continueBulkLayerGreen β b M₂ x r r' := by
  let μ := resumeBulkBoundaryMeasure β b M₂
  let A := fun s : ℝ => continueLayerMultiplier β b M₂ r s*continueLayerMultiplier β b M₂ r' s
  let xn := fun n : ℕ => x+1/((n:ℝ)+1)
  have hxn : Tendsto xn atTop (𝓝 x) := by
    simpa [xn] using tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  have hxp (n : ℕ) : 0<xn n := by dsimp [xn]; positivity
  have hg : Integrable (fun s => (1+1/b)*‖A s/(1+s)‖) μ :=
    (continue_layer_pair_measure hβ hb₀ hb (by norm_num : (0:ℝ)<1) hr hr').1.norm.const_mul _
  have hmeas (y : ℝ) : AEStronglyMeasurable (fun s => A s/(y+s)) μ := by
    apply Measurable.aestronglyMeasurable
    dsimp [A]
    exact ((continueLayerMultiplier_continuous _ _ _ _).mul
      (continueLayerMultiplier_continuous _ _ _ _)).measurable.div (by fun_prop)
  have hi : Integrable (fun s => A s/(x+s)) μ := by
    apply hg.mono' (hmeas x)
    filter_upwards [continue_boundary_measure_gap hβ hb] with s hs
    exact continue_stieltjes_norm_bound hb₀ hx hs
  refine ⟨hi,?_⟩
  have hL : Tendsto (fun n : ℕ => ∫ s,A s/(xn n+s) ∂μ) atTop
      (𝓝 (∫ s,A s/(x+s) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun s => (1+1/b)*‖A s/(1+s)‖)
    · intro n
      exact hmeas (xn n)
    · exact hg
    · intro n
      filter_upwards [continue_boundary_measure_gap hβ hb] with s hs
      exact continue_stieltjes_norm_bound hb₀ (hxp n).le hs
    · filter_upwards [continue_boundary_measure_gap hβ hb] with s hs
      exact tendsto_const_nhds.div (hxn.add_const s)
        (show x+s≠0 by exact (add_pos_of_nonneg_of_pos hx (hb₀.trans hs)).ne')
  have hM : 0<M₂ := hb₀.trans hb
  have hsqrt : 0<Real.sqrt (x+M₂) := Real.sqrt_pos.mpr (by positivity)
  have hG : ContinuousAt (fun y => continueBulkLayerGreen β b M₂ y r r') x := by
    unfold continueBulkLayerGreen
    fun_prop (disch:=positivity)
  apply tendsto_nhds_unique hL
  apply (hG.tendsto.comp hxn).congr'
  exact Eventually.of_forall fun n =>
    (continue_layer_pair_measure hβ hb₀ hb (hxp n) hr hr').2.symm

end UV.RevisionSpectrum
