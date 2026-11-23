import UV.AdvanceSpectrumCompletion
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Order.DenselyOrdered

/-! A finite measure on the compact spectral coordinate is determined by
its resolvent values. The proof recovers its moments at the reference
argument and uses polynomial approximation. -/

noncomputable section

namespace UV.RevisionSpectrum

open Filter MeasureTheory Set
open scoped Topology

private abbrev CompactSpectralCoordinate := Set.Icc (0 : ℝ) 1

private def compactSpectralResolvent (μ : Measure CompactSpectralCoordinate)
    (n : ℕ) (h : ℝ) : ℝ :=
  ∫ t : CompactSpectralCoordinate, (t : ℝ) ^ n / (1 + h * t) ∂μ

private theorem compact_spectral_weight_bound (n : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (t : CompactSpectralCoordinate) : ‖(t : ℝ) ^ n / (1 + h * t)‖ ≤ 1 := by
  have hpos : (0 : ℝ) < 1 + h * t := by linarith [mul_nonneg hh t.property.1]
  rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg t.property.1 _) hpos.le), div_le_one hpos]
  exact (pow_le_one₀ t.property.1 t.property.2).trans (by linarith [mul_nonneg hh t.property.1])

private theorem compact_spectral_weight_integrable (μ : Measure CompactSpectralCoordinate)
    [IsFiniteMeasure μ] (n : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun t : CompactSpectralCoordinate => (t : ℝ) ^ n / (1 + h * t)) μ := by
  have hm : Measurable (fun t : CompactSpectralCoordinate => (t : ℝ) ^ n / (1 + h * t)) :=
    (measurable_subtype_coe.pow_const n).div (measurable_const.add
      (measurable_const.mul measurable_subtype_coe))
  exact Integrable.of_bound hm.aestronglyMeasurable 1
    (Eventually.of_forall (compact_spectral_weight_bound n hh))

private theorem compact_spectral_weight_limit (μ : Measure CompactSpectralCoordinate)
    [IsFiniteMeasure μ] (n : ℕ) :
    Tendsto (compactSpectralResolvent μ n) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t : CompactSpectralCoordinate, (t : ℝ) ^ n ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact (compact_spectral_weight_integrable μ n (mem_Ioi.mp hh).le).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact Eventually.of_forall (compact_spectral_weight_bound n (mem_Ioi.mp hh).le)
  · exact integrable_const _
  · refine Eventually.of_forall fun t => ?_
    have hD : Continuous (fun h : ℝ => 1 + h * (t : ℝ)) := by fun_prop
    have hn : (1 + (0 : ℝ) * (t : ℝ)) ≠ 0 := by simp
    have ht := (continuousAt_const (y := (t : ℝ) ^ n)).div (hD.continuousAt (x := 0)) hn
    simpa only [Pi.div_apply, zero_mul, add_zero, div_one] using
      ht.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)

private theorem compact_spectral_resolvent_succ (μ : Measure CompactSpectralCoordinate)
    [IsFiniteMeasure μ] (n : ℕ) {h : ℝ} (hh : 0 < h) :
    h * compactSpectralResolvent μ (n + 1) h =
      (∫ t : CompactSpectralCoordinate, (t : ℝ) ^ n ∂μ) - compactSpectralResolvent μ n h := by
  have hi := compact_spectral_weight_integrable μ n (h := 0) le_rfl
  simp only [zero_mul, add_zero, div_one] at hi
  rw [compactSpectralResolvent, compactSpectralResolvent, ← integral_const_mul,
    ← integral_sub hi (compact_spectral_weight_integrable μ n hh.le)]
  apply integral_congr_ae
  refine Eventually.of_forall fun t => ?_
  have hden : (0 : ℝ) < 1 + h * (t : ℝ) := by
    linarith [mul_nonneg hh.le t.property.1]
  field_simp [hden.ne']
  ring

private def compactSpectralIntegral (μ : Measure CompactSpectralCoordinate) [IsFiniteMeasure μ] :
    C(CompactSpectralCoordinate, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t, f t ∂μ
      map_add' := fun f g => integral_add (f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace f)) (g.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace g))
      map_smul' := fun c f => integral_smul c (fun t => f t) }
    (μ.real univ) (fun f => by
      rw [mul_comm]
      exact norm_integral_le_of_norm_le_const (Eventually.of_forall f.norm_coe_le_norm))

/-- All moments on the normalized compact interval determine its measure. -/
theorem compact_spectral_measure_eq_of_moments {μ ν : Measure CompactSpectralCoordinate}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ n : ℕ, (∫ t : CompactSpectralCoordinate, (t : ℝ) ^ n ∂μ) =
      ∫ t : CompactSpectralCoordinate, (t : ℝ) ^ n ∂ν) : μ = ν := by
  let F := compactSpectralIntegral μ
  let G := compactSpectralIntegral ν
  have hpoly (p : Polynomial ℝ) :
      F (Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1) p) =
        G (Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1) p) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial n r =>
      simpa only [F, G, compactSpectralIntegral, LinearMap.mkContinuous_apply,
        LinearMap.coe_mk, AddHom.coe_mk, Polynomial.toContinuousMapOnAlgHom_apply,
        Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
        Polynomial.eval_monomial, integral_const_mul] using congrArg (fun z : ℝ => r * z) (hm n)
  have hAll : ∀ f : C(CompactSpectralCoordinate, ℝ), F f = G f := by
    intro f
    apply (isClosed_eq F.continuous G.continuous).closure_subset_iff.mpr ?_
      (continuousMap_mem_polynomialFunctions_closure 0 1 f)
    intro g hg
    change g ∈ (polynomialFunctions (Set.Icc (0 : ℝ) 1) : Set C(CompactSpectralCoordinate, ℝ)) at hg
    rw [polynomialFunctions_coe] at hg
    obtain ⟨p, rfl⟩ := hg
    exact hpoly p
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact hAll f.toContinuousMap

/-- Equality of the compact resolvents on the positive real ray gives
equality of the normalized weighted measures. -/
theorem compact_spectral_measure_eq_of_resolvent {μ ν : Measure CompactSpectralCoordinate}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (he : ∀ h : ℝ, 0 < h →
      (∫ t : CompactSpectralCoordinate, (1 + h * (t : ℝ))⁻¹ ∂μ) =
        ∫ t : CompactSpectralCoordinate, (1 + h * (t : ℝ))⁻¹ ∂ν) : μ = ν := by
  letI : (𝓝[>] (0 : ℝ)).NeBot := nhdsGT_neBot _
  have hn : ∀ n : ℕ, ∀ h : ℝ, 0 < h → compactSpectralResolvent μ n h =
      compactSpectralResolvent ν n h := by
    intro n
    induction n with
    | zero => simpa only [compactSpectralResolvent, pow_zero, one_div] using he
    | succ n ih =>
      have hm := (compact_spectral_weight_limit μ n).congr'
        (eventually_nhdsWithin_of_forall (s := Ioi (0 : ℝ)) ih)
      have hme := tendsto_nhds_unique hm (compact_spectral_weight_limit ν n)
      intro h hh
      apply mul_left_cancel₀ hh.ne'
      rw [compact_spectral_resolvent_succ μ n hh, compact_spectral_resolvent_succ ν n hh,
        hme, ih h hh]
  apply compact_spectral_measure_eq_of_moments
  intro n
  exact tendsto_nhds_unique ((compact_spectral_weight_limit μ n).congr'
    (eventually_nhdsWithin_of_forall (s := Ioi (0 : ℝ)) (hn n))) (compact_spectral_weight_limit ν n)

end UV.RevisionSpectrum
