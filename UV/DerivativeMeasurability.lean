import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Tactic

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV

/-- A fixed directional derivative is measurable as the limit of measurable
point-sample difference quotients. -/
theorem aestronglyMeasurable_fderiv_apply_of_point_samples
    {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [MeasurableSpace X] {μ : Measure X} {F : H → X → ℂ} {c : H}
    (hF : ∀ z, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℂ (fun z => F z x) c) (v : H) :
    AEStronglyMeasurable (fun x => fderiv ℂ (fun z => F z x) c v) μ := by
  let t : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have ht : Tendsto t atTop (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  have htne : Tendsto t atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht, Eventually.of_forall ?_⟩
    intro n
    dsimp only [t, mem_compl_iff, mem_singleton_iff]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n x => (t n)⁻¹ • (F (c + t n • v) x - F c x))
  · intro n
    exact ((hF (c + t n • v)).sub (hF c)).const_smul ((t n)⁻¹)
  filter_upwards [hd] with x hx
  have hinner : HasDerivAt (fun z : ℂ => c + z • v) v 0 := by
    simpa only [one_smul] using
      ((hasDerivAt_id (0 : ℂ)).smul_const v |>.const_add c)
  have hh' : HasDerivAt (fun z : ℂ => F (c + z • v) x)
      (fderiv ℂ (fun z => F z x) c v) 0 := by
    have houter : HasFDerivAt (fun z : H => F z x)
        (fderiv ℂ (fun z : H => F z x) c) c := hx.hasFDerivAt
    simpa only [Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt_of_eq (f := fun z : ℂ => c + z • v)
        (0 : ℂ) houter hinner (by simp)
  simpa only [zero_add, zero_smul, add_zero] using hh'.tendsto_slope_zero.comp htne

/-- Finite-dimensional complex Fréchet derivatives are measurable in an
external parameter whenever all point samples are measurable and the source
is differentiable almost everywhere at the evaluation point. -/
theorem aestronglyMeasurable_fderiv_of_point_samples
    {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [FiniteDimensional ℂ H] [MeasurableSpace X] {μ : Measure X}
    {F : H → X → ℂ} {c : H}
    (hF : ∀ z, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℂ (fun z => F z x) c) :
    AEStronglyMeasurable (fun x => fderiv ℂ (fun z => F z x) c) μ := by
  classical
  let b := Module.finBasis ℂ H
  let coordinate : Fin (Module.finrank ℂ H) → H →L[ℂ] ℂ := fun i =>
    (ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap
  have hc : ∀ i, AEStronglyMeasurable
      (fun x => (fderiv ℂ (fun z => F z x) c (b i)) • coordinate i) μ := by
    intro i
    exact (aestronglyMeasurable_fderiv_apply_of_point_samples hF hd (b i)).smul_const _
  have hs : AEStronglyMeasurable
      (fun x => ∑ i, (fderiv ℂ (fun z => F z x) c (b i)) • coordinate i) μ := by
    exact Finset.univ.aestronglyMeasurable_fun_sum (fun i _ => hc i)
  convert hs using 1
  funext x
  apply ContinuousLinearMap.coe_injective
  apply b.ext
  intro i
  simp [coordinate, Finsupp.single_apply]

end UV
