import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Dynamics.Ergodic.RadonNikodym
import Mathlib.Probability.Independence.Integration
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Translation-ergodic photon marginal and a pathwise invariant random
two-port kernel on a fixed reconstructed plane. The kernel takes values
in its measurable space of test coefficients. No sign or Gaussian
hypothesis on those coefficients is needed. -/

noncomputable section

namespace UV.PhotonSewing

open Function Filter Set MeasureTheory ProbabilityTheory

variable {G Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
variable [VAdd G X] [MeasurableConstVAdd G X]

private theorem invariant_submeasure (G : Type*) {X : Type*} [MeasurableSpace X]
    [VAdd G X] [MeasurableConstVAdd G X] {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [ErgodicVAdd G X μ] (hac : ν ≪ μ)
    (hν : ∀ g : G, MeasurePreserving (g +ᵥ ·) ν ν) :
    ν = ν univ • μ := by
  have hμ (g : G) : MeasurePreserving (g +ᵥ ·) μ μ := by
    refine ⟨measurable_const_vadd g, ?_⟩
    ext s hs
    rw [Measure.map_apply (measurable_const_vadd g) hs]
    exact VAddInvariantMeasure.measure_preimage_vadd g hs
  obtain ⟨c, hc⟩ : ∃ c, ν.rnDeriv μ =ᵐ[μ] const X c := by
    apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
    intro s hs
    apply eventuallyConst_set.mp
    apply ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := G) ((Measure.measurable_rnDeriv ν μ) hs)
    intro g
    have hg := (hν g).rnDeriv_comp_aeEq (hμ g)
    filter_upwards [hg] with x hx
    change (ν.rnDeriv μ (g +ᵥ x) ∈ s) = (ν.rnDeriv μ x ∈ s)
    rw [show ν.rnDeriv μ (g +ᵥ x) = ν.rnDeriv μ x from hx]
  have h : ν = c • μ := by
    ext s hs
    calc
      ν s = ∫⁻ x in s, ν.rnDeriv μ x ∂μ := (Measure.setLIntegral_rnDeriv hac _).symm
      _ = ∫⁻ _ in s, c ∂μ := lintegral_congr_ae (hc.filter_mono (ae_mono Measure.restrict_le_self))
      _ = (c • μ) s := by simp
  have hn : ν univ = c := by rw [h]; simp
  simpa only [hn] using h

/-- Independence follows from joint stationarity and ergodicity of the photon
marginal alone. The null exceptional sets may depend on the translation. -/
theorem invariant_kernel_independent (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → X) (T : Ω → Y) (hA : Measurable A) (hT : Measurable T)
    [ErgodicVAdd G X (μ.map A)] (τ : G → Ω → Ω) (hτ : ∀ g, MeasurePreserving (τ g) μ μ)
    (ha : ∀ g, A ∘ τ g =ᵐ[μ] fun ω => g +ᵥ A ω)
    (ht : ∀ g, T ∘ τ g =ᵐ[μ] T) : IndepFun T A μ := by
  haveI : IsProbabilityMeasure (μ.map A) := Measure.isProbabilityMeasure_map hA.aemeasurable
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s u hs hu
  let B := T ⁻¹' s
  have hB : MeasurableSet B := hT hs
  let ν := (μ.restrict B).map A
  have hac : ν ≪ μ.map A := by
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).map hA
  have hinv (g : G) : MeasurePreserving (g +ᵥ ·) ν ν := by
    refine ⟨measurable_const_vadd g, ?_⟩
    ext v hv
    rw [Measure.map_apply (measurable_const_vadd g) hv]
    change (μ.restrict B).map A _ = (μ.restrict B).map A v
    rw [Measure.map_apply hA ((measurable_const_vadd g) hv), Measure.map_apply hA hv,
      Measure.restrict_apply (hA ((measurable_const_vadd g) hv)), Measure.restrict_apply (hA hv)]
    rw [← (hτ g).measure_preimage (hA hv |>.inter hB).nullMeasurableSet]
    apply measure_congr
    filter_upwards [ha g, ht g] with ω h₁ h₂
    change ((g +ᵥ A ω ∈ v) ∧ T ω ∈ s) = ((A (τ g ω) ∈ v) ∧ T (τ g ω) ∈ s)
    rw [show A (τ g ω) = g +ᵥ A ω from h₁, show T (τ g ω) = T ω from h₂]
  have hn := invariant_submeasure G hac hinv
  have hmass : ν univ = μ B := by simp [ν, Measure.map_apply hA]
  have hu' := congrArg (fun ρ : Measure X => ρ u) hn
  simpa [ν, Measure.map_apply hA hu, Measure.restrict_apply (hA hu), hmass,
    Measure.smul_apply, smul_eq_mul, inter_comm, B] using hu'

/-- For a symmetric two-port Taylor weight, direct sewing is one half of
the trace of the expected kernel times the centered photon covariance.
The formula is valid for every finite family of projected coordinates. -/
theorem invariant_kernel_sewing {ι : Type*} [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → X) (T : Ω → Y) (hA : Measurable A) (hT : Measurable T)
    [ErgodicVAdd G X (μ.map A)] (τ : G → Ω → Ω) (hτ : ∀ g, MeasurePreserving (τ g) μ μ)
    (ha : ∀ g, A ∘ τ g =ᵐ[μ] fun ω => g +ᵥ A ω)
    (U : G → Y → Y) (hc : ∀ g, T ∘ τ g =ᵐ[μ] U g ∘ T)
    (hi : ∀ g, U g ∘ T =ᵐ[μ] T)
    (k : ι → ι → Y → ℝ) (a : ι → X → ℝ)
    (hk : ∀ i j, Measurable (k i j)) (hm : ∀ i, Measurable (a i))
    (hki : ∀ i j, Integrable (k i j ∘ T) μ)
    (hdi : ∀ i j, Integrable (fun ω => a i (A ω) * a j (A ω)) μ) :
    let K : Matrix ι ι ℝ := fun i j => ∫ ω, k i j (T ω) ∂μ
    let D : Matrix ι ι ℝ := fun i j => ∫ ω, a i (A ω) * a j (A ω) ∂μ
    IndepFun T A μ ∧
      (∫ ω, ∑ i, ∑ j, k i j (T ω) * (a i (A ω) * a j (A ω)) ∂μ) / 2 =
        (K * D).trace / 2 := by
  dsimp only
  have h := invariant_kernel_independent μ A T hA hT τ hτ ha (fun g => (hc g).trans (hi g))
  have h' (i j : ι) := h.comp (hk i j) ((hm i).mul (hm j))
  have hint (i j : ι) : Integrable (fun ω => k i j (T ω) * (a i (A ω)*a j (A ω))) μ :=
    (h' i j).integrable_mul (hki i j) (hdi i j)
  refine ⟨h, ?_⟩
  congr 1
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => hint i j)]
  change _ = ∑ j, (∫ ω, k i j (T ω) ∂μ) * ∫ ω, a j (A ω) * a i (A ω) ∂μ
  apply Finset.sum_congr rfl
  intro j _
  simpa only [comp_apply, Pi.mul_apply, mul_comm (a j _) (a i _)] using
    (h' i j).integral_fun_mul_eq_mul_integral (hki i j).1 (hdi i j).1

end UV.PhotonSewing
