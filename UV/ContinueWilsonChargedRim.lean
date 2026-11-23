import UV.ContinueWilsonChargedPole
import UV.MassiveRunningPole

/-! Evaluation of the charged spectral coefficient on both characters of
the directed energy rim of a fixed sector-plane at zero spatial momentum. -/

noncomputable section

open Filter Set UV.Carrier
open scoped Topology

namespace UV.SectorPlane

private theorem wilson_energy_rim_tendsto {η : ℝ} (hη : η ≠ 0) (M : ℝ) :
    Tendsto (fun h : Height => (M:ℂ)+Complex.I*((η*(h:ℝ):ℝ):ℂ)) poleBoundaryHeights (𝓝[≠] (M:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun t : ℝ => (M:ℂ)+Complex.I*((η*t:ℝ):ℂ)) := by fun_prop
    simpa only [mul_zero,Complex.ofReal_zero,add_zero] using hc.continuousAt.tendsto.comp pole_height_tendsto_zero
  · apply Eventually.of_forall
    intro h
    change (M:ℂ)+Complex.I*((η*(h:ℝ):ℝ):ℂ) ≠ (M:ℂ)
    simpa only [ne_eq,add_eq_left,mul_eq_zero,Complex.I_ne_zero,false_or,Complex.ofReal_eq_zero]
      using (mul_ne_zero hη h.property.ne')

/-- The time-spin eigenvalue belongs to the numerator. Orientation enters
through `poleDenominator` with the stored unit GT direction. Both characters
recover the same coefficient of `1/(M-z)` at a simple real rest pole. -/
theorem Plane.charged_rest_vectorial_weights {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε : Evolution) {L lam σ M : ℝ} (D : UV.WilsonRestLaw L)
    (hlam : 0 < lam) (hM : D.block σ 0 M = lam⁻¹) (hd : 0 < D.block σ 1 M) :
    let Z := ((σ*L/(lam*D.block σ 1 M):ℝ):ℂ)
    Tendsto (fun h =>
      let z := quotientCharacterEquiv (diamond.poleDenominator ε h M)
      (((M:ℂ)-z.1)*D.restEndpoint lam σ z.1, ((M:ℂ)-z.2)*D.restEndpoint lam σ z.2))
      poleBoundaryHeights (𝓝 (Z,Z)) := by
  have hη : diamond.eta ε ≠ 0 := fun he => by simpa [he] using diamond.eta_sq ε
  have h := D.rest_weight_limit hlam hM hd
  have h₁ := h.comp (wilson_energy_rim_tendsto hη M)
  have h₂ := h.comp (wilson_energy_rim_tendsto (neg_ne_zero.mpr hη) M)
  simpa [Plane.poleDenominator,directed,Function.comp_apply,sub_eq_add_neg] using h₁.prodMk_nhds h₂

end UV.SectorPlane
