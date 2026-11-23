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

/-- Restrict a punctured carrier-frequency limit to the two characters of
the prescribed vectorial pole, retaining the assigned unit and positive height. -/
theorem Plane.pole_character_limits {E X : Type*} [NormedAddCommGroup E] [TopologicalSpace X]
    (diamond : Plane E) (ε : Evolution) (p : ℝ) {F : ℂ → X} {v : X}
    (hF : Tendsto F (𝓝[≠] (p : ℂ)) (𝓝 v)) :
    Tendsto (fun h : Height =>
      let z := quotientCharacterEquiv (diamond.poleDenominator ε h p)
      (F z.1, F z.2)) poleBoundaryHeights (𝓝 (v, v)) := by
  have hη : diamond.eta ε ≠ 0 := fun he => by simpa [he] using diamond.eta_sq ε
  have h₁ := hF.comp (wilson_energy_rim_tendsto hη p)
  have h₂ := hF.comp (wilson_energy_rim_tendsto (neg_ne_zero.mpr hη) p)
  simpa [Plane.poleDenominator, directed, Function.comp_apply, sub_eq_add_neg]
    using h₁.prodMk_nhds h₂

theorem Plane.pole_characters_nonreal {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε : Evolution) (p : ℝ) (h : Height) :
    let z := quotientCharacterEquiv (diamond.poleDenominator ε h p)
    z.1.im ≠ 0 ∧ z.2.im ≠ 0 := by
  have hη : diamond.eta ε ≠ 0 := fun he => by simpa [he] using diamond.eta_sq ε
  simp [Plane.poleDenominator, directed, hη, h.property.ne']

/-- The same boundary limit for observables defined only at nonreal energies
and identified there with a local continuation. -/
theorem Plane.pole_nonreal_character_limits {E X : Type*} [NormedAddCommGroup E] [TopologicalSpace X]
    (diamond : Plane E) (ε : Evolution) (p : ℝ) {F : ℂ → X} {G : (z : ℂ) → z.im ≠ 0 → X} {v : X}
    (hF : Tendsto F (𝓝[≠] (p : ℂ)) (𝓝 v))
    (hG : ∀ᶠ z in 𝓝 (p : ℂ), ∀ hz, F z = G z hz) :
    Tendsto (fun h : Height =>
      let z := quotientCharacterEquiv (diamond.poleDenominator ε h p)
      let hn := diamond.pole_characters_nonreal ε p h
      (G z.1 hn.1, G z.2 hn.2)) poleBoundaryHeights (𝓝 (v, v)) := by
  have hpair := diamond.pole_character_limits ε p (F := id) (v := (p : ℂ))
    (tendsto_id.mono_right nhdsWithin_le_nhds)
  apply (diamond.pole_character_limits ε p hF).congr'
  filter_upwards [hpair.fst_nhds.eventually hG, hpair.snd_nhds.eventually hG] with h h₁ h₂
  exact Prod.ext (h₁ _) (h₂ _)

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
  exact diamond.pole_character_limits ε M (D.rest_weight_limit hlam hM hd)

end UV.SectorPlane
