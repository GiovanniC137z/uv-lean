import UV.ContinueCollarEigenmode
import UV.AdvanceCollarResonanceBump

/-! Energy of the normalized smooth bump for the actual nonresonant
Friedrichs collar potential 2/r²+j²/r⁸. -/

noncomputable section

open MeasureTheory Set Real
open UV.AdvanceCollarResonanceBump

namespace UV.CollarEigenmode

def dirichletEnergy (j : ℝ) (u : ℝ → ℝ) :=
  ∫ r in Ioc 0 1,deriv u r^2+potential j r*u r^2

theorem dirichlet_bump_energy (j : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ h : ℝ,0 < h → 2*h ≤ 1 →
      IntegrableOn (fun r => deriv (resonanceBump h) r^2+potential j r*resonanceBump h r^2) (Ioc 0 1) ∧
      dirichletEnergy j (resonanceBump h) ≤ C/h^8 := by
  let ν := 1+|j|
  have hν : 1 ≤ ν := by dsimp [ν]; linarith [abs_nonneg j]
  have hj : j^2 ≤ ν^2 := by
    rw [← sq_abs j]
    exact pow_le_pow_left₀ (abs_nonneg j) (by dsimp [ν]; linarith) 2
  obtain ⟨B,hB,h⟩ := resonance_bump_energy_bound
  refine ⟨B*(1+ν^2+ν),by positivity,fun d hd h₂ => ?_⟩
  have hd1 : d ≤ 1 := by linarith
  obtain ⟨hi,hE⟩ := h ν d (by linarith) hd h₂
  have hcmp (r : ℝ) (hr : r ∈ Ioc 0 1) : potential j r ≤ resonancePotential ν r := by
    have hr5 := pow_pos hr.1 5
    have hr2 := pow_pos hr.1 2
    have h3 : r^3 ≤ 1 := pow_le_one₀ hr.1.le hr.2
    have hfirst : 2/r^2 ≤ 4*ν/r^5 := by
      rw [div_le_div_iff₀ hr2 hr5]
      calc
        2*r^5 = (2*r^3)*r^2 := by ring
        _ ≤ (4*ν)*r^2 := mul_le_mul_of_nonneg_right (by linarith) hr2.le
    unfold potential resonancePotential
    linarith [div_le_div_of_nonneg_right hj (pow_nonneg hr.1.le 8)]
  let f := fun r => deriv (resonanceBump d) r^2+potential j r*resonanceBump d r^2
  let G := fun r => deriv (resonanceBump d) r^2+resonancePotential ν r*resonanceBump d r^2
  have hle : f ≤ᵐ[volume.restrict (Ioc 0 1)] G := by
    filter_upwards [ae_restrict_mem (s := Ioc (0:ℝ) 1) measurableSet_Ioc] with r hr
    exact add_le_add_left (mul_le_mul_of_nonneg_right (hcmp r hr) (sq_nonneg _)) _
  have hn : ∀ r,0 ≤ f r := by dsimp [f,potential]; intro r; positivity
  have hs : IntegrableOn f (Ioc 0 1) := by
    apply hi.mono'
    · have hdC := (resonance_bump_smooth d).continuous_deriv (by decide)
      have hbC := (resonance_bump_smooth d).continuous
      dsimp [f,potential]; fun_prop
    · exact hle.mono fun r hr => (Real.norm_of_nonneg (hn r)).le.trans hr
  refine ⟨hs,(integral_mono_ae hs hi hle).trans (hE.trans ?_)⟩
  have h8 := pow_pos hd 8
  have h28 : d^8 ≤ d^2 := pow_le_pow_of_le_one hd.le hd1 (by decide)
  have h58 : d^8 ≤ d^5 := pow_le_pow_of_le_one hd.le hd1 (by decide)
  calc
    _ ≤ B*((1/d^8)+ν^2/d^8+ν/d^8) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact add_le_add (add_le_add_right (by simpa only [one_div] using inv_anti₀ h8 h28) _)
        (div_le_div_of_nonneg_left (by linarith) h8 h58)
    _ = _ := by ring

end UV.CollarEigenmode
