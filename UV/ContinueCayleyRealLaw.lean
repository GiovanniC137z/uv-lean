import UV.ContinueOpeningCoordinateMoment
import Mathlib.Analysis.Complex.Basic

/-! Spectral pushforward from the unit circle to the signed energy axis for
a domain vector of a self-adjoint operator. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace UV.SectorPlane

def closingCayleyEnergy (ζ : ℂ) : ℝ := (Complex.I*(1+ζ)/(1-ζ)).re

def closingCayleyWeight (ζ : ℂ) : ℝ := ‖1-ζ‖^2/4

theorem closing_cayley_energy_real {ζ : ℂ} (hu : ‖ζ‖=1) :
    (closingCayleyEnergy ζ : ℂ) = Complex.I*(1+ζ)/(1-ζ) := by
  have hs : ζ.re*ζ.re+ζ.im*ζ.im=1 := by
    rw [←Complex.normSq_apply,Complex.normSq_eq_norm_sq,hu,one_pow]
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im,Complex.div_im,Complex.mul_im,Complex.mul_re,Complex.I_im,
      Complex.I_re,Complex.sub_re,Complex.sub_im,Complex.one_im,Complex.one_re,Complex.add_im,Complex.add_re]
    ring_nf at hs ⊢
    linear_combination (norm := ring_nf) ((Complex.normSq (1-ζ))⁻¹)*hs

theorem closing_cayley_weighted_square {ζ : ℂ} (hu : ‖ζ‖=1) (hn : ζ ≠ 1) :
    closingCayleyWeight ζ * (closingCayleyEnergy ζ)^2 = ‖1+ζ‖^2/4 := by
  have ha := congrArg norm (closing_cayley_energy_real hu)
  simp only [Complex.norm_real,Real.norm_eq_abs,norm_div,norm_mul,Complex.norm_I,one_mul] at ha
  have hd : ‖1-ζ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hn.symm)
  unfold closingCayleyWeight
  rw [←sq_abs (closingCayleyEnergy ζ),ha]
  field_simp

theorem closing_cayley_square_bound {ζ : ℂ} (hu : ‖ζ‖=1) :
    closingCayleyWeight ζ * (closingCayleyEnergy ζ)^2 ≤ 1 := by
  by_cases hn : ζ=1
  · simp [hn,closingCayleyWeight]
  rw [closing_cayley_weighted_square hu hn]
  have h : ‖1+ζ‖ ≤ 2 := by have hh := norm_add_le (1:ℂ) ζ; rw [norm_one,hu] at hh; linarith
  nlinarith [norm_nonneg (1+ζ)]

variable {X : Type*} [MeasurableSpace X]

def closingCayleyLaw (ν : Measure X) (c : X → ℂ) : Measure ℝ :=
  (ν.withDensity (fun x => ENNReal.ofReal (closingCayleyWeight (c x)))).map (fun x => closingCayleyEnergy (c x))

theorem closing_cayley_law_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ν : Measure X) (c : X → ℂ) (hc : Measurable c) (f : ℝ → F) (hf : StronglyMeasurable f) :
    (∫ t, f t ∂closingCayleyLaw ν c) = ∫ x, closingCayleyWeight (c x) • f (closingCayleyEnergy (c x)) ∂ν := by
  unfold closingCayleyLaw
  have hm : Measurable (fun x => closingCayleyEnergy (c x)) := by unfold closingCayleyEnergy; fun_prop
  have hw : Measurable (fun x => ENNReal.ofReal (closingCayleyWeight (c x))) := by unfold closingCayleyWeight; fun_prop
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable,integral_withDensity_eq_integral_toReal_smul hw
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hn (x : X) : 0≤closingCayleyWeight (c x) := by unfold closingCayleyWeight; positivity
  simp only [ENNReal.toReal_ofReal (hn _)]

theorem closing_cayley_law_second_moment (ν : Measure X) [IsFiniteMeasure ν]
    (c : X → ℂ) (hc : Measurable c) (hu : ∀ x, ‖c x‖ = 1) :
    Integrable (fun t : ℝ => t^2) (closingCayleyLaw ν c) := by
  unfold closingCayleyLaw
  have hm : Measurable (fun x => closingCayleyEnergy (c x)) := by unfold closingCayleyEnergy; fun_prop
  have hw : Measurable (fun x => ENNReal.ofReal (closingCayleyWeight (c x))) := by unfold closingCayleyWeight; fun_prop
  rw [integrable_map_measure (by fun_prop) hm.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hw (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hn (x) : 0≤closingCayleyWeight (c x) := by unfold closingCayleyWeight; positivity
  simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul,Function.comp_apply]
  have hg : Measurable (fun x => closingCayleyWeight (c x) * (closingCayleyEnergy (c x))^2) := by unfold closingCayleyWeight closingCayleyEnergy; fun_prop
  apply (integrable_const (1:ℝ)).mono' hg.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hn x) (sq_nonneg _))]
    exact closing_cayley_square_bound (hu x)

theorem closing_cayley_weight_zero_at_unit (ν : Measure X) (c : X → ℂ) (hc : Measurable c) :
    ν.withDensity (fun x => ENNReal.ofReal (closingCayleyWeight (c x))) (c ⁻¹' {1}) = 0 := by
  have hs : MeasurableSet (c ⁻¹' {1}) := hc (measurableSet_singleton 1)
  rw [MeasureTheory.withDensity_apply _ hs]
  calc _ = ∫⁻ _ in c ⁻¹' {1}, (0:ℝ≥0∞) ∂ν := by
         apply setLIntegral_congr_fun hs
         intro x hx
         change c x=1 at hx
         simp [hx,closingCayleyWeight]
       _ = 0 := by simp

theorem closing_cayley_law_mass (ν : Measure X) [IsFiniteMeasure ν] (c : X → ℂ)
    (hc : Measurable c) :
    (closingCayleyLaw ν c).real univ = ∫ x, closingCayleyWeight (c x) ∂ν := by
  have h := closing_cayley_law_integral ν c hc (fun _ => (1:ℝ)) stronglyMeasurable_const
  simpa only [integral_const,smul_eq_mul,mul_one] using h

def closingCayleyCauchySymbol (z ζ : ℂ) : ℂ :=
  (1-ζ)/(Complex.I*(1+ζ)+z*(1-ζ))

theorem closing_cayley_denominator_ne {z ζ : ℂ} (hz : z.im≠0) (hu : ‖ζ‖=1) :
    Complex.I*(1+ζ)+z*(1-ζ) ≠ 0 := by
  by_cases hn : ζ=1
  · subst ζ; norm_num
  have he := closing_cayley_energy_real hu
  have hd : (1:ℂ)-ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
  have h := (eq_div_iff hd).mp he
  rw [←h,←add_mul]
  apply mul_ne_zero _ hd
  intro h
  have hc := congrArg Complex.im h
  simp only [Complex.add_im,Complex.ofReal_im,zero_add,Complex.zero_im] at hc
  exact hz hc

theorem closing_cayley_weighted_cauchy {z ζ : ℂ} (hu : ‖ζ‖=1) :
    (closingCayleyWeight ζ : ℂ)*(z+(closingCayleyEnergy ζ:ℂ))⁻¹ =
      (closingCayleyWeight ζ : ℂ)*closingCayleyCauchySymbol z ζ := by
  by_cases hm : ζ=1
  · simp [hm,closingCayleyWeight]
  rw [closing_cayley_energy_real hu,closingCayleyCauchySymbol,add_div' _ z (1-ζ) (sub_ne_zero.mpr (Ne.symm hm)),inv_div,add_comm (z*(1-ζ))]


theorem closing_cayley_law_cauchy (ν : Measure X) (c : X → ℂ) (hc : Measurable c)
    (hu : ∀ x, ‖c x‖=1) (z : ℂ) :
    (∫ t : ℝ, (z+(t:ℂ))⁻¹ ∂closingCayleyLaw ν c) =
      ∫ x, (closingCayleyWeight (c x):ℂ)*closingCayleyCauchySymbol z (c x) ∂ν := by
  rw [closing_cayley_law_integral ν c hc _ (by exact (Measurable.inv ((measurable_const).add Complex.measurable_ofReal)).stronglyMeasurable)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => closing_cayley_weighted_cauchy (hu x)

theorem closing_cayley_law_energy_square (ν : Measure X) (c : X → ℂ) (hc : Measurable c)
    (hu : ∀ x, ‖c x‖=1) :
    (∫ t : ℝ, t^2 ∂closingCayleyLaw ν c) =
      ∫ x, (if c x=1 then 0 else ‖1+c x‖^2/4) ∂ν := by
  rw [closing_cayley_law_integral ν c hc _ (continuous_pow 2).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : c x=1
  · simp [hx,closingCayleyWeight]
  · simpa [hx,smul_eq_mul] using closing_cayley_weighted_square (hu x) hx

end UV.SectorPlane
