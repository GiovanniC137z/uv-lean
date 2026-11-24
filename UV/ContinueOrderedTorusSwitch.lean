import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! The smooth compact autocorrelation used to switch the finite slab:
an actual Fourier probability density supplies one unit of mass for every
independent switching frequency. The Fourier variable is in cycles, so its
angular-frequency transfer is `2πξ`. -/

noncomputable section
open MeasureTheory Real Set Filter
open scoped FourierTransform ComplexConjugate RealInnerProductSpace ContDiff
namespace UV.SectorPlane

def orderedSwitchMass (φ : ℝ → ℝ) := ∫ s, (φ s)^2

def orderedTimeSwitch (φ : ℝ → ℝ) (t : ℝ) :=
  (∫ s, φ (s+t)*φ s)/orderedSwitchMass φ

def orderedSwitchDensity (φ : ℝ → ℝ) (ξ : ℝ) :=
  ‖𝓕 (fun s : ℝ => (φ s : ℂ)) ξ‖^2/orderedSwitchMass φ

private theorem switch_inverse_real (φ : ℝ → ℝ) (ξ : ℝ) :
    𝓕⁻ (fun s => (φ s:ℂ)) ξ = conj (𝓕 (fun s => (φ s:ℂ)) ξ) := by
  rw [Real.fourierIntegralInv_eq',Real.fourierIntegral_eq',← integral_conj]
  apply integral_congr_ae; filter_upwards with x
  simp only [smul_eq_mul,map_mul,← Complex.exp_conj,Complex.conj_I,Complex.conj_ofReal]
  congr 2
  push_cast
  ring

private theorem switch_parseval (φ : ℝ → ℝ) (hs : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ) (t : ℝ) :
    ((∫ s, φ (s+t)*φ s : ℝ) : ℂ) =
      ∫ ξ, (Real.fourierChar ((innerₗ ℝ) t ξ):ℂ) * (‖𝓕 (fun s : ℝ => (φ s:ℂ)) ξ‖^2 : ℝ) := by
  let f (s : ℝ) : ℂ := φ s
  let F := 𝓕 f
  let f' := f ∘ (fun s => s+t)
  let ψ := 𝓕⁻ f
  have hsc : HasCompactSupport f := hs.comp_left (g := Complex.ofReal) rfl
  have hfc : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hφ
  let u := hsc.toSchwartzMap hfc
  have hi : Integrable f := u.integrable
  have hψ : Integrable ψ := ((SchwartzMap.fourierTransformCLE ℂ).symm u).integrable.congr
    (by rw [SchwartzMap.fourierTransformCLE_symm_apply]; rfl)
  have ht : Integrable f' := (measurePreserving_add_right (volume : Measure ℝ) t).integrable_comp_of_integrable hi
  have hback : 𝓕 ψ = f := hfc.continuous.fourier_inversion_inv hi ((SchwartzMap.fourierTransformCLM ℂ u).integrable)
  have hpair := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner ht hψ
  rw [flip_innerₗ] at hpair
  change (∫ ξ, 𝓕 f' ξ * ψ ξ) = ∫ s, f' s * 𝓕 ψ s at hpair
  rw [hback] at hpair
  have hshift := VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume (innerₗ ℝ) f t
  change 𝓕 f' = fun ξ => Real.fourierChar ((innerₗ ℝ) t ξ) • F ξ at hshift
  calc
    _ = ∫ s, f' s * f s := by simpa only [f',f,Function.comp_apply,Complex.ofReal_mul] using (integral_complex_ofReal (f := fun s => φ (s+t)*φ s)).symm
    _ = ∫ ξ, 𝓕 f' ξ * ψ ξ := hpair.symm
    _ = _ := by
      rw [hshift]
      apply integral_congr_ae; filter_upwards with ξ
      change ((Real.fourierChar ((innerₗ ℝ) t ξ):ℂ) * F ξ) * 𝓕⁻ f ξ = _
      rw [switch_inverse_real φ ξ,mul_assoc,Complex.mul_conj,Complex.normSq_eq_norm_sq]

/-- The autocorrelation is even, between zero and one, and is represented
at every time by the Fourier transform of a bounded, nonnegative unit-mass
density. This uses mathlib's cycles-per-time normalization explicitly. -/
theorem ordered_torus_switch_probability (φ : ℝ → ℝ) (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hn : ∀ s, 0 ≤ φ s) (hne : ∃ s, φ s ≠ 0) :
    Integrable (orderedSwitchDensity φ) ∧ (∫ ξ, orderedSwitchDensity φ ξ) = 1 ∧
    (∃ B : ℝ, ∀ ξ, 0 ≤ orderedSwitchDensity φ ξ ∧ orderedSwitchDensity φ ξ ≤ B) ∧
    ∀ t, 0 ≤ orderedTimeSwitch φ t ∧ orderedTimeSwitch φ t ≤ 1 ∧ orderedTimeSwitch φ (-t) = orderedTimeSwitch φ t ∧
      (orderedTimeSwitch φ t:ℂ) = ∫ ξ,
        (Real.fourierChar ((innerₗ ℝ) t ξ):ℂ) * (orderedSwitchDensity φ ξ:ℂ) := by
  obtain ⟨s,hs₀⟩ := hne
  have hD : 0 < orderedSwitchMass φ := (hφ.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hs.comp_left (g := fun x : ℝ => x^2) (by norm_num)) (fun x => sq_nonneg _) (pow_ne_zero _ hs₀)
  have hInv (t : ℝ) : (orderedTimeSwitch φ t:ℂ) = ∫ ξ,
      (Real.fourierChar ((innerₗ ℝ) t ξ):ℂ) * (orderedSwitchDensity φ ξ:ℂ) := by
    simp only [orderedTimeSwitch,orderedSwitchDensity,Complex.ofReal_div,←mul_div_assoc,integral_div]
    rw [switch_parseval φ hs hφ t]
  have h0 : orderedTimeSwitch φ 0 = 1 := by
    simp [orderedTimeSwitch,orderedSwitchMass,←pow_two,show (∫ s, φ s^2) ≠ 0 from hD.ne']
  have hone : (∫ ξ, orderedSwitchDensity φ ξ) = 1 := by
    have hh := hInv 0
    simp only [h0,Complex.ofReal_one,LinearMap.map_zero,LinearMap.zero_apply,AddChar.map_zero_eq_one,
      OneMemClass.coe_one,one_mul,integral_complex_ofReal] at hh
    exact_mod_cast hh.symm
  have hi : Integrable (orderedSwitchDensity φ) := Integrable.of_integral_ne_zero (hone.trans_ne one_ne_zero)
  have hnρ (ξ) : 0 ≤ orderedSwitchDensity φ ξ := div_nonneg (sq_nonneg _) hD.le
  let M := ∫ s : ℝ, ‖(φ s:ℂ)‖
  refine ⟨hi,hone,⟨M^2/orderedSwitchMass φ,fun ξ => ⟨hnρ ξ,?_⟩⟩,?_⟩
  · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (fun s => (φ s:ℂ)) ξ) _) hD.le
  intro t
  have hpos : 0 ≤ orderedTimeSwitch φ t := div_nonneg (integral_nonneg fun s => mul_nonneg (hn _) (hn _)) hD.le
  refine ⟨hpos,?_,?_,hInv t⟩
  · calc
      _ = ‖(orderedTimeSwitch φ t : ℂ)‖ := by simp [Real.norm_of_nonneg hpos]
      _ ≤ ∫ ξ, ‖(Real.fourierChar ((innerₗ ℝ) t ξ):ℂ)*(orderedSwitchDensity φ ξ:ℂ)‖ := by
        rw [hInv]; exact norm_integral_le_integral_norm _
      _ = 1 := by simpa [norm_mul, Real.norm_of_nonneg (hnρ _)] using hone
  · have h := integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun s => φ (s+-t)*φ s) t
    simp only [add_neg_cancel_right,mul_comm (φ _) (φ _)] at h
    apply congrArg (·/orderedSwitchMass φ)
    simpa only [mul_comm] using h.symm

/-- Frequency density with respect to angular frequency (the carrier
variable in the propagators), including the inverse Fourier normalization. -/
def orderedAngularSwitchDensity (φ : ℝ → ℝ) (ν : ℝ) :=
  orderedSwitchDensity φ (ν/(2*π))/(2*π)

theorem ordered_torus_angular_switch (φ : ℝ → ℝ) (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hn : ∀ s, 0 ≤ φ s) (hne : ∃ s, φ s ≠ 0) :
    Continuous (orderedAngularSwitchDensity φ) ∧ Integrable (orderedAngularSwitchDensity φ) ∧
    (∫ ν, orderedAngularSwitchDensity φ ν) = 1 ∧
    (∃ B : ℝ, ∀ ν, 0 ≤ orderedAngularSwitchDensity φ ν ∧ orderedAngularSwitchDensity φ ν ≤ B) ∧
    ∀ t, (orderedTimeSwitch φ t:ℂ) = ∫ ν : ℝ,
      Complex.exp ((t:ℂ)*(ν:ℂ)*Complex.I)*(orderedAngularSwitchDensity φ ν:ℂ) := by
  obtain ⟨_,hρ,⟨M,hM⟩,ht⟩ := ordered_torus_switch_probability φ hs hφ hn hne
  let D := 2*π
  have hD : 0 < D := by dsimp [D]; positivity
  have hi : Integrable (fun s => (φ s:ℂ)) :=
    (Complex.continuous_ofReal.comp hφ.continuous).integrable_of_hasCompactSupport (hs.comp_left (g := Complex.ofReal) rfl)
  have hfft : Continuous (𝓕 (fun s => (φ s:ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hi
  have hco : Continuous (orderedSwitchDensity φ) := (hfft.norm.pow 2).div_const _
  have hnorm : (∫ ν, orderedAngularSwitchDensity φ ν) = 1 := by
    change (∫ ν, orderedSwitchDensity φ (ν/D)/D) = 1
    rw [integral_div,Measure.integral_comp_div,abs_of_pos hD,hρ,smul_eq_mul,mul_one,div_self hD.ne']
  refine ⟨(hco.comp (continuous_id.div_const _)).div_const _,Integrable.of_integral_ne_zero (hnorm.trans_ne one_ne_zero),
    hnorm,⟨M/D, fun ν => ⟨div_nonneg (hM _).1 hD.le, div_le_div_of_nonneg_right (hM _).2 hD.le⟩⟩,?_⟩
  intro t
  let F (ξ : ℝ) := (Real.fourierChar ((innerₗ ℝ) t ξ):ℂ)*(orderedSwitchDensity φ ξ:ℂ)
  have he (ν : ℝ) : Complex.exp ((t:ℂ)*(ν:ℂ)*Complex.I)*(orderedAngularSwitchDensity φ ν:ℂ) = F (ν/D)/(D:ℂ) := by
    dsimp only [F,orderedAngularSwitchDensity]
    rw [Complex.ofReal_div,mul_div_assoc,Real.fourierChar_apply,innerₗ_apply]
    change _ = Complex.exp ((↑(D * (ν/D*t)) : ℂ)*Complex.I)*_
    congr 3
    push_cast
    field_simp [hD.ne']
  simp_rw [he]
  rw [integral_div,Measure.integral_comp_div,abs_of_pos hD,Complex.real_smul,← (ht t).2.2.2]
  field_simp [hD.ne']

/-- Solving time conservation for one switch costs at most the uniform
Fourier density bound. All independent switches integrate with mass one,
including a family of length zero. The solved frequency may depend on
arbitrarily shifted external, tree and chord frequencies. -/
theorem ordered_torus_eliminated_switch (φ : ℝ → ℝ) (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hn : ∀ s, 0 ≤ φ s) (hne : ∃ s, φ s ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (ν₀ : (Fin n → ℝ) → ℝ), Measurable ν₀ →
      let f := orderedAngularSwitchDensity φ
      let G (ν : Fin n → ℝ) := f (ν₀ ν)*∏ j, f (ν j)
      Integrable G ∧ (∫ ν, G ν) ≤ B ∧ (∫ ν : Fin n → ℝ, ∏ j, f (ν j)) = 1 := by
  obtain ⟨hf,hi,h1,⟨B,hB⟩,_⟩ := ordered_torus_angular_switch φ hs hφ hn hne
  refine ⟨B,(hB 0).1.trans (hB 0).2,?_⟩
  intro n ν₀ hν f G
  let P (ν : Fin n → ℝ) := ∏ j, f (ν j)
  have hP : Integrable P := Integrable.fintype_prod fun _ => hi
  have hmass : (∫ ν, P ν) = 1 := by simp [P,integral_fintype_prod_volume_eq_prod,f,h1]
  have hPpos (ν) : 0 ≤ P ν := Finset.prod_nonneg fun j _ => (hB (ν j)).1
  have hG (ν) : G ν ≤ B*P ν := mul_le_mul_of_nonneg_right (hB _).2 (hPpos ν)
  have hGI : Integrable G := by
    apply (hP.const_mul B).mono' ((hf.measurable.comp hν).mul (Finset.measurable_prod _ (fun j _ =>
      hf.measurable.comp (measurable_pi_apply j)))).aestronglyMeasurable
    filter_upwards with ν
    change ‖orderedAngularSwitchDensity φ (ν₀ ν)*P ν‖ ≤ B*P ν
    rw [Real.norm_of_nonneg (mul_nonneg (hB _).1 (hPpos ν))]
    exact hG ν
  refine ⟨hGI,(integral_mono hGI (hP.const_mul B) hG).trans_eq ?_,hmass⟩
  rw [integral_const_mul,hmass,mul_one]

end UV.SectorPlane
