import UV.ContinuationChargeResidue
import UV.MatrixAdjugate
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Exact nonvanishing of the limiting temporal coefficient on the frequency
band. The numerator after clearing the determinant denominators is entire.
The double-pole result in the fixed locked-plane orthonormal chart then
rules out vanishing on an interval of either carrier-frequency character. -/

noncomputable section
open Complex Filter Matrix MeasureTheory Set
open scoped Topology Matrix Matrix.Norms.Elementwise

namespace UV
variable {d : ℕ} {Sector : Type*}

abbrev TemporalMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Actual inverse pencil of a finite Hermitian Hamiltonian. -/
def furtherTemporalPencil (H : TemporalMatrix d) (z : ℂ) : TemporalMatrix d := z • 1 + H

def furtherTemporalResolvent (H : TemporalMatrix d) (z : ℂ) : TemporalMatrix d :=
  (furtherTemporalPencil H z)⁻¹

def furtherTemporalCoefficient (A B C Q : TemporalMatrix d) (z : ℂ) : ℂ :=
  let R := furtherTemporalResolvent A z
  let S := furtherTemporalResolvent B z
  (R * C).trace - (R * Qᴴ * S * Q).trace

theorem furtherTemporalPencil_isUnit_of_im_ne_zero {H : TemporalMatrix d}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) : IsUnit (furtherTemporalPencil H z) := by
  have hn : z ∉ spectrum ℂ (-H) := by
    rw [hH.neg.spectrum_eq_image_range]
    rintro ⟨a, _, ha⟩
    have := congrArg Complex.im ha
    exact hz (by simpa using this.symm)
  simpa only [furtherTemporalPencil, spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one,
    sub_neg_eq_add] using hn

private theorem temporalTrace_analyticAt {F : ℂ → TemporalMatrix d} {z : ℂ}
    (hF : AnalyticAt ℂ F z) : AnalyticAt ℂ (fun w => (F w).trace) z := by
  unfold Matrix.trace Matrix.diag
  exact Finset.analyticAt_fun_sum _ (fun i _ => analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hF i) i)

private theorem temporalPencil_analyticAt (H : TemporalMatrix d) (z : ℂ) :
    AnalyticAt ℂ (furtherTemporalPencil H) z := by
  exact ((analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) z).smul
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : TemporalMatrix d)) z)).add analyticAt_const

private def temporalClearedNumerator (H C Q : TemporalMatrix d) (z : ℂ) : ℂ :=
  let D := furtherTemporalPencil H z
  let J := D.adjugate
  D.det * (J * C).trace - (J * Qᴴ * J * Q).trace

private theorem temporalClearedNumerator_entire (H C Q : TemporalMatrix d) :
    AnalyticOnNhd ℂ (temporalClearedNumerator H C Q) univ := by
  intro z _
  have hD := temporalPencil_analyticAt H z
  have hJ := matrix_adjugate_analyticAt hD
  exact ((matrix_det_analyticAt hD).mul
    (temporalTrace_analyticAt (matrix_mul_analyticAt hJ analyticAt_const))).sub
    (temporalTrace_analyticAt (matrix_mul_analyticAt (matrix_mul_analyticAt
      (matrix_mul_analyticAt hJ analyticAt_const) hJ) analyticAt_const))

private theorem temporalClearedNumerator_eq (H C Q : TemporalMatrix d) (z : ℂ)
    (hz : (furtherTemporalPencil H z).det ≠ 0) :
    temporalClearedNumerator H C Q z =
      (furtherTemporalPencil H z).det ^ 2 * furtherTemporalCoefficient H H C Q z := by
  simp only [temporalClearedNumerator, furtherTemporalCoefficient, furtherTemporalResolvent,
    Matrix.inv_def, Ring.inverse_eq_inv]
  simp [smul_smul, mul_sub, pow_two]
  field_simp

private theorem furtherTemporalPencil_diagonal (ε : Fin d → ℝ) (z : ℂ) :
    furtherTemporalPencil (diagonal fun i => (ε i : ℂ)) z = diagonal fun i => z + (ε i : ℂ) := by
  unfold furtherTemporalPencil
  ext i j
  by_cases h : i = j <;> simp [h]

theorem furtherTemporalCoefficient_eq_diagonal (ε : ChargePlane Sector → Fin d → ℝ)
    (C Q : ChargePlane Sector → TemporalMatrix d) (plane : ChargePlane Sector)
    (z : ℂ) (hz : ∀ i, z + (ε plane i : ℂ) ≠ 0) :
    furtherTemporalCoefficient (diagonal fun i => (ε plane i : ℂ))
      (diagonal fun i => (ε plane i : ℂ)) (C plane) (Q plane) z = temporalContactCoefficient ε C Q plane z := by
  unfold furtherTemporalCoefficient furtherTemporalResolvent temporalContactCoefficient
  rw [furtherTemporalPencil_diagonal, ← temporalDiagonalResolvent_inverse _ _ hz]

/-- The two characters of the vectorial frequency on the fixed plane. -/
def furtherTemporalFrequency (negativeCharacter : Bool) (u : ℝ) : ℂ :=
  if negativeCharacter then (temporalCarrierFrequency u).2 else (temporalCarrierFrequency u).1

private theorem furtherTemporalFrequency_eq (b : Bool) (u : ℝ) :
    furtherTemporalFrequency b u = (if b then -I else I) * (u : ℂ) := by
  cases b <;> simp [furtherTemporalFrequency, temporalCarrierFrequency, neg_mul]

theorem furtherTemporalFrequency_im_ne_zero (b : Bool) {u : ℝ} (hu : 0 < u) :
    (furtherTemporalFrequency b u).im ≠ 0 := by
  cases b <;> simp [furtherTemporalFrequency_eq, Complex.mul_im, hu.ne']

theorem furtherTemporalFrequency_continuous (b : Bool) : Continuous (furtherTemporalFrequency b) := by
  have he : furtherTemporalFrequency b = fun u : ℝ => (if b then -I else I) * (u : ℂ) :=
    funext (furtherTemporalFrequency_eq b)
  rw [he]
  fun_prop

private theorem temporal_frequency_injective (b : Bool) : Function.Injective (furtherTemporalFrequency b) := by
  intro x y h
  simp_rw [furtherTemporalFrequency_eq] at h
  exact ofReal_injective (mul_left_cancel₀ (by cases b <;> simp) h)

private theorem temporalPencil_det_diag_ne_zero (ε : Fin d → ℝ) (z : ℂ)
    (hz : ∀ i, z + (ε i : ℂ) ≠ 0) :
    (furtherTemporalPencil (diagonal fun i => (ε i : ℂ)) z).det ≠ 0 := by
  rw [furtherTemporalPencil_diagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hz i

/-- A surviving equal-energy block prevents the complete limiting trace
from vanishing across the frequency band of the selected character. -/
theorem temporal_contact_nonzero_on_frequency_band (ε : ChargePlane Sector → Fin d → ℝ)
    (C Q : ChargePlane Sector → TemporalMatrix d) (plane : ChargePlane Sector)
    (negativeCharacter : Bool) (E : ℝ)
    (h : temporalEnergyProjection (ε plane) E * Q plane * temporalEnergyProjection (ε plane) E ≠ 0) :
    ∃ u ∈ Icc (1 : ℝ) 2, temporalContactCoefficient ε C Q plane
      (furtherTemporalFrequency negativeCharacter u) ≠ 0 := by
  by_contra! hz
  let H := diagonal fun i => (ε plane i : ℂ)
  let N := temporalClearedNumerator H (C plane) (Q plane)
  let f := furtherTemporalFrequency negativeCharacter
  have hN (u : ℝ) (hu : u ∈ Icc (1 : ℝ) 2) : N (f u) = 0 := by
    have hfn := furtherTemporalFrequency_im_ne_zero negativeCharacter (zero_lt_one.trans_le hu.1)
    have hn (i : Fin d) : f u + (ε plane i : ℂ) ≠ 0 := fun hi => hfn (by
      have := congrArg Complex.im hi
      simpa only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] using this)
    unfold N
    rw [temporalClearedNumerator_eq _ _ _ _ (temporalPencil_det_diag_ne_zero _ _ hn),
      furtherTemporalCoefficient_eq_diagonal ε C Q _ _ hn, hz u hu, mul_zero]
  have hcl : f 1 ∈ closure ({z | N z = 0} \ {f 1}) := by
    let v := fun n : ℕ => (1 : ℝ) + ((n : ℝ) + 2)⁻¹
    have hv : Tendsto v atTop (𝓝 1) := by
      simpa [v] using (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)).const_add (1 : ℝ)
    apply mem_closure_of_tendsto ((furtherTemporalFrequency_continuous negativeCharacter).continuousAt.tendsto.comp hv)
    apply Eventually.of_forall
    intro n
    have hpos : 0 < ((n : ℝ) + 2)⁻¹ := by positivity
    have hle : ((n : ℝ) + 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hv' : v n ∈ Icc (1 : ℝ) 2 := ⟨by dsimp [v]; linarith, by dsimp [v]; linarith⟩
    exact ⟨hN _ hv', fun he => (by dsimp [v]; linarith : v n ≠ 1)
      (temporal_frequency_injective negativeCharacter he)⟩
  have hN₀ : ∀ z, N z = 0 := fun z =>
    (temporalClearedNumerator_entire H _ _).eqOn_zero_of_preconnected_of_mem_closure
      isPreconnected_univ (mem_univ _) hcl (mem_univ z)
  apply temporal_contact_not_eventually_zero ε C Q plane E h
  have hd (i : Fin d) : ∀ᶠ t : ℂ in 𝓝[≠] 0, (t - (E : ℂ)) + (ε plane i : ℂ) ≠ 0 := by
    by_cases he : ε plane i = E
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa [he] using (show t ≠ 0 from ht)
    · have hc : ContinuousAt (fun t : ℂ => (t - (E : ℂ)) + (ε plane i : ℂ)) 0 := by fun_prop
      apply mem_nhdsWithin_of_mem_nhds (hc.eventually_ne _)
      simp only [zero_sub, neg_add_eq_sub, sub_ne_zero]
      exact fun h => he (Complex.ofReal_injective h)
  filter_upwards [eventually_all.mpr hd] with t ht
  have hn := hN₀ (t - (E : ℂ))
  unfold N at hn
  have hd0 := temporalPencil_det_diag_ne_zero (ε plane) _ ht
  rw [temporalClearedNumerator_eq _ _ _ _ hd0, furtherTemporalCoefficient_eq_diagonal ε C Q _ _ ht] at hn
  exact (mul_eq_zero.mp hn).resolve_left (pow_ne_zero _ hd0)

/-- The nonnegative absolute frequency integral of the actual limiting
coefficient is strictly positive for each admissible contact matrix. -/
theorem temporal_contact_positive_frequency_integral (ε : ChargePlane Sector → Fin d → ℝ)
    (C Q : ChargePlane Sector → TemporalMatrix d) (plane : ChargePlane Sector)
    (negativeCharacter : Bool) (E : ℝ)
    (h : temporalEnergyProjection (ε plane) E * Q plane * temporalEnergyProjection (ε plane) E ≠ 0) :
    0 < ∫ u in Icc (1 : ℝ) 2, ‖temporalContactCoefficient ε C Q plane
      (furtherTemporalFrequency negativeCharacter u)‖ := by
  let f := fun u => temporalContactCoefficient ε C Q plane (furtherTemporalFrequency negativeCharacter u)
  have hr : ContinuousOn (fun u => temporalDiagonalResolvent (ε plane)
      (furtherTemporalFrequency negativeCharacter u)) (Icc (1 : ℝ) 2) := by
    apply continuous_id.matrix_diagonal.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    apply ((furtherTemporalFrequency_continuous negativeCharacter).add continuous_const).continuousOn.inv₀
    intro u hu
    intro hz
    have hcmp := congrArg Complex.im hz
    apply furtherTemporalFrequency_im_ne_zero negativeCharacter (zero_lt_one.trans_le hu.1)
    simpa using hcmp
  have htrace : Continuous (Matrix.trace : TemporalMatrix d → ℂ) :=
    continuous_finset_sum _ fun i _ => (continuous_apply i).comp (continuous_apply i)
  have hc : ContinuousOn f (Icc (1 : ℝ) 2) :=
    (htrace.comp_continuousOn (hr.mul continuousOn_const)).sub
      (htrace.comp_continuousOn (((hr.mul continuousOn_const).mul hr).mul continuousOn_const))
  have hn : 0 ≤ᵐ[volume.restrict (Icc (1 : ℝ) 2)] fun u => ‖f u‖ :=
    Eventually.of_forall fun _ => norm_nonneg _
  have hm : IntegrableOn (fun u => ‖f u‖) (Icc (1 : ℝ) 2) := hc.norm.integrableOn_Icc
  by_contra! hle
  have hi : (∫ u in Icc (1 : ℝ) 2, ‖f u‖) = 0 :=
    le_antisymm hle (integral_nonneg_of_ae hn)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hn hm).mp hi
  have heq := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (1 : ℝ) ≠ 2) hzero hc.norm continuousOn_const
  obtain ⟨u, hu, hu'⟩ := temporal_contact_nonzero_on_frequency_band ε C Q plane negativeCharacter E h
  exact hu' (norm_eq_zero.mp (heq hu))

end UV
