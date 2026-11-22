import UV.ContinuationChargeRigidity
import UV.RevisionSpectrumSewing

/-! Equal-time density of an identity-shift finite-slot sea on a fixed
sector plane. A positive timelike Lorentz spectral band has an incompatible
lower bound in the same spatial momentum variable. -/

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped ENNReal Topology Matrix

namespace UV.ContinuationBoostSpectrum

theorem equal_rank_projection_overlap {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : Aᴴ = A) (hB : Bᴴ = B) (hAA : A*A = A) (hBB : B*B = B)
    (htr : A.trace = B.trace) :
    (((1-A)*B).trace).re = chargeInclusiveSquare (A-B)/2 := by
  rw [chargeInclusiveSquare_eq_trace, conjTranspose_sub, hA, hB, sub_mul, one_mul,
    mul_sub, sub_mul, sub_mul, hAA, hBB]
  simp only [Matrix.trace_sub, Complex.sub_re]
  rw [Matrix.trace_mul_comm B A, htr]
  ring

private theorem inclusiveSquare_sub_le {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    chargeInclusiveSquare (A-B) ≤ 2 * chargeInclusiveSquare A + 2 * chargeInclusiveSquare B := by
  unfold chargeInclusiveSquare
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.sub_apply, ← Complex.sq_norm]
  have h := (sq_le_sq₀ (norm_nonneg (A i j-B i j))
    (add_nonneg (norm_nonneg (A i j)) (norm_nonneg (B i j)))).mpr
    (norm_sub_le (A i j) (B i j))
  nlinarith [sq_nonneg (‖A i j‖ - ‖B i j‖)]

def spatialMeasureFactor : ℝ := ((2*Real.pi)^3)⁻¹

theorem spatialMeasureFactor_nonneg : 0 ≤ spatialMeasureFactor := by
  unfold spatialMeasureFactor
  positivity

def canonicalDensity {d : ℕ} (occupied : ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ)
    (p : ChargeSpatialMomentum) : ℝ :=
  spatialMeasureFactor * ∫ k : ChargeSpatialMomentum, (((1-occupied (k+p))*occupied k).trace).re

/-- The actual identity-shift sea density is nonnegative and uniformly
bounded. The common constant projector cancels before the L² estimate. -/
theorem canonicalDensity_bounded {d : ℕ} (occupied : ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ)
    (P₀ : Matrix (Fin d) (Fin d) ℂ) (hm : ∀ i j, Measurable (fun k => occupied k i j))
    (hAdj : ∀ k, (occupied k)ᴴ = occupied k) (hProj : ∀ k, occupied k * occupied k = occupied k)
    (hRank : ∀ k k', (occupied k).trace = (occupied k').trace)
    (hL2 : Integrable (fun k => chargeInclusiveSquare (occupied k-P₀)))
    (p : ChargeSpatialMomentum) :
    0 ≤ canonicalDensity occupied p ∧
      canonicalDensity occupied p ≤ 2 * spatialMeasureFactor * ∫ k, chargeInclusiveSquare (occupied k-P₀) := by
  let F := fun k => occupied k-P₀
  let D := fun k => (((1-occupied (k+p))*occupied k).trace).re
  have hMeas : Measurable D := by
    apply Complex.continuous_re.measurable.comp
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.sub_apply]
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      (measurable_const.sub ((hm i j).comp (measurable_id.add measurable_const))).mul (hm j i)
  have hPres : MeasurePreserving (fun k : ChargeSpatialMomentum => k+p) volume volume :=
    measurePreserving_add_right volume p
  have hShift : Integrable (fun k => chargeInclusiveSquare (F (k+p))) :=
    hPres.integrable_comp_of_integrable hL2
  have hu : Integrable (fun k => chargeInclusiveSquare (F (k+p)) + chargeInclusiveSquare (F k)) :=
    hShift.add hL2
  have hpw (k : ChargeSpatialMomentum) : 0 ≤ D k ∧
      D k ≤ chargeInclusiveSquare (F (k+p)) + chargeInclusiveSquare (F k) := by
    have he := equal_rank_projection_overlap (hAdj (k+p)) (hAdj k)
      (hProj (k+p)) (hProj k) (hRank (k+p) k)
    change D k = _ at he
    have hd : 0 ≤ chargeInclusiveSquare (occupied (k+p)-occupied k) := by
      unfold chargeInclusiveSquare
      exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))
    have hf : occupied (k+p)-occupied k = F (k+p)-F k := by unfold F; abel
    rw [hf] at he
    refine ⟨?_, ?_⟩
    · rw [he, ← hf]
      exact div_nonneg hd (by norm_num)
    · rw [he]
      linarith [inclusiveSquare_sub_le (F (k+p)) (F k)]
  have hInt := hu.mono' hMeas.aestronglyMeasurable (Eventually.of_forall fun k => by
    simpa only [Real.norm_of_nonneg (hpw k).1] using (hpw k).2)
  refine ⟨mul_nonneg spatialMeasureFactor_nonneg (integral_nonneg (fun k => (hpw k).1)), ?_⟩
  have h := integral_mono hInt hu (fun k => (hpw k).2)
  rw [integral_add hShift hL2] at h
  have ht := hPres.integral_comp (Homeomorph.addRight p).isClosedEmbedding.measurableEmbedding
    (fun k => chargeInclusiveSquare (F k))
  change (∫ k, chargeInclusiveSquare (F (k+p))) = (∫ k, chargeInclusiveSquare (F k)) at ht
  rw [ht] at h
  change canonicalDensity occupied p ≤ _
  unfold canonicalDensity
  change spatialMeasureFactor * (∫ k, D k) ≤ _
  have h' : (∫ k, D k) ≤ 2 * ∫ k, chargeInclusiveSquare (F k) := by linarith
  convert mul_le_mul_of_nonneg_left h' spatialMeasureFactor_nonneg using 1; ring

/-- The zero-zero weight obtained after integrating the positive timelike
shell, in signature (+---), with the common positive normalization in ρ. -/
def timelikeDensity (ρ : Measure ℝ) (r : ℝ) : ℝ :=
  ∫ s, r^2 / (2 * Real.sqrt (r^2+s)) ∂ρ

theorem timelikeDensity_band_lower (ρ : Measure ℝ) {s₁ s₂ r : ℝ}
    (hr : 0 < r) (hs : ∀ᵐ s ∂ρ, 0 ≤ s) (hfin : ρ (Icc s₁ s₂) ≠ ⊤)
    (hi : Integrable (fun s => r^2/(2*Real.sqrt (r^2+s))) ρ) :
    (r^2/(2*Real.sqrt (r^2+s₂))) * ρ.real (Icc s₁ s₂) ≤ timelikeDensity ρ r := by
  let B := Icc s₁ s₂
  let c := r^2/(2*Real.sqrt (r^2+s₂))
  have hci : Integrable (B.indicator fun _ => c) ρ :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const hfin)
  have h := integral_mono_ae hci hi (by
    filter_upwards [hs] with s hsp
    by_cases hb : s ∈ B
    · rw [indicator_of_mem hb]
      apply div_le_div_of_nonneg_left (sq_nonneg _)
      · positivity
      · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (add_le_add_left hb.2 _)) (by norm_num)
    · rw [indicator_of_notMem hb]
      positivity)
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul] at h
  simpa only [mul_comm, B, c, timelikeDensity] using h

theorem timelikeDensity_linear_lower (ρ : Measure ℝ) {s₁ s₂ r : ℝ}
    (hr : 0 < r) (hs₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂) (hr₂ : s₂ ≤ r^2)
    (hs : ∀ᵐ s ∂ρ, 0 ≤ s) (hfin : ρ (Icc s₁ s₂) ≠ ⊤)
    (hi : Integrable (fun s => r^2/(2*Real.sqrt (r^2+s))) ρ) :
    r/4 * ρ.real (Icc s₁ s₂) ≤ timelikeDensity ρ r := by
  refine (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg).trans
    (timelikeDensity_band_lower ρ hr hs hfin hi)
  have hsq : 0 < r^2+s₂ := by linarith [sq_nonneg r]
  have hroot : Real.sqrt (r^2+s₂) ≤ 2*r := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hsq.le]
    nlinarith [sq_nonneg r]
  have hb : 0 < 2*Real.sqrt (r^2+s₂) := mul_pos (by norm_num) (Real.sqrt_pos.mpr hsq)
  have hratio : r^2/(4*r) ≤ r^2/(2*Real.sqrt (r^2+s₂)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hb (by linarith)
  have he : r^2/(4*r) = r/4 := by field_simp
  exact he ▸ hratio

/-- A fixed-plane identity-shift density with a square-integrable projector
departure cannot equal the time-component density of a positive Lorentz
timelike band at every spatial momentum. -/
theorem bounded_sea_boost_obstruction {Sector : Type*} {d : ℕ} (plane : ChargePlane Sector)
    (occupied : ChargePlane Sector → ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ)
    (P₀ : Matrix (Fin d) (Fin d) ℂ) (hm : ∀ i j, Measurable (fun k => occupied plane k i j))
    (hAdj : ∀ k, (occupied plane k)ᴴ = occupied plane k)
    (hProj : ∀ k, occupied plane k * occupied plane k = occupied plane k)
    (hRank : ∀ k k', (occupied plane k).trace = (occupied plane k').trace)
    (hL2 : Integrable (fun k => chargeInclusiveSquare (occupied plane k-P₀)))
    (ρ : Measure ℝ) (hs : ∀ᵐ s ∂ρ, 0 ≤ s) {s₁ s₂ : ℝ}
    (hs₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂) (hfin : ρ (Icc s₁ s₂) ≠ ⊤)
    (hpos : ρ (Icc s₁ s₂) ≠ 0)
    (hi : ∀ r > 0, Integrable (fun s => r^2/(2*Real.sqrt (r^2+s))) ρ) :
    ¬ ∀ p : ChargeSpatialMomentum, canonicalDensity (occupied plane) p = timelikeDensity ρ ‖p‖ := by
  intro he
  let m := ρ.real (Icc s₁ s₂)
  have hm0 : 0 < m := ENNReal.toReal_pos hpos hfin
  let C := 2*spatialMeasureFactor * ∫ k, chargeInclusiveSquare (occupied plane k-P₀)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) spatialMeasureFactor_nonneg)
      (integral_nonneg (fun k => Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))))
  let r := Real.sqrt s₂ + 4*C/m + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hr₂ : s₂ ≤ r^2 := by
    rw [← Real.sq_sqrt (hs₁.le.trans h₁₂)]
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hr.le).mpr
    dsimp [r]
    linarith [div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) hC) hm0.le]
  let p : ChargeSpatialMomentum := EuclideanSpace.single 0 r
  have hp : ‖p‖ = r := by simp [p, Real.norm_eq_abs, abs_of_pos hr]
  have ha := (canonicalDensity_bounded (occupied plane) P₀ hm hAdj hProj hRank hL2 p).2
  have hb := timelikeDensity_linear_lower ρ hr hs₁ h₁₂ hr₂ hs hfin (hi r hr)
  rw [he p, hp] at ha
  have h := hb.trans ha
  change r/4 * m ≤ C at h
  have ht : 4*C/m < r := by dsimp [r]; linarith [Real.sqrt_nonneg s₂]
  have ff := (div_lt_iff₀ hm0).mp ht
  nlinarith

end UV.ContinuationBoostSpectrum
