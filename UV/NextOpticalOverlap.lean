import UV.ContinuationBoostSpectrum
import UV.ContinuationSectorPlane
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The normalized canonical density of a finite-slot sea on a fixed
sector plane. The overlap estimate uses square integrability on the
intrinsic spatial chart and the separation of the two translated balls. -/

noncomputable section

open Filter Set MeasureTheory Matrix
open scoped Topology ComplexConjugate Matrix

namespace UV.ContinuationBoostSpectrum

variable {d : ℕ}

/-- The real Hilbert–Schmidt inner product in the occupied-slot basis. -/
def matrixOverlap (A B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i, ∑ j, ((A i j) * conj (B i j)).re

theorem matrixOverlap_symm (A B : Matrix (Fin d) (Fin d) ℂ) :
    matrixOverlap A B = matrixOverlap B A := by
  unfold matrixOverlap
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem chargeInclusiveSquare_sub_eq (A B : Matrix (Fin d) (Fin d) ℂ) :
    chargeInclusiveSquare (A-B) = chargeInclusiveSquare A
      + chargeInclusiveSquare B - 2 * matrixOverlap A B := by
  simp only [chargeInclusiveSquare, Matrix.sub_apply, Complex.normSq_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, matrixOverlap]

private theorem overlap_entry_bound (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    |(a * conj b).re| ≤ δ * Complex.normSq a + δ⁻¹ * Complex.normSq b := by
  calc
    _ ≤ ‖a * conj b‖ := Complex.abs_re_le_norm _
    _ = ‖a‖ * ‖b‖ := by rw [norm_mul, Complex.norm_conj]
    _ ≤ _ := by
      simp only [← Complex.sq_norm]
      have hEq : δ * ‖a‖ ^ 2 + δ⁻¹ * ‖b‖ ^ 2 =
          (δ ^ 2 * ‖a‖ ^ 2 + ‖b‖ ^ 2) / δ := by
        field_simp
      rw [hEq]
      apply (le_div_iff₀ hδ).2
      nlinarith [sq_nonneg (δ * ‖a‖ - ‖b‖),
        mul_nonneg (mul_nonneg hδ.le (norm_nonneg a)) (norm_nonneg b)]

theorem matrixOverlap_abs_bound (A B : Matrix (Fin d) (Fin d) ℂ) {δ : ℝ} (hδ : 0 < δ) :
    |matrixOverlap A B| ≤ δ * chargeInclusiveSquare A + δ⁻¹ * chargeInclusiveSquare B := by
  unfold matrixOverlap chargeInclusiveSquare
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro i _
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro j _
  exact overlap_entry_bound _ _ hδ

private theorem matrixOverlap_measurable {F : ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ}
    (hF : ∀ i j, Measurable (fun k => F k i j)) (p : ChargeSpatialMomentum) :
    Measurable (fun k => matrixOverlap (F (k+p)) (F k)) := by
  unfold matrixOverlap
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    Complex.continuous_re.measurable.comp
      (((hF i j).comp (measurable_id.add measurable_const)).mul
        (Complex.continuous_conj.measurable.comp (hF i j)))

private theorem square_shift_integrable {F : ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ}
    (hF : Integrable (fun k => chargeInclusiveSquare (F k))) (p : ChargeSpatialMomentum) :
    Integrable (fun k => chargeInclusiveSquare (F (k+p))) :=
  (measurePreserving_add_right volume p).integrable_comp_of_integrable hF

private theorem shift_integral (g : ChargeSpatialMomentum → ℝ) (p : ChargeSpatialMomentum) :
    (∫ k, g (k+p)) = ∫ k, g k :=
  (measurePreserving_add_right volume p).integral_comp
    (Homeomorph.addRight p).isClosedEmbedding.measurableEmbedding g

private theorem matrixOverlap_integrable {F : ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ}
    (hm : ∀ i j, Measurable (fun k => F k i j))
    (hF : Integrable (fun k => chargeInclusiveSquare (F k))) (p : ChargeSpatialMomentum) :
    Integrable (fun k => matrixOverlap (F (k+p)) (F k)) := by
  apply ((square_shift_integrable hF p).add hF).mono'
    (matrixOverlap_measurable hm p).aestronglyMeasurable
  refine Eventually.of_forall fun k => ?_
  simpa only [Real.norm_eq_abs, inv_one, one_mul] using
    matrixOverlap_abs_bound (F (k+p)) (F k) zero_lt_one

private def outerTail (g : ChargeSpatialMomentum → ℝ) (r : ℝ) (k : ChargeSpatialMomentum) : ℝ :=
  if r < ‖k‖ then g k else 0

private theorem outerTail_integrable {g : ChargeSpatialMomentum → ℝ} (hg : Integrable g) (r : ℝ) :
    Integrable (outerTail g r) := by
  change Integrable ({k | r < ‖k‖}.indicator g)
  exact hg.indicator (measurableSet_lt measurable_const measurable_norm)

private theorem outerTail_limit {g : ChargeSpatialMomentum → ℝ}
    (hg : Integrable g) : Tendsto (fun r => ∫ k, outerTail g r k) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (l := atTop)
    (F := outerTail g) (f := fun _ => (0:ℝ)) (fun k => ‖g k‖)
    (Eventually.of_forall fun r => (outerTail_integrable hg r).aestronglyMeasurable)
    (Eventually.of_forall fun r => Eventually.of_forall fun k => by
      unfold outerTail
      split <;> simp)
    hg.norm (Eventually.of_forall fun k => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ‖k‖] with r hr
      simp [outerTail, not_lt_of_ge hr])
  simpa only [integral_zero] using h

private theorem inclusiveSquare_nonneg (A : Matrix (Fin d) (Fin d) ℂ) :
    0 ≤ chargeInclusiveSquare A :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

/-- Separate the overlap into the two spatial tails. The common (L^2)
mass is finite and the two tail integrals are equal by translation. -/
theorem matrixOverlap_integral_bound {F : ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ}
    (hF : Integrable (fun k => chargeInclusiveSquare (F k))) (p : ChargeSpatialMomentum)
    {r δ : ℝ} (hr : 2*r < ‖p‖) (hδ : 0 < δ) :
    |∫ k, matrixOverlap (F (k+p)) (F k)| ≤
      2*δ*(∫ k, chargeInclusiveSquare (F k))
      + 2*δ⁻¹*(∫ k, outerTail (fun z => chargeInclusiveSquare (F z)) r k) := by
  let g := fun k => chargeInclusiveSquare (F k)
  let G := outerTail g r
  have hi := outerTail_integrable hF r
  have his := (measurePreserving_add_right volume p).integrable_comp_of_integrable hi
  have hgs := square_shift_integrable hF p
  have hB : Integrable (fun k => δ*(g k+g (k+p)) + δ⁻¹*(G k+G (k+p))) :=
    ((hF.add hgs).const_mul δ).add ((hi.add his).const_mul δ⁻¹)
  rw [← Real.norm_eq_abs]
  refine le_trans (norm_integral_le_of_norm_le hB (Eventually.of_forall fun k => ?_)) ?_
  · rw [Real.norm_eq_abs]
    have hg (z) : 0 ≤ g z := inclusiveSquare_nonneg (F z)
    have hG (z) : 0 ≤ G z := by
      change 0 ≤ if r < ‖z‖ then g z else 0
      split <;> simp [hg]
    have hp : ‖p‖ ≤ ‖k+p‖ + ‖k‖ := by
      simpa using norm_sub_le (k+p) k
    by_cases hk : r < ‖k‖
    · have hGk : G k = g k := if_pos hk
      rw [hGk]
      apply (matrixOverlap_abs_bound _ _ hδ).trans
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hg k)) hδ.le)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hG _)) (inv_nonneg.mpr hδ.le))
    · have hks : r < ‖k+p‖ := by linarith [le_of_not_gt hk]
      have hGks : G (k+p) = g (k+p) := if_pos hks
      rw [hGks, matrixOverlap_symm]
      apply (matrixOverlap_abs_bound _ _ hδ).trans
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hg _)) hδ.le)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hG _)) (inv_nonneg.mpr hδ.le))
  · have h₁ : Integrable (fun k => δ*(g k+g (k+p))) := (hF.add hgs).const_mul δ
    have h₂ : Integrable (fun k => δ⁻¹*(G k+G (k+p))) := (hi.add his).const_mul δ⁻¹
    have h₃ : Integrable (fun k => G (k+p)) := his
    have h₄ : Integrable G := hi
    have h₅ : Integrable g := hF
    have h₆ : Integrable (fun k => g (k+p)) := hgs
    rw [integral_add h₁ h₂, integral_const_mul, integral_const_mul, integral_add h₅ h₆,
      integral_add h₄ h₃, shift_integral g p, shift_integral G p]
    change δ * ((∫ k, g k) + ∫ k, g k) + δ⁻¹ * ((∫ k, G k) + ∫ k, G k) ≤
      2*δ*(∫ k, g k) + 2*δ⁻¹*(∫ k, G k)
    ring_nf
    exact le_rfl

/-- A general square-integrable finite-slot departure has vanishing
real Hilbert–Schmidt overlap under unbounded intrinsic spatial shift. -/
theorem matrixOverlap_tendsto_zero {F : ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ}
    (hF : Integrable (fun k => chargeInclusiveSquare (F k)))
    {α : Type*} {l : Filter α} (p : α → ChargeSpatialMomentum)
    (hp : Tendsto (fun z => ‖p z‖) l atTop) :
    Tendsto (fun z => ∫ k, matrixOverlap (F (k+p z)) (F k)) l (𝓝 0) := by
  let M := ∫ k, chargeInclusiveSquare (F k)
  have hM : 0 ≤ M := integral_nonneg fun k => inclusiveSquare_nonneg (F k)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(8*(M+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbound : 2*δ*M < ε/2 := by
    dsimp [δ]
    rw [show 2 * (ε / (8 * (M + 1))) * M = ε*M/(4*(M+1)) by
      have h : M + 1 ≠ 0 := by positivity
      field_simp; ring]
    apply (div_lt_iff₀ (by positivity : 0 < 4*(M+1))).2
    nlinarith [mul_nonneg hε.le hM]
  have ht := (outerTail_limit hF).const_mul (2*δ⁻¹)
  rw [mul_zero, Metric.tendsto_nhds] at ht
  obtain ⟨r, hr⟩ := eventually_atTop.mp (ht (ε/2) (by positivity))
  have htail : 2*δ⁻¹*(∫ k, outerTail (fun z => chargeInclusiveSquare (F z)) r k) < ε/2 :=
    (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hr r le_rfl)
  filter_upwards [hp.eventually_gt_atTop (2*r)] with z hz
  rw [Real.dist_eq, sub_zero]
  exact (matrixOverlap_integral_bound hF (p z) hz hδ).trans_lt (by linarith)

theorem canonicalDensity_overlap_identity {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (occupied : SectorPlane.Plane E → ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ)
    (P₀ : Matrix (Fin d) (Fin d) ℂ)
    (hm : ∀ i j, Measurable (fun k => occupied diamond k i j))
    (hAdj : ∀ k, (occupied diamond k)ᴴ = occupied diamond k)
    (hProj : ∀ k, occupied diamond k * occupied diamond k = occupied diamond k)
    (hRank : ∀ k k', (occupied diamond k).trace = (occupied diamond k').trace)
    (hL2 : Integrable (fun k => chargeInclusiveSquare (occupied diamond k-P₀)))
    (p : ChargeSpatialMomentum) :
    canonicalDensity (occupied diamond) p = spatialMeasureFactor *
      ((∫ k, chargeInclusiveSquare (occupied diamond k-P₀)) -
        ∫ k, matrixOverlap (occupied diamond (k+p)-P₀) (occupied diamond k-P₀)) := by
  let F := fun k => occupied diamond k-P₀
  have hF : ∀ i j, Measurable (fun k => F k i j) := fun i j => (hm i j).sub measurable_const
  have hInt := matrixOverlap_integrable hF hL2 p
  have hS : Integrable (fun k => chargeInclusiveSquare (F (k+p))) :=
    square_shift_integrable hL2 p
  have hG : Integrable (fun k => chargeInclusiveSquare (F k)) := hL2
  have hIntSum : Integrable (fun k => chargeInclusiveSquare (F (k+p)) + chargeInclusiveSquare (F k)) :=
    hS.add hG
  have hpoint (k : ChargeSpatialMomentum) :
      (((1-occupied diamond (k+p))*occupied diamond k).trace).re =
        (chargeInclusiveSquare (F (k+p)) + chargeInclusiveSquare (F k) -
          2 * matrixOverlap (F (k+p)) (F k))/2 := by
    rw [equal_rank_projection_overlap (hAdj _) (hAdj _) (hProj _) (hProj _) (hRank _ _),
      show occupied diamond (k+p)-occupied diamond k = F (k+p)-F k by unfold F; abel,
      chargeInclusiveSquare_sub_eq]
  unfold canonicalDensity
  congr 1
  simp_rw [hpoint]
  rw [integral_div, integral_sub hIntSum (hInt.const_mul 2), integral_add hS hG,
    integral_const_mul, shift_integral (fun k => chargeInclusiveSquare (F k)) p]
  change ((∫ k, chargeInclusiveSquare (F k)) + (∫ k, chargeInclusiveSquare (F k)) -
    2*(∫ k, matrixOverlap (F (k+p)) (F k)))/2 =
      (∫ k, chargeInclusiveSquare (F k)) - ∫ k, matrixOverlap (F (k+p)) (F k)
  ring

/-- The canonical equal-time density tends to the normalized departure
mass on the same sector plane. -/
theorem canonicalDensity_tendsto_departure_mass {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (occupied : SectorPlane.Plane E → ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ)
    (P₀ : Matrix (Fin d) (Fin d) ℂ)
    (hm : ∀ i j, Measurable (fun k => occupied diamond k i j))
    (hAdj : ∀ k, (occupied diamond k)ᴴ = occupied diamond k)
    (hProj : ∀ k, occupied diamond k * occupied diamond k = occupied diamond k)
    (hRank : ∀ k k', (occupied diamond k).trace = (occupied diamond k').trace)
    (hL2 : Integrable (fun k => chargeInclusiveSquare (occupied diamond k-P₀)))
    {α : Type*} {l : Filter α} (p : α → ChargeSpatialMomentum)
    (hp : Tendsto (fun z => ‖p z‖) l atTop) :
    Tendsto (fun z => canonicalDensity (occupied diamond) (p z)) l
      (𝓝 (spatialMeasureFactor * ∫ k, chargeInclusiveSquare (occupied diamond k-P₀))) := by
  have h := matrixOverlap_tendsto_zero hL2 p hp
  have hc : Tendsto (fun _ : α => ∫ k, chargeInclusiveSquare (occupied diamond k-P₀)) l
      (𝓝 (∫ k, chargeInclusiveSquare (occupied diamond k-P₀))) := tendsto_const_nhds
  have he := (hc.sub h).const_mul spatialMeasureFactor
  simp only [sub_zero] at he
  exact he.congr (fun z => (canonicalDensity_overlap_identity diamond occupied P₀ hm hAdj hProj
    hRank hL2 (p z)).symm)

end UV.ContinuationBoostSpectrum
