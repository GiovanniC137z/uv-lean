import UV.ContinuationBoostSpectrum
import UV.CliffordWard
import UV.RealDegree

/-! The free optical spinor on the fixed sector plane. The four real
entries below are coefficients of the Hamiltonian's Clifford matrices.
They are not a momentum four-vector or a replacement for the vectorial
Lorentzian pole unit. -/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology ENNReal Matrix

namespace UV.FurtherOptical

def energy (m : ℝ) (k : ChargeSpatialMomentum) : ℝ :=
  Real.sqrt (m^2+‖k‖^2)

def attenuation (τ : ℝ) (k : ChargeSpatialMomentum) : ℝ :=
  Real.exp (-τ*‖k‖^2)

def diagonal (m τ : ℝ) (k : ChargeSpatialMomentum) : ℝ :=
  Real.sqrt (energy m k ^ 2 - ‖k‖^2 * attenuation τ k ^ 2)

noncomputable def coefficients (m τ : ℝ) (k : ChargeSpatialMomentum) : DiracMomentum :=
  WithLp.toLp 2 (Fin.cons (diagonal m τ k / energy m k)
    (fun i : Fin 3 => attenuation τ k * k i / energy m k))

def massAxis : DiracMomentum := EuclideanSpace.single 0 1

def projector (v : DiracMomentum) : DiracMatrix := (1/2:ℂ) • (1-diracSlash v)

theorem energy_sq (m : ℝ) (k : ChargeSpatialMomentum) :
    energy m k ^ 2 = m^2+‖k‖^2 := Real.sq_sqrt (by positivity)

theorem energy_pos {m : ℝ} (hm : 0 < m) (k : ChargeSpatialMomentum) :
    0 < energy m k := Real.sqrt_pos.mpr (by positivity)

private theorem attenuation_le_one {τ : ℝ} (hτ : 0 ≤ τ) (k : ChargeSpatialMomentum) :
    attenuation τ k ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ) (sq_nonneg ‖k‖)

private theorem diagonal_slack_nonneg {m τ : ℝ} (hτ : 0 ≤ τ) (k : ChargeSpatialMomentum) :
    0 ≤ energy m k ^ 2-‖k‖^2*attenuation τ k^2 := by
  rw [energy_sq]
  have hpos : 0 ≤ attenuation τ k := (Real.exp_pos _).le
  have h := (sq_le_sq₀ hpos zero_le_one).mpr (attenuation_le_one hτ k)
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg ‖k‖), sq_nonneg m]

theorem diagonal_sq {m τ : ℝ} (hτ : 0 ≤ τ) (k : ChargeSpatialMomentum) :
    diagonal m τ k ^ 2 = energy m k ^ 2 - ‖k‖^2 * attenuation τ k ^ 2 :=
  Real.sq_sqrt (diagonal_slack_nonneg hτ k)

private theorem axisCoeff (m τ : ℝ) (k : ChargeSpatialMomentum) :
    coefficients m τ k 0 = diagonal m τ k / energy m k := by
  rfl

private theorem spatialCoeff (m τ : ℝ) (k : ChargeSpatialMomentum) (i : Fin 3) :
    coefficients m τ k i.succ = attenuation τ k * k i / energy m k := by
  rfl

private theorem normSq_decompose (v : DiracMomentum) :
    ‖v‖^2 = (v 0)^2 + ∑ i : Fin 3, (v i.succ)^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp only [Real.norm_eq_abs, sq_abs]

private theorem opticalSpatial_sq (m τ : ℝ) (k : ChargeSpatialMomentum) :
    (∑ i : Fin 3, (coefficients m τ k i.succ)^2) =
      (attenuation τ k / energy m k)^2 * ‖k‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [spatialCoeff, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The coefficient vector is normalized at the exact relativistic
energy, including the Gaussian pair hopping and the compensated diagonal. -/
theorem coefficients_norm_sq {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ) (k : ChargeSpatialMomentum) :
    ‖coefficients m τ k‖^2 = 1 := by
  rw [normSq_decompose, axisCoeff, opticalSpatial_sq, div_pow, div_pow]
  have h := diagonal_sq (m := m) hτ k
  have he := (energy_pos hm k).ne'
  field_simp [he]
  nlinarith

theorem coefficients_zero {m τ : ℝ} (hm : 0 < m) :
    coefficients m τ 0 = massAxis := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [axisCoeff, show massAxis 0 = 1 by simp [massAxis]]
    simp [diagonal, energy, Real.sqrt_sq hm.le, hm.ne']
  · simp [spatialCoeff, massAxis]

private theorem slash_add (v w : DiracMomentum) :
    diracSlash (v+w) = diracSlash v + diracSlash w := by
  simp only [diracSlash, PiLp.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

private theorem slash_neg (v : DiracMomentum) :
    diracSlash (-v) = -diracSlash v := by
  simp only [diracSlash, PiLp.neg_apply, Complex.ofReal_neg, neg_smul, Finset.sum_neg_distrib]

theorem slash_sub (v w : DiracMomentum) : diracSlash (v-w) = diracSlash v-diracSlash w := by
  rw [sub_eq_add_neg, slash_add, slash_neg, sub_eq_add_neg]

theorem slash_adjoint (v : DiracMomentum) : (diracSlash v)ᴴ = diracSlash v := by
  unfold diracSlash
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.conjTranspose_smul, euclideanGamma_isHermitian i]
  simp

theorem slash_trace_zero (v : DiracMomentum) : (diracSlash v).trace = 0 := by
  have hz (i : Fin 4) : (euclideanGamma i).trace = 0 := by
    fin_cases i <;> simp [euclideanGamma, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  simp [diracSlash, Matrix.trace_sum, Matrix.trace_smul, hz]

theorem projector_adjoint (v : DiracMomentum) : (projector v)ᴴ = projector v := by
  simp [projector, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, slash_adjoint]

theorem projector_idempotent (v : DiracMomentum) (hv : ‖v‖^2 = 1) :
    projector v * projector v = projector v := by
  unfold projector
  simp only [smul_mul_smul, sub_mul, mul_sub, one_mul, mul_one, diracSlash_sq, hv,
    Complex.ofReal_one, one_smul]
  module

theorem projector_trace (v : DiracMomentum) : (projector v).trace = 2 := by
  norm_num [projector, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, slash_trace_zero]

/-- The finite four-slot Hilbert–Schmidt norm of a normalized projector
difference agrees exactly with the Euclidean norm of its coefficient
difference. -/
theorem projector_difference_sq (v w : DiracMomentum) :
    chargeInclusiveSquare (projector v-projector w) = ‖v-w‖^2 := by
  have he : projector v-projector w = (-1/2:ℂ) • diracSlash (v-w) := by
    rw [slash_sub]
    unfold projector
    module
  rw [he, chargeInclusiveSquare_eq_trace, Matrix.conjTranspose_smul, slash_adjoint,
    smul_mul_smul, diracSlash_sq, smul_smul, Matrix.trace_smul, Matrix.trace_one]
  simp [smul_eq_mul, Complex.mul_re]
  norm_cast
  norm_num
  ring

private theorem massAxis_zero : massAxis 0 = 1 := by simp [massAxis]
private theorem massAxis_succ (i : Fin 3) : massAxis i.succ = 0 := by simp [massAxis]

theorem coefficientDifference_sq (m τ : ℝ) (k : ChargeSpatialMomentum) :
    ‖coefficients m τ k-massAxis‖^2 =
      (diagonal m τ k/energy m k-1)^2 +
        (attenuation τ k/energy m k)^2 * ‖k‖^2 := by
  rw [normSq_decompose]
  simp only [PiLp.sub_apply, massAxis_zero, massAxis_succ, sub_zero, axisCoeff, opticalSpatial_sq]

/-- The squared spin projector departure is bounded by a genuine spatial
Gaussian; in particular this estimate holds near the origin too. -/
theorem projector_gaussian_bound {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ)
    (k : ChargeSpatialMomentum) :
    chargeInclusiveSquare (projector (coefficients m τ k)-projector massAxis) ≤
      2 * Real.exp (-(2*τ)*‖k‖^2) := by
  have hnormal := coefficients_norm_sq hm hτ k
  rw [normSq_decompose, axisCoeff, opticalSpatial_sq] at hnormal
  let a := diagonal m τ k / energy m k
  let b := (attenuation τ k / energy m k)^2 * ‖k‖^2
  change a^2+b=1 at hnormal
  have ha₀ : 0 ≤ a := by
    exact div_nonneg (Real.sqrt_nonneg _) (energy_pos hm k).le
  have hb₀ : 0 ≤ b := by dsimp [b]; positivity
  have ha₁ : a ≤ 1 := (sq_le_sq₀ ha₀ zero_le_one).mp (by linarith)
  have hb : b ≤ attenuation τ k ^ 2 := by
    have he : 0 < energy m k ^ 2 := sq_pos_of_pos (energy_pos hm k)
    have hscale : ‖k‖^2 / energy m k ^ 2 ≤ 1 :=
      (div_le_one he).mpr (by rw [energy_sq]; linarith [sq_nonneg m])
    dsimp [b]
    rw [div_pow, div_mul_eq_mul_div, mul_div_assoc]
    simpa using mul_le_mul_of_nonneg_left hscale (sq_nonneg (attenuation τ k))
  have hn : (a-1)^2 ≤ b := by
    nlinarith [mul_nonneg ha₀ (sub_nonneg.mpr ha₁)]
  rw [projector_difference_sq, coefficientDifference_sq]
  change (a-1)^2+b ≤ _
  have hExp : attenuation τ k ^ 2 = Real.exp (-(2*τ)*‖k‖^2) := by
    unfold attenuation
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [← hExp]
  linarith

theorem coefficients_continuous {m τ : ℝ} (hm : 0 < m) :
    Continuous (coefficients m τ) := by
  have he : Continuous (energy m) := by unfold energy; fun_prop
  have hc : Continuous (diagonal m τ) := by unfold diagonal energy attenuation; fun_prop
  have ha : Continuous (attenuation τ) := by unfold attenuation; fun_prop
  unfold coefficients
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hc.div he (fun k => (energy_pos hm k).ne')
  · exact (ha.mul (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j)).div he
      (fun k => (energy_pos hm k).ne')

theorem projector_departure_integrable {m τ : ℝ} (hm : 0 < m) (hτ : 0 < τ) :
    Integrable (fun k : ChargeSpatialMomentum =>
      chargeInclusiveSquare (projector (coefficients m τ k)-projector massAxis)) := by
  have hg : Integrable (fun k : ChargeSpatialMomentum => 2*Real.exp (-(2*τ)*‖k‖^2)) := by
    simpa [show (1:ℝ)+1=2 by norm_num, neg_mul] using
      integrable_real_degree_gaussian (E := ChargeSpatialMomentum) (μ := volume)
        (a := 2*τ) (D := 0) (by positivity) (by norm_num)
  apply hg.mono'
  · simp_rw [projector_difference_sq]
    exact ((coefficients_continuous (τ:=τ) hm).sub continuous_const).norm.pow 2 |>.aestronglyMeasurable
  · filter_upwards with k
    rw [Real.norm_of_nonneg (by rw [projector_difference_sq]; positivity)]
    exact projector_gaussian_bound hm hτ.le k

theorem projectorEntry_continuous {m τ : ℝ} (hm : 0 < m) (i j : Fin 4) :
    Continuous (fun k => projector (coefficients m τ k) i j) := by
  have hC := coefficients_continuous (τ:=τ) hm
  simp only [projector, Matrix.smul_apply, Matrix.sub_apply, diracSlash, Matrix.sum_apply]
  apply continuous_const.smul
  apply continuous_const.sub
  apply continuous_finset_sum
  intro l _
  simp only [smul_eq_mul]
  exact ((Complex.continuous_ofReal.comp
    ((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) l).comp hC))).mul continuous_const

/-- For every nonzero spatial transfer the actual identity-shift pair
overlap at zero incoming momentum is strictly positive. -/
theorem pair_overlap_at_zero_pos {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ)
    {p : ChargeSpatialMomentum} (hp : p ≠ 0) :
    0 < (((1-projector (coefficients m τ p))*projector (coefficients m τ 0)).trace).re := by
  rw [ContinuationBoostSpectrum.equal_rank_projection_overlap
    (projector_adjoint _) (projector_adjoint _)
    (projector_idempotent _ (coefficients_norm_sq hm hτ p))
    (projector_idempotent _ (coefficients_norm_sq hm hτ 0))
    (by rw [projector_trace, projector_trace]),
    coefficients_zero hm, projector_difference_sq, coefficientDifference_sq]
  have hp' : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hb : 0 < attenuation τ p / energy m p :=
    div_pos (Real.exp_pos _) (energy_pos hm p)
  positivity

/-- The exact optically transferred projector realizes all finite-slot
hypotheses of the bounded-sea obstruction on the selected plane. -/
theorem optical_boost_obstruction {Sector : Type*} (plane : ChargePlane Sector)
    {m τ : ℝ} (hm : 0 < m) (hτ : 0 < τ)
    (ρ : Measure ℝ) (hs : ∀ᵐ s ∂ρ, 0 ≤ s) {s₁ s₂ : ℝ}
    (hs₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂) (hfin : ρ (Icc s₁ s₂) ≠ ⊤)
    (hpos : ρ (Icc s₁ s₂) ≠ 0)
    (hi : ∀ r > 0, Integrable (fun s => r^2/(2*Real.sqrt (r^2+s))) ρ) :
    ¬ ∀ p : ChargeSpatialMomentum,
      ContinuationBoostSpectrum.canonicalDensity (fun k => projector (coefficients m τ k)) p =
        ContinuationBoostSpectrum.timelikeDensity ρ ‖p‖ := by
  exact ContinuationBoostSpectrum.bounded_sea_boost_obstruction plane
    (fun _ k => projector (coefficients m τ k)) (projector massAxis)
    (fun i j => (projectorEntry_continuous hm i j).measurable)
    (fun k => projector_adjoint _)
    (fun k => projector_idempotent _ (coefficients_norm_sq hm hτ.le k))
    (fun k k' => by rw [projector_trace, projector_trace])
    (projector_departure_integrable hm hτ) ρ hs hs₁ h₁₂ hfin hpos hi

/-- Physical density weight of the unsmeared identity shift. -/
def pairWeight (m τ : ℝ) (p k : ChargeSpatialMomentum) : ℝ :=
  (((1-projector (coefficients m τ (k+p)))*projector (coefficients m τ k)).trace).re

theorem pairWeight_eq_coefficientDistance {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ)
    (p k : ChargeSpatialMomentum) :
    pairWeight m τ p k = ‖coefficients m τ (k+p)-coefficients m τ k‖^2/2 := by
  unfold pairWeight
  rw [ContinuationBoostSpectrum.equal_rank_projection_overlap
    (projector_adjoint _) (projector_adjoint _)
    (projector_idempotent _ (coefficients_norm_sq hm hτ (k+p)))
    (projector_idempotent _ (coefficients_norm_sq hm hτ k))
    (by rw [projector_trace, projector_trace]),
    projector_difference_sq]

def pairInvariantSq (m : ℝ) (p k : ChargeSpatialMomentum) : ℝ :=
  (energy m (k+p)+energy m k)^2 - ‖p‖^2

theorem pairInvariantSq_zero_pos {m : ℝ} (hm : 0 < m) (p : ChargeSpatialMomentum) :
    0 < pairInvariantSq m p 0 := by
  have he₀ : energy m 0 = m := by simp [energy, Real.sqrt_sq hm.le]
  unfold pairInvariantSq
  rw [zero_add, he₀]
  have hh := energy_sq m p
  nlinarith [mul_pos (energy_pos hm p) hm, sq_pos_of_pos hm]

/-- The strictly positive pair weight persists on a ball of incoming
momenta whose separated intermediate invariant masses lie in a compact
strictly timelike band. -/
theorem pair_positive_timelike_ball {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ)
    {p : ChargeSpatialMomentum} (hp : p ≠ 0) :
    ∃ r s₁ s₂ c : ℝ, 0 < r ∧ 0 < s₁ ∧ s₁ ≤ s₂ ∧ 0 < c ∧
      ∀ k ∈ Metric.ball (0 : ChargeSpatialMomentum) r,
        pairInvariantSq m p k ∈ Icc s₁ s₂ ∧ c ≤ pairWeight m τ p k := by
  let M := pairInvariantSq m p 0
  let w := pairWeight m τ p 0
  have hM : 0 < M := pairInvariantSq_zero_pos hm p
  have hw : 0 < w := by
    simpa only [w, pairWeight, zero_add] using pair_overlap_at_zero_pos hm hτ hp
  have hC := coefficients_continuous (τ:=τ) hm
  have hpw : Continuous (pairWeight m τ p) := by
    have heq : pairWeight m τ p =
        fun k => ‖coefficients m τ (k+p)-coefficients m τ k‖^2/2 :=
      funext (pairWeight_eq_coefficientDistance hm hτ p)
    rw [heq]
    exact (((hC.comp (continuous_id.add continuous_const)).sub hC).norm.pow 2).div_const 2
  have hpM : Continuous (pairInvariantSq m p) := by unfold pairInvariantSq energy; fun_prop
  have hwin : ∀ᶠ k in 𝓝 (0:ChargeSpatialMomentum), w/2 < pairWeight m τ p k :=
    hpw.continuousAt (Ioi_mem_nhds (by linarith : w/2 < pairWeight m τ p 0))
  have hMin : ∀ᶠ k in 𝓝 (0:ChargeSpatialMomentum), pairInvariantSq m p k ∈ Ioo (M/2) (M+1) :=
    hpM.continuousAt (Ioo_mem_nhds (by linarith : M/2 < pairInvariantSq m p 0)
      (by linarith : pairInvariantSq m p 0 < M+1))
  obtain ⟨r, hr, h⟩ := Metric.mem_nhds_iff.mp (hwin.and hMin)
  exact ⟨r, M/2, M+1, w/2, hr, by positivity, by linarith, by positivity,
    fun k hk => ⟨Ioo_subset_Icc_self (h hk).2, (h hk).1.le⟩⟩

end UV.FurtherOptical
