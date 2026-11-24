import UV.ContinueOrderedHopMeasure
import UV.ContinueWilsonPolygonCurrent

/-! Closed alternating temporal/spatial paths for the ordered two-band
source. The final duration and displacement are determined by the two
closure constraints. The polynomially marked return density is integrable,
and its absolute cost is summable over all positive hop counts. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace UV.SectorPlane

variable {n : ℕ}

def orderedHopClosingStep (d : Fin n → OrderedHopStep) : OrderedHopStep := -(∑ j, d j)

theorem orderedHop_path_closes (d : Fin n → OrderedHopStep) :
    ∑ j, (Fin.cons (orderedHopClosingStep d) d : Fin (n+1) → OrderedHopStep) j = 0 := by
  rw [Fin.sum_univ_succ]
  simp [orderedHopClosingStep]

def orderedHopPathLength (d : Fin n → OrderedHopStep) : ℝ :=
  orderedHopLength (orderedHopClosingStep d) + ∑ j, orderedHopLength (d j)

def orderedHopReturnDensity (m σ : ℝ) (d : Fin n → OrderedHopStep) : ℝ :=
  orderedHopDensity m σ (orderedHopClosingStep d) * ∏ j, orderedHopDensity m σ (d j)

def orderedHopPathEnvelope (m σ g : ℝ) (a b : ℕ) (d : Fin n → OrderedHopStep) : ℝ :=
  |g|^(n+1) * (1+(n:ℝ))^a * ((1+orderedHopPathLength d)^b * orderedHopReturnDensity m σ d)

theorem orderedHop_path_length_nonneg (d : Fin n → OrderedHopStep) : 0 ≤ orderedHopPathLength d :=
  add_nonneg (orderedHop_length_nonneg _) (Finset.sum_nonneg fun _ _ => orderedHop_length_nonneg _)

theorem orderedHop_return_density_nonneg {σ : ℝ} (hσ : 0 < σ) (m : ℝ) (d : Fin n → OrderedHopStep) :
    0 ≤ orderedHopReturnDensity m σ d :=
  mul_nonneg (orderedHop_density_nonneg hσ m _) (Finset.prod_nonneg fun _ _ => orderedHop_density_nonneg hσ m _)

theorem orderedHop_path_envelope_nonneg {m g σ : ℝ} (hσ : 0 < σ) (a b : ℕ) (d : Fin n → OrderedHopStep) :
    0 ≤ orderedHopPathEnvelope m σ g a b d := by
  have hl := orderedHop_path_length_nonneg d
  have hd := orderedHop_return_density_nonneg hσ m d
  unfold orderedHopPathEnvelope; positivity

@[fun_prop] theorem continuous_orderedHopClosingStep : Continuous (orderedHopClosingStep (n := n)) := by
  unfold orderedHopClosingStep; fun_prop

@[fun_prop] theorem continuous_orderedHopPathLength : Continuous (orderedHopPathLength (n := n)) := by
  unfold orderedHopPathLength; fun_prop

@[fun_prop] theorem continuous_orderedHopReturnDensity (m σ : ℝ) :
    Continuous (orderedHopReturnDensity (n := n) m σ) := by
  unfold orderedHopReturnDensity; fun_prop

@[fun_prop] theorem continuous_orderedHopPathEnvelope (m σ g : ℝ) (a b : ℕ) :
    Continuous (orderedHopPathEnvelope (n := n) m σ g a b) := by
  unfold orderedHopPathEnvelope; fun_prop

theorem orderedHop_tilt_closed_path {m σ η : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η)
    (hm : η ≤ m) (ha : η ≤ orderedHopPrecision σ) (d : Fin n → OrderedHopStep) :
    orderedHopReturnDensity m σ d * Real.exp (η*orderedHopPathLength d) ≤
      orderedHopTiltPeak σ η * ∏ j, orderedHopTiltMajorant m σ η (d j) := by
  unfold orderedHopReturnDensity orderedHopPathLength
  rw [mul_add,Real.exp_add, Finset.mul_sum, Real.exp_sum]
  calc
    _ = (orderedHopDensity m σ (orderedHopClosingStep d) *
          Real.exp (η*orderedHopLength (orderedHopClosingStep d))) *
        ∏ j, (orderedHopDensity m σ (d j) * Real.exp (η*orderedHopLength (d j))) := by
      rw [Finset.prod_mul_distrib]; ring
    _ ≤ _ := mul_le_mul ((orderedHop_tilt_le_majorant hσ hη m _).trans
      (orderedHop_tilt_majorant_le_peak hσ hm ha _))
      (Finset.prod_le_prod (fun j _ => mul_nonneg (orderedHop_density_nonneg hσ m _) (Real.exp_pos _).le)
        (fun j _ => orderedHop_tilt_le_majorant hσ hη m _))
      (Finset.prod_nonneg fun _ _ => mul_nonneg (orderedHop_density_nonneg hσ m _) (Real.exp_pos _).le)
      (orderedHop_tilt_peak_nonneg hσ η)

def orderedHopMomentConstant (η : ℝ) (b : ℕ) : ℝ := η⁻¹^b * (b.factorial : ℝ) * Real.exp η

theorem orderedHop_nonneg_power_bound {η L : ℝ} (hη : 0 < η) (hL : 0 ≤ L) (b : ℕ) :
    (1+L)^b ≤ orderedHopMomentConstant η b * Real.exp (η*L) := by
  have hf : (0:ℝ) < b.factorial := by exact_mod_cast b.factorial_pos
  have he := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (η*(1+L)) (by positivity) b)
  change (1+L)^b ≤ orderedHopMomentConstant η b * Real.exp (η*L)
  calc
    _ = η⁻¹^b * (η*(1+L))^b := by rw [←mul_pow, ←mul_assoc, inv_mul_cancel₀ hη.ne', one_mul]
    _ ≤ η⁻¹^b * (Real.exp (η*(1+L)) * b.factorial) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by unfold orderedHopMomentConstant; rw [mul_add,mul_one,Real.exp_add]; ring

theorem orderedHop_length_power_bound {η : ℝ} (hη : 0 < η) (b : ℕ) (d : Fin n → OrderedHopStep) :
    (1+orderedHopPathLength d)^b ≤ orderedHopMomentConstant η b * Real.exp (η*orderedHopPathLength d) :=
  orderedHop_nonneg_power_bound hη (orderedHop_path_length_nonneg d) b

theorem orderedHop_path_moment_bound {m σ g η : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hm : η < m)
    (ha : η < orderedHopPrecision σ) (a b : ℕ) (d : Fin n → OrderedHopStep) :
    orderedHopPathEnvelope m σ g a b d ≤
      (|g|^(n+1)*(1+(n:ℝ))^a * (orderedHopMomentConstant η b * orderedHopTiltPeak σ η)) *
        ∏ j, orderedHopTiltMajorant m σ η (d j) := by
  have hC : 0 ≤ orderedHopMomentConstant η b := by unfold orderedHopMomentConstant; positivity
  unfold orderedHopPathEnvelope
  rw [mul_assoc (|g|^(n+1)*(1+(n:ℝ))^a), mul_assoc (orderedHopMomentConstant η b)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ (orderedHopMomentConstant η b * Real.exp (η*orderedHopPathLength d)) * orderedHopReturnDensity m σ d :=
      mul_le_mul_of_nonneg_right (orderedHop_length_power_bound hη b d) (orderedHop_return_density_nonneg hσ m d)
    _ = orderedHopMomentConstant η b * (orderedHopReturnDensity m σ d * Real.exp (η*orderedHopPathLength d)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (orderedHop_tilt_closed_path hσ hη.le hm.le ha.le d) hC

theorem orderedHop_path_moment_integral {m σ g η : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hm : η < m)
    (ha : η < orderedHopPrecision σ) (a b n : ℕ) :
    Integrable (orderedHopPathEnvelope (n := n) m σ g a b) ∧
    (∫ d, orderedHopPathEnvelope (n := n) m σ g a b d) ≤
      (|g| * (orderedHopMomentConstant η b * orderedHopTiltPeak σ η)) *
        ((|g| * orderedHopTiltMass m σ η)^n * (1+(n:ℝ))^a) := by
  let C := |g|^(n+1)*(1+(n:ℝ))^a*(orderedHopMomentConstant η b * orderedHopTiltPeak σ η)
  let H := fun d : Fin n → OrderedHopStep => C * ∏ j, orderedHopTiltMajorant m σ η (d j)
  have hInt : Integrable H := by
    rw [show (volume : Measure (Fin n → OrderedHopStep)) = Measure.pi (fun _ => volume) from volume_pi]
    exact (Integrable.fintype_prod (fun _ : Fin n => orderedHop_tilt_majorant_integrable hσ hm ha)).const_mul C
  have hBound := orderedHop_path_moment_bound (g := g) (n := n) hσ hη hm ha a b
  have hEnv := hInt.mono' (continuous_orderedHopPathEnvelope m σ g a b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun d => (Real.norm_of_nonneg (orderedHop_path_envelope_nonneg hσ a b d)).le.trans (hBound d))
  refine ⟨hEnv,(integral_mono hEnv hInt hBound).trans_eq ?_⟩
  unfold H
  rw [integral_const_mul,integral_fintype_prod_volume_eq_pow, Fintype.card_fin,orderedHop_tilt_majorant_integral hm ha]
  unfold C
  rw [mul_pow,pow_succ]
  ring

/-- Every fixed polynomial cost in the number of hops and total length is
admissible at the original threshold, including the two closure densities. -/
theorem orderedHop_path_moments_summable {m σ g : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m) (a b : ℕ) :
    (∀ n : ℕ, Integrable (orderedHopPathEnvelope (n := n) m σ g a b)) ∧
      Summable (fun n : ℕ => ∫ d, orderedHopPathEnvelope (n := n) m σ g a b d) := by
  obtain ⟨η,hη,hm,ha,hsmall⟩ := orderedHop_has_summable_tilt hσ hg
  have hbound := orderedHop_path_moment_integral (g := g) hσ hη hm ha a b
  refine ⟨fun n => (hbound n).1, ?_⟩
  let r := |g| * orderedHopTiltMass m σ η
  have hM : 0 ≤ orderedHopTiltMass m σ η := by
    unfold orderedHopTiltMass
    exact mul_nonneg (div_nonneg (by norm_num) (sub_pos.mpr hm).le)
      (mul_nonneg (orderedHop_tilt_peak_nonneg hσ η) (orderedHop_gaussian_mass_pos (sub_pos.mpr ha)).le)
  have hr : 0 ≤ r := mul_nonneg (abs_nonneg _) hM
  have hs := UV.wilson_marked_hop_summable a (show 0 ≤ r/2 by positivity) (show 2*(r/2)<1 by linarith)
  rw [show 2*(r/2) = r by ring] at hs
  exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun d => orderedHop_path_envelope_nonneg hσ a b d)
    (fun n => (hbound n).2) (hs.mul_left _)

end UV.SectorPlane
