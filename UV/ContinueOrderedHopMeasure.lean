import UV.ContinueTwoBandFourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Pi

/-! The return-density majorant for one ordered two-band path, on the
locked plane's Euclidean carrier coordinate and three spatial coordinates.
The symmetric duration exponential dominates either one-sided onsite
propagator. Its mass and the heat normalization retain the small-hopping
threshold of the manuscript. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace UV.SectorPlane

abbrev OrderedHopStep := ℝ × Spatial

def orderedHopLength (x : OrderedHopStep) : ℝ := |x.1| + ‖x.2‖

def orderedHopPrecision (σ : ℝ) : ℝ := (4*σ^2)⁻¹

def orderedHopGaussianMass (a : ℝ) : ℝ := (Real.pi/a)^((3:ℝ)/2)

private theorem orderedHop_heat_precision (σ : ℝ) (z : Spatial) :
    twoBandDisplacementDensity σ z =
      (orderedHopGaussianMass (orderedHopPrecision σ))⁻¹ * Real.exp (-orderedHopPrecision σ * ‖z‖^2) := by
  unfold orderedHopGaussianMass orderedHopPrecision twoBandDisplacementDensity
  rw [div_inv_eq_mul, show Real.pi*(4*σ^2) = 4*Real.pi*σ^2 by ring, neg_mul]

def orderedHopDensity (m σ : ℝ) (x : OrderedHopStep) : ℝ :=
  Real.exp (-m*|x.1|) * twoBandDisplacementDensity σ x.2

theorem orderedHop_precision_pos {σ : ℝ} (hσ : 0 < σ) : 0 < orderedHopPrecision σ := by
  unfold orderedHopPrecision; positivity

theorem orderedHop_gaussian_mass_pos {a : ℝ} (ha : 0 < a) : 0 < orderedHopGaussianMass a :=
  Real.rpow_pos_of_pos (div_pos Real.pi_pos ha) _

theorem orderedHop_length_nonneg (x : OrderedHopStep) : 0 ≤ orderedHopLength x :=
  add_nonneg (abs_nonneg _) (norm_nonneg _)

theorem orderedHop_density_nonneg {σ : ℝ} (hσ : 0 < σ) (m : ℝ) (x : OrderedHopStep) :
    0 ≤ orderedHopDensity m σ x := by
  rw [orderedHopDensity, orderedHop_heat_precision]
  exact mul_nonneg (Real.exp_pos _).le (mul_nonneg
    (inv_pos.mpr (orderedHop_gaussian_mass_pos (orderedHop_precision_pos hσ))).le (Real.exp_pos _).le)

@[fun_prop] theorem continuous_orderedHopLength : Continuous orderedHopLength := by
  unfold orderedHopLength; fun_prop

@[fun_prop] theorem continuous_orderedHopDensity (m σ : ℝ) : Continuous (orderedHopDensity m σ) := by
  unfold orderedHopDensity twoBandDisplacementDensity; fun_prop

theorem orderedHop_time_mass {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ, Real.exp (-b*|t|)) = 2/b := by
  rw [integral_comp_abs (f := fun x => Real.exp (-b*x)), integral_exp_mul_Ioi (neg_lt_zero.mpr hb)]
  simp
  ring

theorem orderedHop_gaussian_mass {a : ℝ} (ha : 0 < a) :
    (∫ z : Spatial, Real.exp (-a*‖z‖^2)) = orderedHopGaussianMass a := by
  simpa only [orderedHopGaussianMass,finrank_euclideanSpace,Fintype.card_fin,Nat.cast_ofNat] using
    (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Spatial) ha)

/-- A tilt of the spatial length is bounded by exp(η) times a Gaussian
of precision a-η, since r ≤ 1+r². The bound is sharp at zero tilt. -/
def orderedHopTiltPeak (σ η : ℝ) : ℝ :=
  (orderedHopGaussianMass (orderedHopPrecision σ))⁻¹ * Real.exp η

def orderedHopTiltMajorant (m σ η : ℝ) (x : OrderedHopStep) : ℝ :=
  Real.exp (-(m-η)*|x.1|) *
    (orderedHopTiltPeak σ η * Real.exp (-(orderedHopPrecision σ-η)*‖x.2‖^2))

def orderedHopTiltMass (m σ η : ℝ) : ℝ :=
  2/(m-η) * (orderedHopTiltPeak σ η * orderedHopGaussianMass (orderedHopPrecision σ-η))

theorem orderedHop_tilt_peak_nonneg {σ : ℝ} (hσ : 0 < σ) (η : ℝ) :
    0 ≤ orderedHopTiltPeak σ η :=
  mul_nonneg (inv_pos.mpr (orderedHop_gaussian_mass_pos (orderedHop_precision_pos hσ))).le (Real.exp_pos _).le

theorem orderedHop_tilt_majorant_nonneg {σ : ℝ} (hσ : 0 < σ) (m η : ℝ) (x : OrderedHopStep) :
    0 ≤ orderedHopTiltMajorant m σ η x :=
  mul_nonneg (Real.exp_pos _).le (mul_nonneg (orderedHop_tilt_peak_nonneg hσ η) (Real.exp_pos _).le)

theorem orderedHop_tilt_le_majorant {σ η : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (m : ℝ) (x : OrderedHopStep) :
    orderedHopDensity m σ x * Real.exp (η*orderedHopLength x) ≤ orderedHopTiltMajorant m σ η x := by
  let A := (orderedHopGaussianMass (orderedHopPrecision σ))⁻¹
  have hA : 0 ≤ A := (inv_pos.mpr (orderedHop_gaussian_mass_pos (orderedHop_precision_pos hσ))).le
  have hr : ‖x.2‖ ≤ 1+‖x.2‖^2 := by nlinarith [sq_nonneg (‖x.2‖-1/2)]
  have hExp := mul_le_mul_of_nonneg_left hr hη
  rw [orderedHopDensity, orderedHop_heat_precision]
  unfold orderedHopLength orderedHopTiltMajorant orderedHopTiltPeak
  change Real.exp _ * (A * Real.exp _) * Real.exp _ ≤ Real.exp _ * (A * Real.exp _ * Real.exp _)
  calc
    _ = A * Real.exp (-m*|x.1| + -orderedHopPrecision σ*‖x.2‖^2 + η*(|x.1|+‖x.2‖)) := by
      rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ A * Real.exp (-(m-η)*|x.1| + η + -(orderedHopPrecision σ-η)*‖x.2‖^2) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hA
      linarith
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

theorem orderedHop_tilt_majorant_le_peak {m σ η : ℝ} (hσ : 0 < σ)
    (hm : η ≤ m) (ha : η ≤ orderedHopPrecision σ) (x : OrderedHopStep) :
    orderedHopTiltMajorant m σ η x ≤ orderedHopTiltPeak σ η := by
  have ht : Real.exp (-(m-η)*|x.1|) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hm)) (abs_nonneg _))
  have hz : Real.exp (-(orderedHopPrecision σ-η)*‖x.2‖^2) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr ha)) (sq_nonneg _))
  unfold orderedHopTiltMajorant
  calc
    _ ≤ 1*(orderedHopTiltPeak σ η * 1) := mul_le_mul ht
      (mul_le_mul_of_nonneg_left hz (orderedHop_tilt_peak_nonneg hσ η))
      (mul_nonneg (orderedHop_tilt_peak_nonneg hσ η) (Real.exp_pos _).le) zero_le_one
    _ = _ := by ring

theorem orderedHop_tilt_majorant_integral {m σ η : ℝ} (hm : η < m) (ha : η < orderedHopPrecision σ) :
    (∫ x, orderedHopTiltMajorant m σ η x) = orderedHopTiltMass m σ η := by
  unfold orderedHopTiltMajorant orderedHopTiltMass
  rw [Measure.volume_eq_prod, integral_prod_mul (fun t : ℝ => Real.exp (-(m-η)*|t|))
    (fun z : Spatial => orderedHopTiltPeak σ η * Real.exp (-(orderedHopPrecision σ-η)*‖z‖^2)),
    integral_const_mul,
    orderedHop_time_mass (sub_pos.mpr hm), orderedHop_gaussian_mass (sub_pos.mpr ha)]

theorem orderedHop_tilt_majorant_integrable {m σ η : ℝ} (hσ : 0 < σ) (hm : η < m)
    (ha : η < orderedHopPrecision σ) : Integrable (orderedHopTiltMajorant m σ η) := by
  by_contra h
  have hn := orderedHop_tilt_majorant_integral hm ha
  rw [integral_undef h] at hn
  have hU := orderedHop_gaussian_mass_pos (sub_pos.mpr ha)
  have hB := orderedHop_gaussian_mass_pos (orderedHop_precision_pos hσ)
  unfold orderedHopTiltMass orderedHopTiltPeak at hn
  have hD := sub_pos.mpr hm
  exact (show 0 < 2/(m-η) * ((orderedHopGaussianMass (orderedHopPrecision σ))⁻¹ * Real.exp η *
    orderedHopGaussianMass (orderedHopPrecision σ-η)) by positivity).ne hn

theorem orderedHop_tilt_mass_zero {σ : ℝ} (hσ : 0 < σ) (m : ℝ) :
    orderedHopTiltMass m σ 0 = 2/m := by
  unfold orderedHopTiltMass orderedHopTiltPeak
  simp [inv_mul_cancel₀ (orderedHop_gaussian_mass_pos (orderedHop_precision_pos hσ)).ne']

theorem orderedHop_has_summable_tilt {m g σ : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m) :
    ∃ η : ℝ, 0 < η ∧ η < m ∧ η < orderedHopPrecision σ ∧ |g| * orderedHopTiltMass m σ η < 1 := by
  have hm : 0 < m := lt_of_le_of_lt (by positivity) hg
  have ha := orderedHop_precision_pos hσ
  have hMass : ContinuousAt (orderedHopTiltMass m σ) 0 := by
    unfold orderedHopTiltMass orderedHopTiltPeak orderedHopGaussianMass
    fun_prop (disch := first | positivity | simp [ne_of_gt hm,ne_of_gt ha])
  have hzero : |g| * orderedHopTiltMass m σ 0 < 1 := by
    rw [orderedHop_tilt_mass_zero hσ, ← mul_div_assoc, div_lt_one hm, mul_comm]
    exact hg
  have hnear := (hMass.const_mul |g|).eventually_lt continuousAt_const hzero
  have hevent : ∀ᶠ η in 𝓝 (0:ℝ), η < m ∧ η < orderedHopPrecision σ ∧ |g| * orderedHopTiltMass m σ η < 1 :=
    (eventually_lt_nhds hm).and ((eventually_lt_nhds ha).and hnear)
  have hpos : ∀ᶠ x in 𝓝[>] (0:ℝ), 0 < x := self_mem_nhdsWithin
  obtain ⟨η, hη, hb⟩ := (hpos.and
    (hevent.filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨η,hη,hb⟩

end UV.SectorPlane
