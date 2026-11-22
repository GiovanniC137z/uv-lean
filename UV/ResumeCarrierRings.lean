import UV.Convergence
import UV.ResumeCarrierPolarization
import UV.ContinuationSectorPlane
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-! Absolute full-frequency bounds for the individual Gaussian rings of the
positive two-oscillator magnetic square, `prop:spex-polarization-uv`.
All three spatial coordinates are intrinsic to the selected sector plane. -/

noncomputable section

open MeasureTheory Filter

namespace UV.ResumeCarrierPolarization

abbrev SpatialMomentum := SectorPlane.Spatial

/-- One magnetic contact, with the spatial harmonic readout at both incidences. -/
def ringInsertion (r : ℝ) (q : ℝ × SpatialMomentum) : ℝ :=
  ‖q.2‖ ^ 2 * Real.exp (-(2 * r * ‖q.2‖)) / (q.1 ^ 2 + ‖q.2‖ ^ 2)

/-- The factor accompanying a pair of oscillator mixing vertices. -/
def materialInsertion (Ω ω : ℝ) : ℝ := Ω ^ 2 / (ω ^ 2 + Ω ^ 2)

theorem ringInsertion_nonneg (r : ℝ) (q : ℝ × SpatialMomentum) :
    0 ≤ ringInsertion r q := by unfold ringInsertion; positivity

theorem ringInsertion_le_one {r : ℝ} (hr : 0 ≤ r) (q : ℝ × SpatialMomentum) :
    ringInsertion r q ≤ 1 := by
  unfold ringInsertion
  by_cases hd : q.1 ^ 2 + ‖q.2‖ ^ 2 = 0
  · rw [hd, div_zero]
    norm_num
  · apply (div_le_one (lt_of_le_of_ne (by positivity) (Ne.symm hd))).mpr
    have he : Real.exp (-(2 * r * ‖q.2‖)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg ‖q.2‖), sq_nonneg q.1]

theorem materialInsertion_bounds (Ω ω : ℝ) :
    0 ≤ materialInsertion Ω ω ∧ materialInsertion Ω ω ≤ 1 := by
  unfold materialInsertion
  constructor
  · positivity
  · by_cases hd : ω ^ 2 + Ω ^ 2 = 0
    · rw [hd, div_zero]
      norm_num
    · apply (div_le_one (lt_of_le_of_ne (by positivity) (Ne.symm hd))).mpr
      linarith [sq_nonneg ω]

/-- A separable majorant retains the full carrier frequency integration. -/
theorem ringInsertion_majorant (r : ℝ) (q : ℝ × SpatialMomentum) :
    ringInsertion r q ≤ (1 + q.1 ^ 2)⁻¹ *
      ((1 + ‖q.2‖ ^ 2) * Real.exp (-(2 * r * ‖q.2‖))) := by
  unfold ringInsertion
  by_cases hd : q.1 ^ 2 + ‖q.2‖ ^ 2 = 0
  · rw [hd, div_zero]
    positivity
  · have hdpos : 0 < q.1 ^ 2 + ‖q.2‖ ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hd)
    have hone : 0 < 1 + q.1 ^ 2 := by positivity
    apply (div_le_iff₀ hdpos).mpr
    rw [mul_assoc ((1 + q.1 ^ 2)⁻¹)
      ((1 + ‖q.2‖ ^ 2) * Real.exp (-(2 * r * ‖q.2‖)))
      (q.1 ^ 2 + ‖q.2‖ ^ 2)]
    apply (le_inv_mul_iff₀ hone).mpr
    have hbase : ‖q.2‖ ^ 2 * (1 + q.1 ^ 2) ≤
        (1 + ‖q.2‖ ^ 2) * (q.1 ^ 2 + ‖q.2‖ ^ 2) := by
      nlinarith [sq_nonneg q.1, sq_nonneg (‖q.2‖ ^ 2)]
    nlinarith [mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg (-(2 * r * ‖q.2‖)))]

/-- The dominating product is integrable in dω d³k, with no frequency cutoff. -/
theorem ringMajorant_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (fun q : ℝ × SpatialMomentum => (1 + q.1 ^ 2)⁻¹ *
      ((1 + ‖q.2‖ ^ 2) * Real.exp (-(2 * r * ‖q.2‖)))) := by
  exact integrable_inv_one_add_sq.mul_prod
    (UV.integrable_polynomial_exp (μ := (volume : Measure SpatialMomentum)) (by linarith) 2)

theorem ringInsertion_integrable {r : ℝ} (hr : 0 < r) : Integrable (ringInsertion r) := by
  apply (ringMajorant_integrable hr).mono'
  · have hm : Measurable (ringInsertion r) := by
      unfold ringInsertion
      fun_prop
    exact hm.aestronglyMeasurable
  · exact Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (ringInsertion_nonneg r q)]
      exact ringInsertion_majorant r q

/-- Every connected interacting Gaussian ring is represented by positive powers
of the contact insertion and any number of the material mixing factor. -/
def vacuumRing (r Ω : ℝ) (contacts mixingPairs : ℕ) (q : ℝ × SpatialMomentum) : ℝ :=
  ringInsertion r q ^ (contacts + 1) * materialInsertion Ω q.1 ^ mixingPairs

theorem vacuumRing_bounds {r : ℝ} (hr : 0 ≤ r) (Ω : ℝ) (contacts mixingPairs : ℕ)
    (q : ℝ × SpatialMomentum) :
    0 ≤ vacuumRing r Ω contacts mixingPairs q ∧
      vacuumRing r Ω contacts mixingPairs q ≤ ringInsertion r q := by
  have hu := ringInsertion_nonneg r q
  have hu1 := ringInsertion_le_one hr q
  have hv := materialInsertion_bounds Ω q.1
  have hpow : ringInsertion r q ^ (contacts + 1) ≤ ringInsertion r q := by
    rw [pow_succ]
    exact mul_le_of_le_one_left hu (pow_le_one₀ hu hu1)
  unfold vacuumRing
  refine ⟨mul_nonneg (pow_nonneg hu _) (pow_nonneg hv.1 _), ?_⟩
  exact (mul_le_of_le_one_right (pow_nonneg hu _) (pow_le_one₀ hv.1 hv.2)).trans hpow

/-- Every finite perturbative ring, before cancellations with the direct contact,
is absolutely integrable in all four momentum variables. -/
theorem vacuumRing_integrable {r : ℝ} (hr : 0 < r) (Ω : ℝ) (contacts mixingPairs : ℕ) :
    Integrable (vacuumRing r Ω contacts mixingPairs) := by
  apply (ringInsertion_integrable hr).mono'
  · have hm : Measurable (vacuumRing r Ω contacts mixingPairs) := by
      unfold vacuumRing ringInsertion materialInsertion
      fun_prop
    exact hm.aestronglyMeasurable
  · exact Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (vacuumRing_bounds hr.le Ω contacts mixingPairs q).1]
      exact (vacuumRing_bounds hr.le Ω contacts mixingPairs q).2

/-- Literal ring with any numbers of contacts and pairs of mixing vertices. -/
def contactMixingRing (r Ω : ℝ) (contacts mixingPairs : ℕ) (q : ℝ × SpatialMomentum) : ℝ :=
  ringInsertion r q ^ (contacts + mixingPairs) * materialInsertion Ω q.1 ^ mixingPairs

theorem contactMixingRing_integrable {r : ℝ} (hr : 0 < r) (Ω : ℝ)
    (contacts mixingPairs : ℕ) (hNonempty : 0 < contacts + mixingPairs) :
    Integrable (contactMixingRing r Ω contacts mixingPairs) := by
  have hn : contacts + mixingPairs - 1 + 1 = contacts + mixingPairs :=
    Nat.sub_add_cancel hNonempty
  have he : contactMixingRing r Ω contacts mixingPairs =
      vacuumRing r Ω (contacts + mixingPairs - 1) mixingPairs := by
    funext q
    change ringInsertion r q ^ (contacts + mixingPairs) * materialInsertion Ω q.1 ^ mixingPairs =
      ringInsertion r q ^ (contacts + mixingPairs - 1 + 1) * materialInsertion Ω q.1 ^ mixingPairs
    rw [hn]
  rw [he]
  exact vacuumRing_integrable hr Ω (contacts + mixingPairs - 1) mixingPairs

/-- Every finite disconnected collection keeps its own independent four-momentum
per ring. No identification of loop variables enters the bound. -/
theorem finite_independent_vacuum_rings_integrable {ι : Type*} [Fintype ι]
    {r : ℝ} (hr : 0 < r) (Ω : ℝ) (n j : ι → ℕ) :
    Integrable (fun q : ι → ℝ × SpatialMomentum =>
      ∏ i, vacuumRing r Ω (n i) (j i) (q i))
      (Measure.pi (fun _ : ι => (volume : Measure (ℝ × SpatialMomentum)))) := by
  exact Integrable.fintype_prod fun i => vacuumRing_integrable hr Ω (n i) (j i)

/-- Finite linear combinations of the separate contact/mixing rings retain
absolute convergence at every prescribed perturbative order. -/
theorem finite_vacuum_coefficient_integrable {ι : Type*} (s : Finset ι)
    {r : ℝ} (hr : 0 < r) (Ω : ℝ) (a : ι → ℝ) (n j : ι → ℕ) :
    Integrable (fun q => ∑ i ∈ s, a i * vacuumRing r Ω (n i) (j i) q) := by
  exact integrable_finset_sum _ fun i _ => (vacuumRing_integrable hr Ω (n i) (j i)).const_mul _

/-- Finite products of disconnected rings use independent full momentum variables. -/
theorem independent_vacuum_rings_integrable {r : ℝ} (hr : 0 < r) (Ω : ℝ)
    (n₁ j₁ n₂ j₂ : ℕ) :
    Integrable (fun q : (ℝ × SpatialMomentum) × (ℝ × SpatialMomentum) =>
      vacuumRing r Ω n₁ j₁ q.1 * vacuumRing r Ω n₂ j₂ q.2) :=
  (vacuumRing_integrable hr Ω n₁ j₁).mul_prod (vacuumRing_integrable hr Ω n₂ j₂)

/-- The complete relative determinant retains the direct contact and mixing. -/
def determinantKernel (r Ω : ℝ) (q : ℝ × SpatialMomentum) : ℝ :=
  ringInsertion r q * (1 - materialInsertion Ω q.1)

theorem determinantKernel_bounds {r : ℝ} (hr : 0 ≤ r) (Ω : ℝ)
    (q : ℝ × SpatialMomentum) :
    0 ≤ determinantKernel r Ω q ∧ determinantKernel r Ω q ≤ ringInsertion r q ∧
      determinantKernel r Ω q ≤ 1 := by
  have hu := ringInsertion_nonneg r q
  have hv := materialInsertion_bounds Ω q.1
  have hw : 0 ≤ 1 - materialInsertion Ω q.1 := sub_nonneg.mpr hv.2
  have hwu : determinantKernel r Ω q ≤ ringInsertion r q :=
    mul_le_of_le_one_right hu (by linarith [hv.1])
  exact ⟨mul_nonneg hu hw, hwu, hwu.trans (ringInsertion_le_one hr q)⟩

/-- This is the determinant of the actual two-field Euclidean precision relative
to the free determinant, not an imposed ultraviolet multiplier. -/
theorem precision_relative_determinant {Ω : ℝ} (hΩ : 0 < Ω) (r g : ℝ)
    (q : ℝ × SpatialMomentum) (hq : q.2 ≠ 0) :
    Matrix.det (precision Ω r g ‖q.2‖ (q.1 ^ 2)) /
        ((q.1 ^ 2 + ‖q.2‖ ^ 2) * (q.1 ^ 2 + Ω ^ 2)) =
      1 + g ^ 2 * determinantKernel r Ω q := by
  have hs := normal_frequency_sum hΩ r g ‖q.2‖
  have hp := normal_frequency_product hΩ r g ‖q.2‖
  have hsx := congrArg (fun t : ℝ => q.1 ^ 2 * t) hs
  dsimp at hsx
  unfold frequencySum mixing at hs hsx
  rw [precision_determinant hΩ]
  unfold determinantKernel ringInsertion materialInsertion
  have hk := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hq)
  have hden : q.1 ^ 2 + ‖q.2‖ ^ 2 ≠ 0 := by positivity
  have hdenΩ : q.1 ^ 2 + Ω ^ 2 ≠ 0 := by positivity
  field_simp
  have he : -(2 * r * ‖q.2‖) = -(‖q.2‖ * 2 * r) := by ring
  rw [he] at hsx
  nlinarith

/-- Coefficient at electric order 2(n+1) in half of the logarithm of the
relative determinant. -/
def bareVacuumCoefficient (r Ω : ℝ) (n : ℕ) (q : ℝ × SpatialMomentum) : ℝ :=
  -((-determinantKernel r Ω q) ^ (n + 1) / (n + 1)) / 2

theorem bareVacuumCoefficient_integrable {r : ℝ} (hr : 0 < r) (Ω : ℝ) (n : ℕ) :
    Integrable (bareVacuumCoefficient r Ω n) := by
  have hpow : Integrable (fun q => (-determinantKernel r Ω q) ^ (n + 1)) := by
    apply (ringInsertion_integrable hr).mono'
    · have hm : Measurable (fun q => (-determinantKernel r Ω q) ^ (n + 1)) := by
        unfold determinantKernel ringInsertion materialInsertion
        fun_prop
      exact hm.aestronglyMeasurable
    · refine Eventually.of_forall fun q => ?_
      have hw := determinantKernel_bounds hr.le Ω q
      rw [norm_pow, norm_neg, Real.norm_of_nonneg hw.1, pow_succ]
      exact (mul_le_of_le_one_left hw.1 (pow_le_one₀ hw.1 hw.2.2)).trans hw.2.1
  exact (hpow.div_const (n + 1)).neg.div_const 2

/-- Genuine logarithmic expansion of the specified Gaussian determinant, with
all coefficients already proved absolutely integrable above. -/
theorem bareVacuumCoefficient_hasSum {r : ℝ} (hr : 0 ≤ r) (Ω g : ℝ)
    (hg : g ^ 2 < 1) (q : ℝ × SpatialMomentum) :
    HasSum (fun n : ℕ => g ^ (2 * (n + 1)) * bareVacuumCoefficient r Ω n q)
      (Real.log (1 + g ^ 2 * determinantKernel r Ω q) / 2) := by
  have hw := determinantKernel_bounds hr Ω q
  have hsmall : |-(g ^ 2 * determinantKernel r Ω q)| < 1 := by
    rw [abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg g) hw.1)]
    exact (mul_le_of_le_one_right (sq_nonneg g) hw.2.2).trans_lt hg
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hsmall).mul_left (-(1 / 2 : ℝ))
  convert h using 1
  · funext n
    unfold bareVacuumCoefficient
    rw [show -(g ^ 2 * determinantKernel r Ω q) = g ^ 2 * (-determinantKernel r Ω q) by ring,
      mul_pow, pow_mul]
    ring
  · simp only [sub_neg_eq_add]
    ring

/-- The exact resummed vacuum shift is also integrable at arbitrary real coupling. -/
def vacuumShift (Ω r g : ℝ) (k : SpatialMomentum) : ℝ :=
  (Real.sqrt ((‖k‖ + Ω) ^ 2 + g ^ 2 * ‖k‖ ^ 2 * Real.exp (-(2 * r * ‖k‖))) -
    (‖k‖ + Ω)) / 2

theorem vacuumShift_normal_energies {Ω : ℝ} (hΩ : 0 < Ω)
    (r g : ℝ) (k : SpatialMomentum) :
    vacuumShift Ω r g k =
      (Real.sqrt (lowFrequency Ω r g ‖k‖) + Real.sqrt (highFrequency Ω r g ‖k‖) -
        (‖k‖ + Ω)) / 2 := by
  rw [normal_energy_sum hΩ (norm_nonneg k)]
  rfl

theorem vacuumShift_bounds {Ω : ℝ} (hΩ : 0 < Ω) (r g : ℝ) (k : SpatialMomentum) :
    0 ≤ vacuumShift Ω r g k ∧ vacuumShift Ω r g k ≤
      g ^ 2 * ‖k‖ ^ 2 * Real.exp (-(2 * r * ‖k‖)) / (4 * (‖k‖ + Ω)) := by
  let a := ‖k‖ + Ω
  let c := g ^ 2 * ‖k‖ ^ 2 * Real.exp (-(2 * r * ‖k‖))
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hs : Real.sqrt (a ^ 2 + c) ^ 2 = a ^ 2 + c := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (a ^ 2 + c) := Real.sqrt_nonneg _
  have hsle : a ≤ Real.sqrt (a ^ 2 + c) := by nlinarith
  change 0 ≤ (Real.sqrt (a ^ 2 + c) - a) / 2 ∧
    (Real.sqrt (a ^ 2 + c) - a) / 2 ≤ c / (4 * a)
  constructor
  · linarith
  · apply (le_div_iff₀ (by positivity : 0 < 4 * a)).mpr
    nlinarith [sq_nonneg (Real.sqrt (a ^ 2 + c) - a)]

theorem vacuumShift_integrable {Ω r : ℝ} (hΩ : 0 < Ω) (hr : 0 < r) (g : ℝ) :
    Integrable (vacuumShift Ω r g) := by
  have hi := (UV.integrable_norm_pow_exp (μ := (volume : Measure SpatialMomentum))
    (by linarith : 0 < 2*r) 2).const_mul (g ^ 2 / (4 * Ω))
  apply hi.mono'
  · unfold vacuumShift
    fun_prop
  · exact Eventually.of_forall fun k => by
      rw [Real.norm_of_nonneg (vacuumShift_bounds hΩ r g k).1]
      apply (vacuumShift_bounds hΩ r g k).2.trans
      have hnum : 0 ≤ g ^ 2 * ‖k‖ ^ 2 * Real.exp (-(2 * r * ‖k‖)) := by positivity
      calc
        _ ≤ (g ^ 2 * ‖k‖ ^ 2 * Real.exp (-(2 * r * ‖k‖))) / (4 * Ω) :=
          div_le_div_of_nonneg_left hnum (by positivity) (by linarith [norm_nonneg k])
        _ = _ := by ring

/-- Positive intrinsic radial momentum is measured along a normalized direction
of the same selected sector plane. The carrier direction remains norm one. -/
theorem selected_plane_radial_normalization {E : Type*} [Norm E]
    (diamond : SectorPlane.Plane E) (n : SectorPlane.UnitVector SpatialMomentum)
    {k : ℝ} (hk : 0 ≤ k) :
    ‖diamond.Ghat.val‖ = 1 ∧ ‖k • n.val‖ = k := by
  refine ⟨diamond.Ghat.property, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg hk, n.property, mul_one]

end UV.ResumeCarrierPolarization
