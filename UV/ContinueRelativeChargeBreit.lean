import UV.ContinueRelativeCharge
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Transverse Breit sequence for the Gaussian relative Wilson chord.
The volume integral is the uniform straight-chord parameter average in the
continuum vertex. The free external residues are evaluated at rest. -/

noncomputable section

open Filter
open scoped Topology RealInnerProductSpace Matrix.Norms.Elementwise

namespace UV.SectorPlane

def chordBreitEnergy (m t : ℝ) : ℝ :=
  Real.sqrt (m ^ 2 + t ^ 2 / 4)

def chordBreitSpatial (u : UnitVector Spatial) (t a : ℝ) : Spatial :=
  ((a - 1 / 2) * t) • (u : Spatial)

/-- The interpolation from the incoming leg at a = 0 to the outgoing leg
at a = 1 has an unchanged carrier coordinate. -/
def chordBreitMomentum (m : ℝ) (u : UnitVector Spatial) (t a : ℝ) : ChordMomentum :=
  (Complex.I * (chordBreitEnergy m t : ℂ), fun j => (chordBreitSpatial u t a j : ℂ))

theorem chord_breit_spatial_norm_sq (u : UnitVector Spatial) (t a : ℝ) :
    ‖chordBreitSpatial u t a‖ ^ 2 = ((a - 1 / 2) * t) ^ 2 := by
  simp only [chordBreitSpatial, norm_smul, Real.norm_eq_abs, u.property, mul_one, sq_abs]

theorem chord_breit_positive_energy_on_shell (m t : ℝ) (u : UnitVector Spatial) :
    shellSquare (chordBreitEnergy m t) (chordBreitSpatial u t 0) = m ^ 2 ∧
      shellSquare (chordBreitEnergy m t) (chordBreitSpatial u t 1) = m ^ 2 := by
  have he : chordBreitEnergy m t ^ 2 = m ^ 2 + t ^ 2 / 4 :=
    Real.sq_sqrt (by positivity)
  constructor <;> rw [shellSquare, he, chord_breit_spatial_norm_sq] <;> ring

theorem chord_breit_energy_pos {m : ℝ} (hm : 0 < m) (t : ℝ) :
    0 < chordBreitEnergy m t :=
  Real.sqrt_pos.mpr (by positivity)

theorem chord_breit_analytic_square (m : ℝ) (u : UnitVector Spatial) (t a : ℝ) :
    chordSquare (chordBreitMomentum m u t a) =
      -(shellSquare (chordBreitEnergy m t) (chordBreitSpatial u t a) : ℂ) := by
  rw [chordSquare, shellSquare, EuclideanSpace.norm_sq_eq]
  simp [chordBreitMomentum, mul_pow, Complex.I_sq, Real.norm_eq_abs, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, sub_eq_add_neg, add_comm]

theorem chord_breit_spatial_difference (u : UnitVector Spatial) (t : ℝ) :
    chordBreitSpatial u t 1 - chordBreitSpatial u t 0 = t • (u : Spatial) := by
  simp only [chordBreitSpatial, ← sub_smul]
  congr 1
  ring

theorem chord_breit_at_zero {m : ℝ} (hm : 0 ≤ m) (u : UnitVector Spatial) (a : ℝ) :
    chordBreitMomentum m u 0 a = chordRest m := by
  simp [chordBreitMomentum, chordBreitEnergy, chordBreitSpatial, chordRest, Real.sqrt_sq hm, Pi.zero_def]

/-- The polarization is the actual plane's carrier unit and the momentum
transfer lies entirely in the spatial plane. Their inner product vanishes
for the complete sequence, including nonzero transfers t. -/
theorem Plane.chord_breit_transverse {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (diamond : Plane E) (u : UnitVector Spatial) (t : ℝ) :
    let polarization := WithLp.toLp 2 ((diamond.poleUnit : E), (0 : Spatial))
    let transfer := WithLp.toLp 2 ((0 : E), t • (u : Spatial))
    ‖polarization‖ = 1 ∧ ⟪polarization, transfer⟫ = 0 := by
  dsimp
  constructor
  · rw [WithLp.prod_norm_eq_of_L2]
    simp [diamond.poleUnit.property]
  · simp

/-- At both real external momenta the vectorial prescription still
uses the fixed pole root, the assigned sector sign, and positive height. -/
theorem Plane.chord_breit_pole_denominator {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε : Evolution) (height : Height)
    (m t : ℝ) (u : UnitVector Spatial) :
    let prescribed a := diamond.poleDenominator ε height
      (shellSquare (chordBreitEnergy m t) (chordBreitSpatial u t a) - m ^ 2)
    prescribed 0 = directed (Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ)) ∧
      prescribed 1 = directed (Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ)) := by
  obtain ⟨h₀, h₁⟩ := chord_breit_positive_energy_on_shell m t u
  simp [Plane.poleDenominator, h₀, h₁]

theorem continuous_chord_breit_momentum (m : ℝ) (u : UnitVector Spatial) :
    Continuous (fun ta : ℝ × ℝ => chordBreitMomentum m u ta.1 ta.2) := by
  unfold chordBreitMomentum chordBreitEnergy chordBreitSpatial
  fun_prop

theorem continuous_chord_axial_vertex (σ : ℝ) : Continuous (chordAxialVertex σ) := by
  unfold chordAxialVertex chordAxialDerivative chordGaussian chordSquare
  dsimp
  fun_prop

/-- The harmonic readout at a transverse spatial transfer t·u. -/
def chordBreitReadout (r : ℝ) (u : UnitVector Spatial) (t : ℝ) : ℝ :=
  Real.exp (-r * ‖t • (u : Spatial)‖)

theorem chord_breit_readout_eq (r : ℝ) (u : UnitVector Spatial) (t : ℝ) :
    chordBreitReadout r u t = Real.exp (-r * |t|) := by
  simp [chordBreitReadout, norm_smul, Real.norm_eq_abs, u.property]

theorem chord_breit_readout_limit (r : ℝ) (u : UnitVector Spatial) :
    Tendsto (chordBreitReadout r u) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (chordBreitReadout r u) := by
    unfold chordBreitReadout
    fun_prop
  simpa [chordBreitReadout] using hc.continuousAt (x := 0).tendsto

def chordBreitVertex (e r m σ : ℝ) (u : UnitVector Spatial) (t : ℝ) : DiracMatrix :=
  ((e * chordBreitReadout r u t : ℝ) : ℂ) •
    (∫ a in (0 : ℝ)..1, chordAxialVertex σ (chordBreitMomentum m u t a))

theorem continuous_chord_breit_vertex (e r m σ : ℝ) (u : UnitVector Spatial) :
    Continuous (chordBreitVertex e r m σ u) := by
  have hc : Continuous (fun ta : ℝ × ℝ => chordAxialVertex σ
      (chordBreitMomentum m u ta.1 ta.2)) :=
    (continuous_chord_axial_vertex σ).comp (continuous_chord_breit_momentum m u)
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) (f := fun t a => chordAxialVertex σ (chordBreitMomentum m u t a))
    hc 0 1
  unfold chordBreitVertex chordBreitReadout
  fun_prop

/-- The projected continuum finite-transfer vertex tends to the tree
charge times the minimally coupled unit-charge rest matrix. -/
theorem chord_breit_vertex_rest_limit (e r m σ : ℝ) (hm : 0 < m) (u : UnitVector Spatial) :
    Tendsto (fun t => chordRestProjector * chordBreitVertex e r m σ u t * chordRestProjector)
      (𝓝 0) (𝓝 (((e * chordChargeFactor (m ^ 2 * σ ^ 2) : ℝ) : ℂ) • chordRestProjector)) := by
  have hc : Continuous (fun t => chordRestProjector * chordBreitVertex e r m σ u t *
      chordRestProjector) := by
    have hv := continuous_chord_breit_vertex e r m σ u
    fun_prop
  have hzero : chordRestProjector * chordBreitVertex e r m σ u 0 * chordRestProjector =
      (((e * chordChargeFactor (m ^ 2 * σ ^ 2) : ℝ) : ℂ) • chordRestProjector) := by
    simp only [chordBreitVertex, chordBreitReadout, zero_smul, norm_zero, mul_zero, Real.exp_zero,
      mul_one, chord_breit_at_zero hm.le, intervalIntegral.integral_const, sub_zero, one_smul]
    exact (chord_rest_charge_ratio m σ e _).mpr rfl
  simpa only [hzero] using hc.continuousAt (x := 0).tendsto

/-- The derivative of the massive Lorentzian denominator in the
positive exterior carrier coordinate at each Breit momentum. -/
theorem chord_breit_shell_axial_derivative (m : ℝ) (u : UnitVector Spatial) (t a : ℝ) :
    HasDerivAt (fun p => shellSquare p (chordBreitSpatial u t a) - m ^ 2)
      (2 * chordBreitEnergy m t) (chordBreitEnergy m t) := by
  simpa [shellSquare] using (((hasDerivAt_id (chordBreitEnergy m t)).pow 2).sub_const
    (‖chordBreitSpatial u t a‖ ^ 2)).sub_const (m ^ 2)

/-- Free numerator divided by the carrier derivative of the Lorentzian
denominator. This supplies the same normalized rest limit at a = 0, 1. -/
def chordBreitResidue (m : ℝ) (u : UnitVector Spatial) (t a : ℝ) : DiracMatrix :=
  let k := chordBreitMomentum m u t a
  (2 * (chordBreitEnergy m t : ℂ))⁻¹ •
    (chordFreeAxialNumerator m k.1 +
      ∑ j : Fin 3, (-(Complex.I * k.2 j)) • euclideanGamma j.succ)

theorem chord_breit_residue_at_zero {m : ℝ} (hm : 0 < m) (u : UnitVector Spatial) (a : ℝ) :
    chordBreitResidue m u 0 a = chordRestProjector := by
  unfold chordBreitResidue
  rw [chord_breit_at_zero hm.le]
  simpa [chordRest, chordBreitEnergy, Real.sqrt_sq hm.le] using chord_rest_normalized_residue m hm

theorem continuous_chord_breit_residue {m : ℝ} (hm : 0 < m) (u : UnitVector Spatial) (a : ℝ) :
    Continuous (fun t => chordBreitResidue m u t a) := by
  have he : Continuous (fun t => 2 * (chordBreitEnergy m t : ℂ)) := by
    unfold chordBreitEnergy
    fun_prop
  have hne (t : ℝ) : 2 * (chordBreitEnergy m t : ℂ) ≠ 0 := by
    have ht : (chordBreitEnergy m t : ℂ) ≠ 0 := by
      exact_mod_cast (chord_breit_energy_pos hm t).ne'
    exact mul_ne_zero (by norm_num) ht
  have hi : Continuous (fun t : ℝ => (2 * (chordBreitEnergy m t : ℂ))⁻¹) := he.inv₀ hne
  unfold chordBreitResidue chordFreeAxialNumerator
  dsimp
  refine hi.smul ?_
  unfold chordBreitMomentum chordBreitEnergy chordBreitSpatial
  fun_prop

/-- The finite-transfer vertex with both exterior free residues tends to
the oriented tree charge times the same unit-charge rest matrix. -/
theorem chord_breit_residue_vertex_limit (e r m σ : ℝ) (hm : 0 < m) (u : UnitVector Spatial) :
    Tendsto (fun t => chordBreitResidue m u t 1 * chordBreitVertex e r m σ u t *
      chordBreitResidue m u t 0) (𝓝 0)
      (𝓝 (((e * chordChargeFactor (m ^ 2 * σ ^ 2) : ℝ) : ℂ) • chordRestProjector)) := by
  have hc : Continuous (fun t => chordBreitResidue m u t 1 * chordBreitVertex e r m σ u t *
      chordBreitResidue m u t 0) := by
    have hl := continuous_chord_breit_residue hm u 1
    have hr := continuous_chord_breit_residue hm u 0
    have hv := continuous_chord_breit_vertex e r m σ u
    fun_prop
  have hzero : chordBreitResidue m u 0 1 * chordBreitVertex e r m σ u 0 *
      chordBreitResidue m u 0 0 =
      (((e * chordChargeFactor (m ^ 2 * σ ^ 2) : ℝ) : ℂ) • chordRestProjector) := by
    simp only [chord_breit_residue_at_zero hm, chordBreitVertex, chordBreitReadout, zero_smul,
      norm_zero, mul_zero, Real.exp_zero, mul_one, chord_breit_at_zero hm.le,
      intervalIntegral.integral_const, sub_zero, one_smul]
    exact (chord_rest_charge_ratio m σ e _).mpr rfl
  simpa only [hzero] using hc.continuousAt (x := 0).tendsto

theorem chord_breit_residue_vertex_punctured_limit (e r m σ : ℝ) (hm : 0 < m)
    (u : UnitVector Spatial) :
    Tendsto (fun t => chordBreitResidue m u t 1 * chordBreitVertex e r m σ u t *
      chordBreitResidue m u t 0) (𝓝[≠] 0)
      (𝓝 (((e * chordChargeFactor (m ^ 2 * σ ^ 2) : ℝ) : ℂ) • chordRestProjector)) :=
  (chord_breit_residue_vertex_limit e r m σ hm u).mono_left nhdsWithin_le_nhds

end UV.SectorPlane
