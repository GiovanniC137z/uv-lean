import UV.ContinueTwoBandProjectors
import UV.ContinueTwoBandCoulombTail
import UV.ContinueRigidSphereRadial

/-! Positive spectral representation of the order-two Coulomb energy.
Momentum transfer and charged momentum are independently integrated on
the selected plane, with the original harmonic and Gaussian readouts. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace UV.SectorPlane

def twoBandSpatialWeight (m g σ : ℝ) (k p : Spatial) : ℝ :=
  twoBandTransitionWeight m (twoBandSpatialHop g σ k) (twoBandSpatialHop g σ (k+p))

@[fun_prop] theorem continuous_twoBandSpatialWeight {m : ℝ} (hm : 0 < m) (g σ : ℝ) :
    Continuous (fun u : Spatial × Spatial => twoBandSpatialWeight m g σ u.2 u.1) := by
  unfold twoBandSpatialWeight twoBandTransitionWeight
  fun_prop (disch := intros; exact mul_ne_zero (twoBand_gap_pos hm _).ne' (twoBand_gap_pos hm _).ne')

private theorem hop_sq_bound (g σ : ℝ) (k : Spatial) :
    (twoBandSpatialHop g σ k)^2 ≤ |g| * |twoBandSpatialHop g σ k| := by
  have h : |twoBandSpatialHop g σ k| ≤ |g| := by
    simp only [twoBandSpatialHop,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
  simpa only [←sq, sq_abs] using mul_le_mul_of_nonneg_right h (abs_nonneg (twoBandSpatialHop g σ k))

private def weightMajorant (m g σ : ℝ) (k p : Spatial) : ℝ :=
  (|g|/(2*m^2))*(|twoBandSpatialHop g σ k|+|twoBandSpatialHop g σ (k+p)|)

private theorem spatialWeight_le {m : ℝ} (hm : 0 < m) (g σ : ℝ) (k p : Spatial) :
    twoBandSpatialWeight m g σ k p ≤ weightMajorant m g σ k p := by
  let v := twoBandSpatialHop g σ k
  let w := twoBandSpatialHop g σ (k+p)
  apply (twoBand_transition_upper hm v w).trans
  change (v-w)^2/(4*m^2) ≤ (|g|/(2*m^2))*(|v|+|w|)
  field_simp [hm.ne']
  nlinarith only [sq_nonneg (v+w), (hop_sq_bound g σ k : v^2 ≤ _),
    (hop_sq_bound g σ (k+p) : w^2 ≤ _)]

theorem twoBand_spatial_weight_integral {m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (g : ℝ) (p : Spatial) :
    Integrable (fun k => twoBandSpatialWeight m g σ k p) ∧
    (∫ k, twoBandSpatialWeight m g σ k p) ≤
      (|g|/m^2)*(∫ k, |twoBandSpatialHop g σ k|) := by
  let f := fun k : Spatial => |twoBandSpatialHop g σ k|
  have hi : Integrable f := twoBand_spatial_hop_integrable g hσ
  have ht := measurePreserving_add_right (volume : Measure Spatial) p
  have hj : Integrable (fun k => f (k+p)) := ht.integrable_comp_of_integrable hi
  have hM : Integrable (fun k => weightMajorant m g σ k p) :=
    (hi.add hj).const_mul _
  have hW : Integrable (fun k => twoBandSpatialWeight m g σ k p) := by
    apply hM.mono' ((continuous_twoBandSpatialWeight hm g σ).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    filter_upwards with k
    change ‖twoBandSpatialWeight m g σ k p‖ ≤ _
    rw [Real.norm_of_nonneg (show 0 ≤ twoBandSpatialWeight m g σ k p from twoBand_transition_nonneg hm _ _)]
    exact spatialWeight_le hm g σ k p
  refine ⟨hW,(integral_mono hW hM (fun k => spatialWeight_le hm g σ k p)).trans_eq ?_⟩
  change (∫ k, (|g|/(2*m^2))*(f k+f (k+p))) = _
  rw [integral_const_mul, integral_add hi hj, integral_add_right_eq_self f]
  change _ = (|g|/m^2)*(∫ k, f k)
  ring

def twoBandCoulombSpatialDensity (m g σ q a : ℝ) (u : Spatial × Spatial) : ℝ :=
  twoBandCoulombMultiplier q a u.1 * twoBandSpatialWeight m g σ u.2 u.1

theorem twoBand_coulomb_spatial_density_nonneg {m : ℝ} (hm : 0 < m) (g σ q a : ℝ)
    (u : Spatial × Spatial) : 0 ≤ twoBandCoulombSpatialDensity m g σ q a u :=
  mul_nonneg (by unfold twoBandCoulombMultiplier; positivity) (twoBand_transition_nonneg hm _ _)

theorem twoBand_positive_coulomb_spatial {m σ a : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (ha : 0 < a) (g q : ℝ) : Integrable (twoBandCoulombSpatialDensity m g σ q a) := by
  let M := twoBandCoulombMultiplier q a
  let W := twoBandSpatialWeight m g σ
  have hmM : Measurable M := by unfold M twoBandCoulombMultiplier; fun_prop
  have hNon (p : Spatial) : 0 ≤ M p := by unfold M twoBandCoulombMultiplier; positivity
  have hi : Integrable M := by
    have h := UV.ContinueRigidLaw.spatial_coulombIntegral ha
    have h0 := Integrable.of_integral_ne_zero (h.trans_ne (by positivity))
    change Integrable (fun p : Spatial => q^2 * _ / ‖p‖^2)
    simpa only [mul_div_assoc] using h0.const_mul (q^2)
  have hMeas := ((hmM.comp measurable_fst).mul (continuous_twoBandSpatialWeight hm g σ).measurable)
  apply (integrable_prod_iff hMeas.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun p => ((twoBand_spatial_weight_integral hm hσ g p).1).const_mul (M p)
  · apply (hi.mul_const ((|g|/m^2)*(∫ k, |twoBandSpatialHop g σ k|))).mono'
      hMeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    change (∫ k, ‖M p * W k p‖) ≤ _
    have hW (k : Spatial) : 0 ≤ M p * W k p := mul_nonneg (hNon p) (twoBand_transition_nonneg hm _ _)
    simp_rw [Real.norm_of_nonneg (hW _)]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (twoBand_spatial_weight_integral hm hσ g p).2 (hNon p)

def twoBandLorentzDensity (E v : ℝ) : ℝ := (2*E/(v^2+E^2))/(2*Real.pi)

theorem twoBand_lorentz_density_normalized {E : ℝ} (hE : 0 < E) :
    Integrable (twoBandLorentzDensity E) ∧ (∫ v, twoBandLorentzDensity E v) = 1 := by
  have he : twoBandLorentzDensity E = fun v => (E/Real.pi)*(twoBandFrequencyBound E v)^2 := by
    funext v
    rw [twoBand_frequency_bound_sq]
    unfold twoBandLorentzDensity
    ring
  rw [he, integral_const_mul, (twoBand_frequency_integral hE).2]
  exact ⟨(twoBand_frequency_integral hE).1.const_mul _, by field_simp [Real.pi_ne_zero,hE.ne']⟩

/-- Original charged frequency and transferred photon frequency, including
both factors of the Fourier measure. -/
def twoBandFrequencyPair (E F : ℝ) (x : ℝ × ℝ) : ℝ :=
  twoBandLorentzDensity E x.1 * twoBandLorentzDensity F (x.1+x.2)

theorem twoBand_positive_frequency_pair {E F : ℝ} (hE : 0 < E) (hF : 0 < F) :
    Integrable (twoBandFrequencyPair E F) ∧ (∫ z, twoBandFrequencyPair E F z) = 1 := by
  have hMeas : Measurable (twoBandFrequencyPair E F) := by
    unfold twoBandFrequencyPair twoBandLorentzDensity
    fun_prop
  have hN (z : ℝ × ℝ) : 0 ≤ twoBandFrequencyPair E F z := by
    unfold twoBandFrequencyPair twoBandLorentzDensity
    positivity
  have hi (v : ℝ) : Integrable (fun Ω => twoBandFrequencyPair E F (v,Ω)) :=
    ((measurePreserving_add_left volume v).integrable_comp_of_integrable
      (twoBand_lorentz_density_normalized hF).1).const_mul (twoBandLorentzDensity E v)
  have hMass (v : ℝ) : (∫ Ω, twoBandFrequencyPair E F (v,Ω)) = twoBandLorentzDensity E v := by
    simp only [twoBandFrequencyPair, integral_const_mul, integral_add_left_eq_self,
      (twoBand_lorentz_density_normalized hF).2, mul_one]
  have hI : Integrable (twoBandFrequencyPair E F) := by
    apply (integrable_prod_iff hMeas.aestronglyMeasurable).mpr
    simp_rw [Real.norm_of_nonneg (hN _), hMass]
    exact ⟨ae_of_all _ hi,(twoBand_lorentz_density_normalized hE).1⟩
  refine ⟨hI, ?_⟩
  calc
    _ = ∫ v, ∫ Ω, twoBandFrequencyPair E F (v,Ω) := integral_prod _ hI
    _ = _ := by simp only [hMass, (twoBand_lorentz_density_normalized hE).2]

/-- The strictly positive energy density occupies an open set of transfers
and charged momenta as soon as both the charge and hopping are nonzero. -/
theorem twoBand_positive_coulomb_spatial_mass {m σ a g q : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (ha : 0 < a) (hg : g ≠ 0) (hq : q ≠ 0) :
    0 < ∫ u, twoBandCoulombSpatialDensity m g σ q a u := by
  let U := {u : Spatial × Spatial | u.1 ≠ 0 ∧
    twoBandSpatialHop g σ u.2 ≠ twoBandSpatialHop g σ (u.2+u.1)}
  have hU : IsOpen U := (isOpen_ne_fun continuous_fst continuous_const).inter
    (isOpen_ne_fun ((continuous_twoBandSpatialHop g σ).comp continuous_snd)
      ((continuous_twoBandSpatialHop g σ).comp (continuous_snd.add continuous_fst)))
  let d : UnitVector Spatial := ⟨EuclideanSpace.single (0 : Fin 3) (1:ℝ), by simp⟩
  have hNonempty : U.Nonempty := by
    refine ⟨(d.val,0), (norm_pos_iff.mp (show 0 < ‖d.val‖ by rw [d.property]; norm_num)), ?_⟩
    change twoBandSpatialHop g σ 0 ≠ twoBandSpatialHop g σ ((0:Spatial)+d.val)
    simp only [twoBandSpatialHop, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, neg_zero, Real.exp_zero, mul_one, zero_add, d.property, one_pow]
    intro h
    have he : Real.exp (-(σ^2)) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (sq_pos_of_pos hσ))
    exact he.ne (mul_right_injective₀ hg (show g * Real.exp (-(σ^2)) = g*1 by linarith))
  apply (integral_pos_iff_support_of_nonneg (twoBand_coulomb_spatial_density_nonneg hm g σ q a)
    (twoBand_positive_coulomb_spatial hm hσ ha g q)).mpr
  apply (hU.measure_pos volume hNonempty).trans_le
  apply measure_mono
  intro u hu
  exact (mul_pos (twoBand_coulomb_multiplier_pos hq hu.1) (twoBand_transition_pos hm hu.2)).ne'

def twoBandPositiveCoulombIntegrand (m g σ q a : ℝ) (x : (Spatial × Spatial) × (ℝ × ℝ)) : ℝ :=
  (1/(2*(2*Real.pi)^6)) * twoBandCoulombSpatialDensity m g σ q a x.1 *
    twoBandFrequencyPair (twoBandGap m (twoBandSpatialHop g σ x.1.2))
      (twoBandGap m (twoBandSpatialHop g σ (x.1.2+x.1.1))) x.2

private theorem positive_pair_integral {X : Type*} [MeasureSpace X] [SigmaFinite (volume : Measure X)]
    (D : X → ℝ) (A B : X → ℝ) (hi : Integrable D) (hn : ∀ u, 0 ≤ D u)
    (ha : ∀ u, 0 < A u) (hb : ∀ u, 0 < B u) (hA : Measurable A) (hB : Measurable B) :
    let f := fun z : X × (ℝ × ℝ) => D z.1 * twoBandFrequencyPair (A z.1) (B z.1) z.2
    Integrable f ∧ (∫ z, f z) = ∫ u, D u := by
  intro f
  have hm : AEStronglyMeasurable f volume := by
    have hF : Measurable (fun z : X × (ℝ × ℝ) => twoBandFrequencyPair (A z.1) (B z.1) z.2) := by
      unfold twoBandFrequencyPair twoBandLorentzDensity
      fun_prop
    exact (hi.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul hF.aestronglyMeasurable
  have hN (z : X × (ℝ × ℝ)) : 0 ≤ f z := by
    apply mul_nonneg (hn z.1)
    unfold twoBandFrequencyPair twoBandLorentzDensity
    have h₁ := ha z.1
    have h₂ := hb z.1
    positivity
  have hS (u : X) : Integrable (fun z => f (u,z)) :=
    (twoBand_positive_frequency_pair (ha u) (hb u)).1.const_mul (D u)
  have hMass (u : X) : (∫ z, f (u,z)) = D u := by
    change (∫ z, D u * twoBandFrequencyPair (A u) (B u) z) = D u
    rw [integral_const_mul,(twoBand_positive_frequency_pair (ha u) (hb u)).2,mul_one]
  have hI : Integrable f := by
    apply (integrable_prod_iff hm).mpr
    simp_rw [Real.norm_of_nonneg (hN _), hMass]
    exact ⟨ae_of_all _ hS,hi⟩
  refine ⟨hI, (integral_prod _ hI).trans ?_⟩
  exact integral_congr_ae (ae_of_all _ hMass)

/-- Absolute integration of the positive spectral density in the original
eight momentum variables, with the two frequencies still independent. -/
theorem twoBand_positive_coulomb_energy {m σ a : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (ha : 0 < a) (g q : ℝ) :
    Integrable (twoBandPositiveCoulombIntegrand m g σ q a) ∧
    (∫ x, twoBandPositiveCoulombIntegrand m g σ q a x) =
      (1/(2*(2*Real.pi)^6)) * ∫ u, twoBandCoulombSpatialDensity m g σ q a u := by
  let C : ℝ := 1/(2*(2*Real.pi)^6)
  let D := twoBandCoulombSpatialDensity m g σ q a
  let A := fun u : Spatial × Spatial => twoBandGap m (twoBandSpatialHop g σ u.2)
  let B := fun u : Spatial × Spatial => twoBandGap m (twoBandSpatialHop g σ (u.2+u.1))
  have hC : 0 < C := by unfold C; positivity
  have hD : Integrable D := twoBand_positive_coulomb_spatial hm hσ ha g q
  have H := positive_pair_integral (fun u => C*D u) A B (hD.const_mul C)
    (fun u => mul_nonneg hC.le (twoBand_coulomb_spatial_density_nonneg hm g σ q a u))
    (fun u => twoBand_gap_pos hm _) (fun u => twoBand_gap_pos hm _)
    (by unfold A; fun_prop) (by unfold B; fun_prop)
  exact ⟨H.1,H.2.trans (integral_const_mul C D)⟩

theorem twoBand_positive_coulomb_energy_pos {m σ a g q : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (ha : 0 < a) (hg : g ≠ 0) (hq : q ≠ 0) :
    0 < ∫ x, twoBandPositiveCoulombIntegrand m g σ q a x := by
  rw [(twoBand_positive_coulomb_energy hm hσ ha g q).2]
  exact mul_pos (by positivity) (twoBand_positive_coulomb_spatial_mass hm hσ ha hg hq)

end UV.SectorPlane
