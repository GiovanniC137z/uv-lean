import UV.ContinueOrderedTorusShell
import UV.ContinueTwoBandResolvent
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Photon propagators on the fixed spatial torus. Spatial harmonic modes
are absent, including when a bridge transfer is fixed by endpoint momenta. -/

noncomputable section
open Real MeasureTheory Set Filter
open scoped ENNReal Topology
namespace UV.SectorPlane

def orderedTorusTransverse (δ : Fin 3 → ℝ) (r : ℝ) (k : OrderedHopWinding) (ν : ℝ) : ℝ :=
  if k = 0 then 0 else exp (-(2*r*‖orderedTorusMomentum δ k‖)) /
    (ν^2+‖orderedTorusMomentum δ k‖^2)

def orderedTorusCoulomb (δ : Fin 3 → ℝ) (r : ℝ) (k : OrderedHopWinding) (ν : ℝ) : ℝ :=
  if k = 0 then 0 else exp (-(2*r*‖orderedTorusMomentum δ k‖)) /
    (‖orderedTorusMomentum δ k‖^2*(1+|ν|)^2)

private theorem coulomb_time_mass : (∫ ν : ℝ, ((1+|ν|)^2)⁻¹) = 2 := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) 1).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft (1:ℝ)).measurableEmbedding (fun x : ℝ => x^(-2:ℝ)) (Ioi 1)
  have hS : (fun x : ℝ => 1+x) ⁻¹' Ioi 1 = Ioi 0 := by ext x; simp
  rw [hS] at h
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) zero_lt_one] at h
  norm_num at h
  rw [integral_comp_abs (f := fun x : ℝ => ((1+x)^2)⁻¹)]
  simp only [zpow_ofNat] at h
  linarith

/-- The normalization gives `π/|p|` for the transverse frequency integral
and `2` for the integrable scalar endpoint time factor. -/
theorem ordered_torus_photon_time {δ : Fin 3 → ℝ} {d : ℝ} (hd : 0 < d) (hδ : ∀ i, d ≤ δ i)
    (r : ℝ) (k : OrderedHopWinding) :
    (∫⁻ ν : ℝ, ENNReal.ofReal (orderedTorusTransverse δ r k ν)) =
      ENNReal.ofReal π * (if k = 0 then 0 else
        ENNReal.ofReal (exp (-(2*r*‖orderedTorusMomentum δ k‖)) / ‖orderedTorusMomentum δ k‖)) ∧
    (∫⁻ ν : ℝ, ENNReal.ofReal (orderedTorusCoulomb δ r k ν)) =
      2 * (if k = 0 then 0 else
        ENNReal.ofReal (exp (-(2*r*‖orderedTorusMomentum δ k‖)) / ‖orderedTorusMomentum δ k‖^2)) := by
  by_cases hk : k = 0
  · simp [hk,orderedTorusTransverse,orderedTorusCoulomb]
  let a := ‖orderedTorusMomentum δ k‖
  have ha : 0 < a := hd.trans_le (ordered_torus_gap hd hδ hk)
  let G := exp (-(2*r*a))
  have hG : 0 ≤ G := (exp_pos _).le
  simp only [if_neg hk]
  constructor
  · have hI := twoBand_frequency_integral ha
    have he (ν : ℝ) : orderedTorusTransverse δ r k ν = G*(twoBandFrequencyBound a ν)^2 := by
      rw [orderedTorusTransverse,if_neg hk,twoBand_frequency_bound_sq]; rfl
    simp_rw [he]
    rw [← ofReal_integral_eq_lintegral_ofReal (hI.1.const_mul G)
      (Eventually.of_forall fun x => mul_nonneg hG (sq_nonneg _)),integral_const_mul,hI.2,
      ← ENNReal.ofReal_mul pi_pos.le]
    congr 1; ring
  · have hI : Integrable (fun ν : ℝ => ((1+|ν|)^2)⁻¹) := Integrable.of_integral_ne_zero
      (coulomb_time_mass.trans_ne (by norm_num))
    have he (ν : ℝ) : orderedTorusCoulomb δ r k ν = (G/a^2)*((1+|ν|)^2)⁻¹ := by
      rw [orderedTorusCoulomb,if_neg hk]; simp [G,a,div_eq_mul_inv,mul_assoc,mul_comm]
    simp_rw [he]
    rw [← ofReal_integral_eq_lintegral_ofReal (hI.const_mul (G/a^2))
      (Eventually.of_forall fun x => mul_nonneg (div_nonneg hG (sq_nonneg _)) (inv_nonneg.mpr (sq_nonneg _))),
      integral_const_mul,coulomb_time_mass,mul_comm,ENNReal.ofReal_mul (by norm_num)]
    norm_num [G,a]

/-- Every bridge value is controlled uniformly, even without a soft current
subtraction. The excluded mode has exactly zero contribution. -/
theorem ordered_torus_bridge_bound {δ : Fin 3 → ℝ} {d r : ℝ} (hd : 0 < d) (hδ : ∀ i, d ≤ δ i)
    (hr : 0 ≤ r) (k : OrderedHopWinding) (ν : ℝ) :
    orderedTorusTransverse δ r k ν ≤ (d^2)⁻¹ ∧ orderedTorusCoulomb δ r k ν ≤ (d^2)⁻¹ := by
  by_cases hk : k = 0
  · simp [hk,orderedTorusTransverse,orderedTorusCoulomb,sq_nonneg]
  have hgap := ordered_torus_gap hd hδ hk
  have hg := pow_le_pow_left₀ hd.le hgap 2
  have hG : exp (-(2*r*‖orderedTorusMomentum δ k‖)) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have h₁ : 1 ≤ (1+|ν|)^2 := by nlinarith [abs_nonneg ν,sq_nonneg |ν|]
  rw [orderedTorusTransverse,orderedTorusCoulomb,if_neg hk,if_neg hk,←one_div]
  constructor
  · apply div_le_div₀ zero_le_one hG (by positivity); linarith [sq_nonneg ν]
  · exact div_le_div₀ zero_le_one hG (by positivity) (hg.trans (le_mul_of_one_le_right (sq_nonneg _) h₁))

/-- Small-depth costs for a full chord of either kind, with a rectangular
spatial lattice and the entire real frequency axis. -/
theorem ordered_torus_integrated_chord_costs {δ : Fin 3 → ℝ} {d : ℝ} (hd : 0 < d)
    (hδ : ∀ i, d ≤ δ i) :
    ∃ CT CC : ℝ≥0∞, CT < ⊤ ∧ CC < ⊤ ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∑' k, ∫⁻ ν : ℝ, ENNReal.ofReal (orderedTorusTransverse δ r k ν)) ≤ CT * ENNReal.ofReal ((r^2)⁻¹) ∧
      (∑' k, ∫⁻ ν : ℝ, ENNReal.ofReal (orderedTorusCoulomb δ r k ν)) ≤ CC * ENNReal.ofReal r⁻¹ := by
  let CT := π*(26/d)*exp (2*d)/(2*d)^2
  let CC := 2*(26/d^2)/(2*d)
  refine ⟨ENNReal.ofReal CT, ENNReal.ofReal CC,ENNReal.ofReal_lt_top,ENNReal.ofReal_lt_top,?_⟩
  intro r hr hr₁
  have h := ordered_torus_spatial_chord_budgets hd hδ hr
  simp_rw [(ordered_torus_photon_time hd hδ r _).1, (ordered_torus_photon_time hd hδ r _).2,
    ENNReal.tsum_mul_left]
  constructor
  · apply (mul_le_mul_left' h.1 _).trans
    rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul pi_pos.le,
      ← ENNReal.ofReal_mul (show 0 ≤ CT by dsimp [CT]; positivity)]
    apply ENNReal.ofReal_le_ofReal
    have he : exp (2*r*d) ≤ exp (2*d) := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hr₁ hd.le])
    calc
      _ ≤ π * (26/d * (exp (2*d) / (2*r*d)^2)) := by gcongr
      _ = _ := by dsimp [CT]; field_simp
  · apply (mul_le_mul_left' h.2 _).trans
    rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (show 0 ≤ CC by dsimp [CC]; positivity)]
    apply le_of_eq; congr 1; dsimp [CC]; field_simp

end UV.SectorPlane
