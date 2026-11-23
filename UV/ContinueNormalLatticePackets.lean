import UV.ContinueNormalLatticeLoops
import Mathlib.Analysis.Distribution.SchwartzSpace

/-! Uniform sampling of smooth spinor endpoints on a reciprocal
four-lattice. The translated packet and all routed momenta may vary. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal SchwartzMap

namespace UV

def normalPacketWeight (k : OSFourSpace) : ℝ := ((1+‖k‖)^6)⁻¹

theorem normal_packet_weight_integrable : Integrable normalPacketWeight := by
  have hd : (Module.finrank ℝ OSFourSpace : ℝ) < 6 := by rw [finrank_euclideanSpace_fin]; norm_num
  apply (integrable_one_add_norm (μ := volume) hd).congr
  refine Eventually.of_forall fun x => ?_
  change (1+‖x‖)^(-(6:ℝ)) = ((1+‖x‖)^6)⁻¹
  rw [Real.rpow_neg (by positivity),Real.rpow_ofNat]

theorem normal_lattice_packet_weight_shifts (b : NormalReciprocalBasis) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : OSFourSpace, let g := fun k => normalPacketWeight (k+s)
      Integrable g (normalLatticeMeasure b) ∧ (∫ k, g k ∂normalLatticeMeasure b) ≤ B := by
  obtain ⟨R,hR⟩ := (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
  let R' := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  let C := (1+R')^6
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let A := normalCellFactor b C
  have hB : 0 ≤ ∫ k, normalPacketWeight k := integral_nonneg fun k => by dsimp [normalPacketWeight]; positivity
  refine ⟨A.toReal*(∫ k, normalPacketWeight k),mul_nonneg ENNReal.toReal_nonneg hB,fun s => ?_⟩
  let g := fun k => normalPacketWeight (k+s)
  have hg : Measurable g := by dsimp [g,normalPacketWeight]; fun_prop
  have hn (k) : 0 ≤ g k := by dsimp [g,normalPacketWeight]; positivity
  have hi := (measurePreserving_add_right volume s).integrable_comp_of_integrable normal_packet_weight_integrable
  have hc (k : NormalReciprocalLattice b) (x) (hx : x ∈ ZSpan.fundamentalDomain b) :
      g k ≤ C * g ((k:OSFourSpace)+x) := by
    have hnorm : 1+‖(k:OSFourSpace)+x+s‖ ≤ (1+R')*(1+‖(k:OSFourSpace)+s‖) := by
      rw [add_right_comm (k:OSFourSpace) x s]
      nlinarith [norm_add_le ((k:OSFourSpace)+s) x,(hR x hx).trans (le_max_left R 0),
        mul_nonneg hR' (norm_nonneg ((k:OSFourSpace)+s))]
    dsimp only [g,C,normalPacketWeight]
    rw [←div_eq_mul_inv,le_div_iff₀ (by positivity),inv_mul_eq_div,div_le_iff₀ (by positivity),←mul_pow]
    exact pow_le_pow_left₀ (by positivity) hnorm 6
  have h := normal_integral_from_cell_bound (normalLatticeMeasure b) volume hg hn hi A (normal_cell_factor_finite b C)
    (normal_lattice_cell_lintegral b C _ (ENNReal.measurable_ofReal.comp hg) (fun k x hx => by
      rw [←ENNReal.ofReal_mul hC]; exact ENNReal.ofReal_le_ofReal (hc k x hx)))
  exact ⟨h.1,h.2.trans_eq (congrArg (A.toReal*·) (integral_add_right_eq_self normalPacketWeight s))⟩

def normalSchwartzPacket (f : 𝓢(OSFourSpace,WilsonPacketSpinor)) : WilsonPacket :=
  ⟨f,f.continuous.measurable,f.memLp 2⟩

/-- An L² packet on the continuum alone need not control its point
samples. Schwartz decay gives a uniform square sum on all translates. -/
theorem normal_schwartz_lattice_shifts (b : NormalReciprocalBasis) (f : 𝓢(OSFourSpace,WilsonPacketSpinor)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : OSFourSpace, let g := fun k => ‖f (k+s)‖^2
      Integrable g (normalLatticeMeasure b) ∧ (∫ k, g k ∂normalLatticeMeasure b) ≤ B := by
  let K : ℝ := 2^3*(Finset.Iic (3,0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hk (x : OSFourSpace) : (1+‖x‖)^3*‖f x‖ ≤ K := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3,0)) (le_refl 3) (le_refl 0) f x
  have hk' (x : OSFourSpace) : ‖f x‖^2 ≤ K^2*normalPacketWeight x := by
    dsimp only [normalPacketWeight]
    rw [←div_eq_mul_inv,le_div_iff₀ (by positivity)]
    calc _ = ((1+‖x‖)^3*‖f x‖)^2 := by ring
         _ ≤ _ := pow_le_pow_left₀ (by positivity) (hk x) 2
  obtain ⟨B,hB,h⟩ := normal_lattice_packet_weight_shifts b
  refine ⟨K^2*B,mul_nonneg (sq_nonneg _) hB,fun s => ?_⟩
  have hmaj := (h s).1.const_mul (K^2)
  have hi := hmaj.mono' ((f.continuous.comp (continuous_id.add (continuous_const (y := s)))).norm.pow 2).measurable.aestronglyMeasurable
    (Eventually.of_forall fun k => by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hk' (k+s))
  refine ⟨hi,(integral_mono hi hmaj (fun k => hk' (k+s))).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (h s).2 (sq_nonneg _)

end UV
